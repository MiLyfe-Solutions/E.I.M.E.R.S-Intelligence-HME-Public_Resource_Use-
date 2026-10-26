import V185TrunkScan23Chunk0495

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2933530 : List Nat := [3, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4]
def baseStart_2933530 : Nat := 118140960795 + 2933530 * 2 ^ 59
def prefixEnd_2933530 : Nat := 4983230072969 + 3 ^ 40 * 2933530 * 2
def baseEnd_2933530 : Nat := 1506310904384012784083947

theorem tailTrace_2933530 : CollatzResearch.WordTrace tailWord_2933530 prefixEnd_2933530 1506310904384012784083947 := by
  unfold tailWord_2933530
  simp only [CollatzResearch.WordTrace]
  refine ⟨26748657265582322970475511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71329752708219527921268029 26748657265582322970475511)
  ·
    refine ⟨40122985898373484455713267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26748657265582322970475511 40122985898373484455713267)
    ·
      refine ⟨60184478847560226683569901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40122985898373484455713267 60184478847560226683569901)
      ·
        refine ⟨22569179567835085006338713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60184478847560226683569901 22569179567835085006338713)
        ·
          refine ⟨16926884675876313754754035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22569179567835085006338713 16926884675876313754754035)
          ·
            refine ⟨25390327013814470632131053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16926884675876313754754035 25390327013814470632131053)
            ·
              refine ⟨9521372630180426487049145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25390327013814470632131053 9521372630180426487049145)
              ·
                refine ⟨7141029472635319865286859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9521372630180426487049145 7141029472635319865286859)
                ·
                  refine ⟨10711544208952979797930289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7141029472635319865286859 10711544208952979797930289)
                  ·
                    refine ⟨8033658156714734848447717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10711544208952979797930289 8033658156714734848447717)
                    ·
                      refine ⟨1506310904384012784083947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8033658156714734848447717 1506310904384012784083947)
                      ·
                        rfl

theorem cell23_2933530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_2933530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933530 prefixEnd_2933530 := by exact prefixLift 2933530
  have htrace : WordTrace (prefixWord ++ tailWord_2933530) baseStart_2933530 baseEnd_2933530 := by
    simpa [prefixWord, tailWord_2933530, baseEnd_2933530] using wordTrace_append hprefix tailTrace_2933530
  have hstable : (prefixWord ++ tailWord_2933530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933530).length < 2 ^ (prefixWord ++ tailWord_2933530).sum := by decide
  have hdescent : baseEnd_2933530 < baseStart_2933530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933540 : List Nat := [2, 3, 1, 3, 4, 10]
def baseStart_2933540 : Nat := 118140960795 + 2933540 * 2 ^ 59
def prefixEnd_2933540 : Nat := 4983230072969 + 3 ^ 40 * 2933540 * 2
def baseEnd_2933540 : Nat := 6198831436998180020407

theorem tailTrace_2933540 : CollatzResearch.WordTrace tailWord_2933540 prefixEnd_2933540 6198831436998180020407 := by
  unfold tailWord_2933540
  simp only [CollatzResearch.WordTrace]
  refine ⟨53497496896146531794883037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71329995861528709059844049 53497496896146531794883037)
  ·
    refine ⟨20061561336054949423081139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53497496896146531794883037 20061561336054949423081139)
    ·
      refine ⟨30092342004082424134621709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20061561336054949423081139 30092342004082424134621709)
      ·
        refine ⟨11284628251530909050483141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30092342004082424134621709 11284628251530909050483141)
        ·
          refine ⟨2115867797162045446965589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11284628251530909050483141 2115867797162045446965589)
          ·
            refine ⟨6198831436998180020407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2115867797162045446965589 6198831436998180020407)
            ·
              rfl

theorem cell23_2933540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 10].length) (baseStart_2933540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933540 prefixEnd_2933540 := by exact prefixLift 2933540
  have htrace : WordTrace (prefixWord ++ tailWord_2933540) baseStart_2933540 baseEnd_2933540 := by
    simpa [prefixWord, tailWord_2933540, baseEnd_2933540] using wordTrace_append hprefix tailTrace_2933540
  have hstable : (prefixWord ++ tailWord_2933540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933540).length < 2 ^ (prefixWord ++ tailWord_2933540).sum := by decide
  have hdescent : baseEnd_2933540 < baseStart_2933540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933553 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 1, 9]
def baseStart_2933553 : Nat := 118140960795 + 2933553 * 2 ^ 59
def prefixEnd_2933553 : Nat := 4983230072969 + 3 ^ 40 * 2933553 * 2
def baseEnd_2933553 : Nat := 502107571479688731365447

theorem tailTrace_2933553 : CollatzResearch.WordTrace tailWord_2933553 prefixEnd_2933553 502107571479688731365447 := by
  unfold tailWord_2933553
  simp only [CollatzResearch.WordTrace]
  refine ⟨106995467941245966809989313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71330311960830644539992875 106995467941245966809989313)
  ·
    refine ⟨80246600955934475107491985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106995467941245966809989313 80246600955934475107491985)
    ·
      refine ⟨60184950716950856330618989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80246600955934475107491985 60184950716950856330618989)
      ·
        refine ⟨22569356518856571123982121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60184950716950856330618989 22569356518856571123982121)
        ·
          refine ⟨16927017389142428342986591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22569356518856571123982121 16927017389142428342986591)
          ·
            refine ⟨25390526083713642514479887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16927017389142428342986591 25390526083713642514479887)
            ·
              refine ⟨38085789125570463771719831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25390526083713642514479887 38085789125570463771719831)
              ·
                refine ⟨57128683688355695657579747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38085789125570463771719831 57128683688355695657579747)
                ·
                  refine ⟨85693025532533543486369621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57128683688355695657579747 85693025532533543486369621)
                  ·
                    refine ⟨502107571479688731365447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 85693025532533543486369621 502107571479688731365447)
                    ·
                      rfl

theorem cell23_2933553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_2933553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933553 prefixEnd_2933553 := by exact prefixLift 2933553
  have htrace : WordTrace (prefixWord ++ tailWord_2933553) baseStart_2933553 baseEnd_2933553 := by
    simpa [prefixWord, tailWord_2933553, baseEnd_2933553] using wordTrace_append hprefix tailTrace_2933553
  have hstable : (prefixWord ++ tailWord_2933553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933553).length < 2 ^ (prefixWord ++ tailWord_2933553).sum := by decide
  have hdescent : baseEnd_2933553 < baseStart_2933553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933567 : List Nat := [1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 3]
def baseStart_2933567 : Nat := 118140960795 + 2933567 * 2 ^ 59
def prefixEnd_2933567 : Nat := 4983230072969 + 3 ^ 40 * 2933567 * 2
def baseEnd_2933567 : Nat := 1506329903168229139321277

theorem tailTrace_2933567 : CollatzResearch.WordTrace tailWord_2933567 prefixEnd_2933567 1506329903168229139321277 := by
  unfold tailWord_2933567
  simp only [CollatzResearch.WordTrace]
  refine ⟨106995978563195247200998955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71330652375463498133999303 106995978563195247200998955)
  ·
    refine ⟨160493967844792870801498433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106995978563195247200998955 160493967844792870801498433)
    ·
      refine ⟨120370475883594653101123825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160493967844792870801498433 120370475883594653101123825)
      ·
        refine ⟨90277856912695989825842869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120370475883594653101123825 90277856912695989825842869)
        ·
          refine ⟨8463549085565249046172769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90277856912695989825842869 8463549085565249046172769)
          ·
            refine ⟨6347661814173936784629577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8463549085565249046172769 6347661814173936784629577)
            ·
              refine ⟨4760746360630452588472183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6347661814173936784629577 4760746360630452588472183)
              ·
                refine ⟨7141119540945678882708275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4760746360630452588472183 7141119540945678882708275)
                ·
                  refine ⟨10711679311418518324062413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7141119540945678882708275 10711679311418518324062413)
                  ·
                    refine ⟨4016879741781944371523405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10711679311418518324062413 4016879741781944371523405)
                    ·
                      refine ⟨1506329903168229139321277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4016879741781944371523405 1506329903168229139321277)
                      ·
                        rfl

theorem cell23_2933567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 3].length) (baseStart_2933567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933567 prefixEnd_2933567 := by exact prefixLift 2933567
  have htrace : WordTrace (prefixWord ++ tailWord_2933567) baseStart_2933567 baseEnd_2933567 := by
    simpa [prefixWord, tailWord_2933567, baseEnd_2933567] using wordTrace_append hprefix tailTrace_2933567
  have hstable : (prefixWord ++ tailWord_2933567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933567).length < 2 ^ (prefixWord ++ tailWord_2933567).sum := by decide
  have hdescent : baseEnd_2933567 < baseStart_2933567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933577 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 3, 3, 2]
def baseStart_2933577 : Nat := 118140960795 + 2933577 * 2 ^ 59
def prefixEnd_2933577 : Nat := 4983230072969 + 3 ^ 40 * 2933577 * 2
def baseEnd_2933577 : Nat := 1506335037974774100196231

theorem tailTrace_2933577 : CollatzResearch.WordTrace tailWord_2933577 prefixEnd_2933577 1506335037974774100196231 := by
  unfold tailWord_2933577
  simp only [CollatzResearch.WordTrace]
  refine ⟨106996343293159018908862985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71330895528772679272575323 106996343293159018908862985)
  ·
    refine ⟨80247257469869264181647239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106996343293159018908862985 80247257469869264181647239)
    ·
      refine ⟨120370886204803896272470859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80247257469869264181647239 120370886204803896272470859)
      ·
        refine ⟨180556329307205844408706289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120370886204803896272470859 180556329307205844408706289)
        ·
          refine ⟨135417246980404383306529717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180556329307205844408706289 135417246980404383306529717)
          ·
            refine ⟨12695366904412910934987161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135417246980404383306529717 12695366904412910934987161)
            ·
              refine ⟨9521525178309683201240371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12695366904412910934987161 9521525178309683201240371)
              ·
                refine ⟨14282287767464524801860557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9521525178309683201240371 14282287767464524801860557)
                ·
                  refine ⟨5355857912799196800697709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14282287767464524801860557 5355857912799196800697709)
                  ·
                    refine ⟨2008446717299698800261641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5355857912799196800697709 2008446717299698800261641)
                    ·
                      refine ⟨1506335037974774100196231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2008446717299698800261641 1506335037974774100196231)
                      ·
                        rfl

theorem cell23_2933577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 3, 3, 2].length) (baseStart_2933577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933577 prefixEnd_2933577 := by exact prefixLift 2933577
  have htrace : WordTrace (prefixWord ++ tailWord_2933577) baseStart_2933577 baseEnd_2933577 := by
    simpa [prefixWord, tailWord_2933577, baseEnd_2933577] using wordTrace_append hprefix tailTrace_2933577
  have hstable : (prefixWord ++ tailWord_2933577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933577).length < 2 ^ (prefixWord ++ tailWord_2933577).sum := by decide
  have hdescent : baseEnd_2933577 < baseStart_2933577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933588 : List Nat := [2, 4, 1, 1, 5, 1, 2, 1, 1, 2, 3]
def baseStart_2933588 : Nat := 118140960795 + 2933588 * 2 ^ 59
def prefixEnd_2933588 : Nat := 4983230072969 + 3 ^ 40 * 2933588 * 2
def baseEnd_2933588 : Nat := 1506340686261973557158681

theorem tailTrace_2933588 : CollatzResearch.WordTrace tailWord_2933588 prefixEnd_2933588 1506340686261973557158681 := by
  unfold tailWord_2933588
  simp only [CollatzResearch.WordTrace]
  refine ⟨53498372248059583893756709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71331162997412778525008945 53498372248059583893756709)
  ·
    refine ⟨10030944796511171980079383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53498372248059583893756709 10030944796511171980079383)
    ·
      refine ⟨15046417194766757970119075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10030944796511171980079383 15046417194766757970119075)
      ·
        refine ⟨22569625792150136955178613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15046417194766757970119075 22569625792150136955178613)
        ·
          refine ⟨2115902418014075339547995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22569625792150136955178613 2115902418014075339547995)
          ·
            refine ⟨3173853627021113009321993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2115902418014075339547995 3173853627021113009321993)
            ·
              refine ⟨2380390220265834756991495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3173853627021113009321993 2380390220265834756991495)
              ·
                refine ⟨3570585330398752135487243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2380390220265834756991495 3570585330398752135487243)
                ·
                  refine ⟨5355877995598128203230865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3570585330398752135487243 5355877995598128203230865)
                  ·
                    refine ⟨4016908496698596152423149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5355877995598128203230865 4016908496698596152423149)
                    ·
                      refine ⟨1506340686261973557158681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4016908496698596152423149 1506340686261973557158681)
                      ·
                        rfl

theorem cell23_2933588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_2933588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933588 prefixEnd_2933588 := by exact prefixLift 2933588
  have htrace : WordTrace (prefixWord ++ tailWord_2933588) baseStart_2933588 baseEnd_2933588 := by
    simpa [prefixWord, tailWord_2933588, baseEnd_2933588] using wordTrace_append hprefix tailTrace_2933588
  have hstable : (prefixWord ++ tailWord_2933588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933588).length < 2 ^ (prefixWord ++ tailWord_2933588).sum := by decide
  have hdescent : baseEnd_2933588 < baseStart_2933588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933594 : List Nat := [3, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2]
def baseStart_2933594 : Nat := 118140960795 + 2933594 * 2 ^ 59
def prefixEnd_2933594 : Nat := 4983230072969 + 3 ^ 40 * 2933594 * 2
def baseEnd_2933594 : Nat := 1506343767145900533683653

theorem tailTrace_2933594 : CollatzResearch.WordTrace tailWord_2933594 prefixEnd_2933594 1506343767145900533683653 := by
  unfold tailWord_2933594
  simp only [CollatzResearch.WordTrace]
  refine ⟨26749240833524357703057959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71331308889398287208154557 26749240833524357703057959)
  ·
    refine ⟨40123861250286536554586939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26749240833524357703057959 40123861250286536554586939)
    ·
      refine ⟨60185791875429804831880409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40123861250286536554586939 60185791875429804831880409)
      ·
        refine ⟨45139343906572353623910307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60185791875429804831880409 45139343906572353623910307)
        ·
          refine ⟨67709015859858530435865461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45139343906572353623910307 67709015859858530435865461)
          ·
            refine ⟨6347720236861737228362387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67709015859858530435865461 6347720236861737228362387)
            ·
              refine ⟨9521580355292605842543581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6347720236861737228362387 9521580355292605842543581)
              ·
                refine ⟨3570592633234727190953843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9521580355292605842543581 3570592633234727190953843)
                ·
                  refine ⟨5355888949852090786430765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3570592633234727190953843 5355888949852090786430765)
                  ·
                    refine ⟨2008458356194534044911537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5355888949852090786430765 2008458356194534044911537)
                    ·
                      refine ⟨1506343767145900533683653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2008458356194534044911537 1506343767145900533683653)
                      ·
                        rfl

theorem cell23_2933594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_2933594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933594 prefixEnd_2933594 := by exact prefixLift 2933594
  have htrace : WordTrace (prefixWord ++ tailWord_2933594) baseStart_2933594 baseEnd_2933594 := by
    simpa [prefixWord, tailWord_2933594, baseEnd_2933594] using wordTrace_append hprefix tailTrace_2933594
  have hstable : (prefixWord ++ tailWord_2933594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933594).length < 2 ^ (prefixWord ++ tailWord_2933594).sum := by decide
  have hdescent : baseEnd_2933594 < baseStart_2933594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933623 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 9]
def baseStart_2933623 : Nat := 118140960795 + 2933623 * 2 ^ 59
def prefixEnd_2933623 : Nat := 4983230072969 + 3 ^ 40 * 2933623 * 2
def baseEnd_2933623 : Nat := 1506358658084880920221019

theorem tailTrace_2933623 : CollatzResearch.WordTrace tailWord_2933623 prefixEnd_2933623 1506358658084880920221019 := by
  unfold tailWord_2933623
  simp only [CollatzResearch.WordTrace]
  refine ⟨106998021050992368765037523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71332014033994912510025015 106998021050992368765037523)
  ·
    refine ⟨160497031576488553147556285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106998021050992368765037523 160497031576488553147556285)
    ·
      refine ⟨60186386841183207430333607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160497031576488553147556285 60186386841183207430333607)
      ·
        refine ⟨90279580261774811145500411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60186386841183207430333607 90279580261774811145500411)
        ·
          refine ⟨135419370392662216718250617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90279580261774811145500411 135419370392662216718250617)
          ·
            refine ⟨101564527794496662538687963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135419370392662216718250617 101564527794496662538687963)
            ·
              refine ⟨152346791691744993808031945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101564527794496662538687963 152346791691744993808031945)
              ·
                refine ⟨114260093768808745356023959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152346791691744993808031945 114260093768808745356023959)
                ·
                  refine ⟨171390140653213118034035939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114260093768808745356023959 171390140653213118034035939)
                  ·
                    refine ⟨257085210979819677051053909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 171390140653213118034035939 257085210979819677051053909)
                    ·
                      refine ⟨1506358658084880920221019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 257085210979819677051053909 1506358658084880920221019)
                      ·
                        rfl

theorem cell23_2933623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 9].length) (baseStart_2933623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933623 prefixEnd_2933623 := by exact prefixLift 2933623
  have htrace : WordTrace (prefixWord ++ tailWord_2933623) baseStart_2933623 baseEnd_2933623 := by
    simpa [prefixWord, tailWord_2933623, baseEnd_2933623] using wordTrace_append hprefix tailTrace_2933623
  have hstable : (prefixWord ++ tailWord_2933623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933623).length < 2 ^ (prefixWord ++ tailWord_2933623).sum := by decide
  have hdescent : baseEnd_2933623 < baseStart_2933623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933714 : List Nat := [3, 2, 2, 3, 1, 1, 2, 2, 2, 1, 4]
def baseStart_2933714 : Nat := 118140960795 + 2933714 * 2 ^ 59
def prefixEnd_2933714 : Nat := 4983230072969 + 3 ^ 40 * 2933714 * 2
def baseEnd_2933714 : Nat := 1506405384824440064183101

theorem tailTrace_2933714 : CollatzResearch.WordTrace tailWord_2933714 prefixEnd_2933714 1506405384824440064183101 := by
  unfold tailWord_2933714
  simp only [CollatzResearch.WordTrace]
  refine ⟨26750335023415672826650049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71334226729108460871066797 26750335023415672826650049)
  ·
    refine ⟨20062751267561754619987537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26750335023415672826650049 20062751267561754619987537)
    ·
      refine ⟨15047063450671315964990653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20062751267561754619987537 15047063450671315964990653)
      ·
        refine ⟨5642648794001743486871495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15047063450671315964990653 5642648794001743486871495)
        ·
          refine ⟨8463973191002615230307243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5642648794001743486871495 8463973191002615230307243)
          ·
            refine ⟨12695959786503922845460865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8463973191002615230307243 12695959786503922845460865)
            ·
              refine ⟨9521969839877942134095649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12695959786503922845460865 9521969839877942134095649)
              ·
                refine ⟨7141477379908456600571737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9521969839877942134095649 7141477379908456600571737)
                ·
                  refine ⟨5356108034931342450428803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7141477379908456600571737 5356108034931342450428803)
                  ·
                    refine ⟨8034162052397013675643205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5356108034931342450428803 8034162052397013675643205)
                    ·
                      refine ⟨1506405384824440064183101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8034162052397013675643205 1506405384824440064183101)
                      ·
                        rfl

theorem cell23_2933714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_2933714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933714 prefixEnd_2933714 := by exact prefixLift 2933714
  have htrace : WordTrace (prefixWord ++ tailWord_2933714) baseStart_2933714 baseEnd_2933714 := by
    simpa [prefixWord, tailWord_2933714, baseEnd_2933714] using wordTrace_append hprefix tailTrace_2933714
  have hstable : (prefixWord ++ tailWord_2933714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933714).length < 2 ^ (prefixWord ++ tailWord_2933714).sum := by decide
  have hdescent : baseEnd_2933714 < baseStart_2933714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933781 : List Nat := [1, 3, 2, 1, 4, 2, 2, 1, 3, 1, 3]
def baseStart_2933781 : Nat := 118140960795 + 2933781 * 2 ^ 59
def prefixEnd_2933781 : Nat := 4983230072969 + 3 ^ 40 * 2933781 * 2
def baseEnd_2933781 : Nat := 1506439788028291302045293

theorem tailTrace_2933781 : CollatzResearch.WordTrace tailWord_2933781 prefixEnd_2933781 1506439788028291302045293 := by
  unfold tailWord_2933781
  simp only [CollatzResearch.WordTrace]
  refine ⟨107003783784419961749289197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71335855856279974499526131 107003783784419961749289197)
  ·
    refine ⟨40126418919157485655983449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107003783784419961749289197 40126418919157485655983449)
    ·
      refine ⟨30094814189368114241987587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40126418919157485655983449 30094814189368114241987587)
      ·
        refine ⟨45142221284052171362981381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30094814189368114241987587 45142221284052171362981381)
        ·
          refine ⟨8464166490759782130559009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45142221284052171362981381 8464166490759782130559009)
          ·
            refine ⟨6348124868069836597919257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8464166490759782130559009 6348124868069836597919257)
            ·
              refine ⟨4761093651052377448439443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6348124868069836597919257 4761093651052377448439443)
              ·
                refine ⟨7141640476578566172659165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4761093651052377448439443 7141640476578566172659165)
                ·
                  refine ⟨2678115178716962314747187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7141640476578566172659165 2678115178716962314747187)
                  ·
                    refine ⟨4017172768075443472120781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2678115178716962314747187 4017172768075443472120781)
                    ·
                      refine ⟨1506439788028291302045293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4017172768075443472120781 1506439788028291302045293)
                      ·
                        rfl

theorem cell23_2933781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_2933781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933781 prefixEnd_2933781 := by exact prefixLift 2933781
  have htrace : WordTrace (prefixWord ++ tailWord_2933781) baseStart_2933781 baseEnd_2933781 := by
    simpa [prefixWord, tailWord_2933781, baseEnd_2933781] using wordTrace_append hprefix tailTrace_2933781
  have hstable : (prefixWord ++ tailWord_2933781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933781).length < 2 ^ (prefixWord ++ tailWord_2933781).sum := by decide
  have hdescent : baseEnd_2933781 < baseStart_2933781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933804 : List Nat := [2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 4]
def baseStart_2933804 : Nat := 118140960795 + 2933804 * 2 ^ 59
def prefixEnd_2933804 : Nat := 4983230072969 + 3 ^ 40 * 2933804 * 2
def baseEnd_2933804 : Nat := 1506451598083344712057687

theorem tailTrace_2933804 : CollatzResearch.WordTrace tailWord_2933804 prefixEnd_2933804 1506451598083344712057687 := by
  unfold tailWord_2933804
  simp only [CollatzResearch.WordTrace]
  refine ⟨53502311331668318338688233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71336415108891091118250977 53502311331668318338688233)
  ·
    refine ⟨40126733498751238754016175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53502311331668318338688233 40126733498751238754016175)
    ·
      refine ⟨60190100248126858131024263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40126733498751238754016175 60190100248126858131024263)
      ·
        refine ⟨90285150372190287196536395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60190100248126858131024263 90285150372190287196536395)
        ·
          refine ⟨135427725558285430794804593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90285150372190287196536395 135427725558285430794804593)
          ·
            refine ⟨101570794168714073096103445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135427725558285430794804593 101570794168714073096103445)
            ·
              refine ⟨4761130976658472176379849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101570794168714073096103445 4761130976658472176379849)
              ·
                refine ⟨3570848232493854132284887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4761130976658472176379849 3570848232493854132284887)
                ·
                  refine ⟨5356272348740781198427331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3570848232493854132284887 5356272348740781198427331)
                  ·
                    refine ⟨8034408523111171797640997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5356272348740781198427331 8034408523111171797640997)
                    ·
                      refine ⟨1506451598083344712057687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8034408523111171797640997 1506451598083344712057687)
                      ·
                        rfl

theorem cell23_2933804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 4].length) (baseStart_2933804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933804 prefixEnd_2933804 := by exact prefixLift 2933804
  have htrace : WordTrace (prefixWord ++ tailWord_2933804) baseStart_2933804 baseEnd_2933804 := by
    simpa [prefixWord, tailWord_2933804, baseEnd_2933804] using wordTrace_append hprefix tailTrace_2933804
  have hstable : (prefixWord ++ tailWord_2933804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933804).length < 2 ^ (prefixWord ++ tailWord_2933804).sum := by decide
  have hdescent : baseEnd_2933804 < baseStart_2933804 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933807 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 3]
def baseStart_2933807 : Nat := 118140960795 + 2933807 * 2 ^ 59
def prefixEnd_2933807 : Nat := 4983230072969 + 3 ^ 40 * 2933807 * 2
def baseEnd_2933807 : Nat := 1506453138525308200320173

theorem tailTrace_2933807 : CollatzResearch.WordTrace tailWord_2933807 prefixEnd_2933807 1506453138525308200320173 := by
  unfold tailWord_2933807
  simp only [CollatzResearch.WordTrace]
  refine ⟨107004732082325768189735675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71336488054883845459823783 107004732082325768189735675)
  ·
    refine ⟨160507098123488652284603513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107004732082325768189735675 160507098123488652284603513)
    ·
      refine ⟨120380323592616489213452635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160507098123488652284603513 120380323592616489213452635)
      ·
        refine ⟨180570485388924733820178953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120380323592616489213452635 180570485388924733820178953)
        ·
          refine ⟨135427864041693550365134215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180570485388924733820178953 135427864041693550365134215)
          ·
            refine ⟨203141796062540325547701323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135427864041693550365134215 203141796062540325547701323)
            ·
              refine ⟨304712694093810488321551985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203141796062540325547701323 304712694093810488321551985)
              ·
                refine ⟨228534520570357866241163989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304712694093810488321551985 228534520570357866241163989)
                ·
                  refine ⟨5356277825867762490027281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 228534520570357866241163989 5356277825867762490027281)
                  ·
                    refine ⟨4017208369400821867520461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5356277825867762490027281 4017208369400821867520461)
                    ·
                      refine ⟨1506453138525308200320173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4017208369400821867520461 1506453138525308200320173)
                      ·
                        rfl

theorem cell23_2933807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 3].length) (baseStart_2933807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933807 prefixEnd_2933807 := by exact prefixLift 2933807
  have htrace : WordTrace (prefixWord ++ tailWord_2933807) baseStart_2933807 baseEnd_2933807 := by
    simpa [prefixWord, tailWord_2933807, baseEnd_2933807] using wordTrace_append hprefix tailTrace_2933807
  have hstable : (prefixWord ++ tailWord_2933807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933807).length < 2 ^ (prefixWord ++ tailWord_2933807).sum := by decide
  have hdescent : baseEnd_2933807 < baseStart_2933807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933824 : List Nat := [2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 3]
def baseStart_2933824 : Nat := 118140960795 + 2933824 * 2 ^ 59
def prefixEnd_2933824 : Nat := 4983230072969 + 3 ^ 40 * 2933824 * 2
def baseEnd_2933824 : Nat := 1506461867696434633807595

theorem tailTrace_2933824 : CollatzResearch.WordTrace tailWord_2933824 prefixEnd_2933824 1506461867696434633807595 := by
  unfold tailWord_2933824
  simp only [CollatzResearch.WordTrace]
  refine ⟨53502676061632090046552263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71336901415509453395403017 53502676061632090046552263)
  ·
    refine ⟨80254014092448135069828395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53502676061632090046552263 80254014092448135069828395)
    ·
      refine ⟨120381021138672202604742593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80254014092448135069828395 120381021138672202604742593)
      ·
        refine ⟨90285765854004151953556945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120381021138672202604742593 90285765854004151953556945)
        ·
          refine ⟨67714324390503113965167709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90285765854004151953556945 67714324390503113965167709)
          ·
            refine ⟨25392871646438667736937891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67714324390503113965167709 25392871646438667736937891)
            ·
              refine ⟨38089307469658001605406837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25392871646438667736937891 38089307469658001605406837)
              ·
                refine ⟨3570872575280437650506891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38089307469658001605406837 3570872575280437650506891)
                ·
                  refine ⟨5356308862920656475760337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3570872575280437650506891 5356308862920656475760337)
                  ·
                    refine ⟨4017231647190492356820253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5356308862920656475760337 4017231647190492356820253)
                    ·
                      refine ⟨1506461867696434633807595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4017231647190492356820253 1506461867696434633807595)
                      ·
                        rfl

theorem cell23_2933824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 3].length) (baseStart_2933824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933824 prefixEnd_2933824 := by exact prefixLift 2933824
  have htrace : WordTrace (prefixWord ++ tailWord_2933824) baseStart_2933824 baseEnd_2933824 := by
    simpa [prefixWord, tailWord_2933824, baseEnd_2933824] using wordTrace_append hprefix tailTrace_2933824
  have hstable : (prefixWord ++ tailWord_2933824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933824).length < 2 ^ (prefixWord ++ tailWord_2933824).sum := by decide
  have hdescent : baseEnd_2933824 < baseStart_2933824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933858 : List Nat := [3, 3, 2, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_2933858 : Nat := 118140960795 + 2933858 * 2 ^ 59
def prefixEnd_2933858 : Nat := 4983230072969 + 3 ^ 40 * 2933858 * 2
def baseEnd_2933858 : Nat := 1506479326038687500782439

theorem tailTrace_2933858 : CollatzResearch.WordTrace tailWord_2933858 prefixEnd_2933858 1506479326038687500782439 := by
  unfold tailWord_2933858
  simp only [CollatzResearch.WordTrace]
  refine ⟨26751648051285250974960557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71337728136760669266561485 26751648051285250974960557)
  ·
    refine ⟨10031868019231969115610209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26751648051285250974960557 10031868019231969115610209)
    ·
      refine ⟨7523901014423976836707657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10031868019231969115610209 7523901014423976836707657)
      ·
        refine ⟨5642925760817982627530743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7523901014423976836707657 5642925760817982627530743)
        ·
          refine ⟨8464388641226973941296115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5642925760817982627530743 8464388641226973941296115)
          ·
            refine ⟨12696582961840460911944173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8464388641226973941296115 12696582961840460911944173)
            ·
              refine ⟨4761218610690172841979065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12696582961840460911944173 4761218610690172841979065)
              ·
                refine ⟨3570913958017629631484299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4761218610690172841979065 3570913958017629631484299)
                ·
                  refine ⟨5356370937026444447226449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3570913958017629631484299 5356370937026444447226449)
                  ·
                    refine ⟨4017278202769833335419837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5356370937026444447226449 4017278202769833335419837)
                    ·
                      refine ⟨1506479326038687500782439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4017278202769833335419837 1506479326038687500782439)
                      ·
                        rfl

theorem cell23_2933858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_2933858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933858 prefixEnd_2933858 := by exact prefixLift 2933858
  have htrace : WordTrace (prefixWord ++ tailWord_2933858) baseStart_2933858 baseEnd_2933858 := by
    simpa [prefixWord, tailWord_2933858, baseEnd_2933858] using wordTrace_append hprefix tailTrace_2933858
  have hstable : (prefixWord ++ tailWord_2933858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933858).length < 2 ^ (prefixWord ++ tailWord_2933858).sum := by decide
  have hdescent : baseEnd_2933858 < baseStart_2933858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933907 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 4]
def baseStart_2933907 : Nat := 118140960795 + 2933907 * 2 ^ 59
def prefixEnd_2933907 : Nat := 4983230072969 + 3 ^ 40 * 2933907 * 2
def baseEnd_2933907 : Nat := 1506504486590757809069713

theorem tailTrace_2933907 : CollatzResearch.WordTrace tailWord_2933907 prefixEnd_2933907 1506504486590757809069713 := by
  unfold tailWord_2933907
  simp only [CollatzResearch.WordTrace]
  refine ⟨107008379381963485268375975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71338919587975656845583983 107008379381963485268375975)
  ·
    refine ⟨160512569072945227902563963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107008379381963485268375975 160512569072945227902563963)
    ·
      refine ⟨240768853609417841853845945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160512569072945227902563963 240768853609417841853845945)
      ·
        refine ⟨180576640207063381390384459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240768853609417841853845945 180576640207063381390384459)
        ·
          refine ⟨270864960310595072085576689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180576640207063381390384459 270864960310595072085576689)
          ·
            refine ⟨203148720232946304064182517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270864960310595072085576689 203148720232946304064182517)
            ·
              refine ⟨19045192521838716006017111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 203148720232946304064182517 19045192521838716006017111)
              ·
                refine ⟨28567788782758074009025667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19045192521838716006017111 28567788782758074009025667)
                ·
                  refine ⟨42851683174137111013538501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28567788782758074009025667 42851683174137111013538501)
                  ·
                    refine ⟨8034690595150708315038469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42851683174137111013538501 8034690595150708315038469)
                    ·
                      refine ⟨1506504486590757809069713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8034690595150708315038469 1506504486590757809069713)
                      ·
                        rfl

theorem cell23_2933907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 4].length) (baseStart_2933907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933907 prefixEnd_2933907 := by exact prefixLift 2933907
  have htrace : WordTrace (prefixWord ++ tailWord_2933907) baseStart_2933907 baseEnd_2933907 := by
    simpa [prefixWord, tailWord_2933907, baseEnd_2933907] using wordTrace_append hprefix tailTrace_2933907
  have hstable : (prefixWord ++ tailWord_2933907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933907).length < 2 ^ (prefixWord ++ tailWord_2933907).sum := by decide
  have hdescent : baseEnd_2933907 < baseStart_2933907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933911 : List Nat := [1, 1, 3, 3, 3, 1, 1, 3, 1, 4, 2]
def baseStart_2933911 : Nat := 118140960795 + 2933911 * 2 ^ 59
def prefixEnd_2933911 : Nat := 4983230072969 + 3 ^ 40 * 2933911 * 2
def baseEnd_2933911 : Nat := 1506506540513375793419695

theorem tailTrace_2933911 : CollatzResearch.WordTrace tailWord_2933911 prefixEnd_2933911 1506506540513375793419695 := by
  unfold tailWord_2933911
  simp only [CollatzResearch.WordTrace]
  refine ⟨107008525273948993951521587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71339016849299329301014391 107008525273948993951521587)
  ·
    refine ⟨160512787910923490927282381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107008525273948993951521587 160512787910923490927282381)
    ·
      refine ⟨60192295466596309097730893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160512787910923490927282381 60192295466596309097730893)
      ·
        refine ⟨22572110799973615911649085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60192295466596309097730893 22572110799973615911649085)
        ·
          refine ⟨8464541549990105966868407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22572110799973615911649085 8464541549990105966868407)
          ·
            refine ⟨12696812324985158950302611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8464541549990105966868407 12696812324985158950302611)
            ·
              refine ⟨19045218487477738425453917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12696812324985158950302611 19045218487477738425453917)
              ·
                refine ⟨7141956932804151909545219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19045218487477738425453917 7141956932804151909545219)
                ·
                  refine ⟨10712935399206227864317829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7141956932804151909545219 10712935399206227864317829)
                  ·
                    refine ⟨2008675387351167724559593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10712935399206227864317829 2008675387351167724559593)
                    ·
                      refine ⟨1506506540513375793419695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2008675387351167724559593 1506506540513375793419695)
                      ·
                        rfl

theorem cell23_2933911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_2933911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933911 prefixEnd_2933911 := by exact prefixLift 2933911
  have htrace : WordTrace (prefixWord ++ tailWord_2933911) baseStart_2933911 baseEnd_2933911 := by
    simpa [prefixWord, tailWord_2933911, baseEnd_2933911] using wordTrace_append hprefix tailTrace_2933911
  have hstable : (prefixWord ++ tailWord_2933911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933911).length < 2 ^ (prefixWord ++ tailWord_2933911).sum := by decide
  have hdescent : baseEnd_2933911 < baseStart_2933911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933945 : List Nat := [1, 2, 1, 4, 1, 5, 1, 2, 2, 2, 2]
def baseStart_2933945 : Nat := 118140960795 + 2933945 * 2 ^ 59
def prefixEnd_2933945 : Nat := 4983230072969 + 3 ^ 40 * 2933945 * 2
def baseEnd_2933945 : Nat := 1506523998855628660394539

theorem tailTrace_2933945 : CollatzResearch.WordTrace tailWord_2933945 prefixEnd_2933945 1506523998855628660394539 := by
  unfold tailWord_2933945
  simp only [CollatzResearch.WordTrace]
  refine ⟨107009765355825817758259289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71339843570550545172172859 107009765355825817758259289)
  ·
    refine ⟨80257324016869363318694467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107009765355825817758259289 80257324016869363318694467)
    ·
      refine ⟨120385986025304044978041701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80257324016869363318694467 120385986025304044978041701)
      ·
        refine ⟨22572372379744508433382819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120385986025304044978041701 22572372379744508433382819)
        ·
          refine ⟨33858558569616762650074229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22572372379744508433382819 33858558569616762650074229)
          ·
            refine ⟨3174239865901571498444459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33858558569616762650074229 3174239865901571498444459)
            ·
              refine ⟨4761359798852357247666689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3174239865901571498444459 4761359798852357247666689)
              ·
                refine ⟨3571019849139267935750017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4761359798852357247666689 3571019849139267935750017)
                ·
                  refine ⟨2678264886854450951812513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3571019849139267935750017 2678264886854450951812513)
                  ·
                    refine ⟨2008698665140838213859385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2678264886854450951812513 2008698665140838213859385)
                    ·
                      refine ⟨1506523998855628660394539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2008698665140838213859385 1506523998855628660394539)
                      ·
                        rfl

theorem cell23_2933945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_2933945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933945 prefixEnd_2933945 := by exact prefixLift 2933945
  have htrace : WordTrace (prefixWord ++ tailWord_2933945) baseStart_2933945 baseEnd_2933945 := by
    simpa [prefixWord, tailWord_2933945, baseEnd_2933945] using wordTrace_append hprefix tailTrace_2933945
  have hstable : (prefixWord ++ tailWord_2933945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933945).length < 2 ^ (prefixWord ++ tailWord_2933945).sum := by decide
  have hdescent : baseEnd_2933945 < baseStart_2933945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933957 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 1, 1, 7]
def baseStart_2933957 : Nat := 118140960795 + 2933957 * 2 ^ 59
def prefixEnd_2933957 : Nat := 4983230072969 + 3 ^ 40 * 2933957 * 2
def baseEnd_2933957 : Nat := 1506530160623482613444483

theorem tailTrace_2933957 : CollatzResearch.WordTrace tailWord_2933957 prefixEnd_2933957 1506530160623482613444483 := by
  unfold tailWord_2933957
  simp only [CollatzResearch.WordTrace]
  refine ⟨107010203031782343807696125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71340135354521562538464083 107010203031782343807696125)
  ·
    refine ⟨40128826136918378927886047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107010203031782343807696125 40128826136918378927886047)
    ·
      refine ⟨60193239205377568391829071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40128826136918378927886047 60193239205377568391829071)
      ·
        refine ⟨90289858808066352587743607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60193239205377568391829071 90289858808066352587743607)
        ·
          refine ⟨135434788212099528881615411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90289858808066352587743607 135434788212099528881615411)
          ·
            refine ⟨203152182318149293322423117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135434788212099528881615411 203152182318149293322423117)
            ·
              refine ⟨76182068369305984995908669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203152182318149293322423117 76182068369305984995908669)
              ·
                refine ⟨28568275638489744373465751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76182068369305984995908669 28568275638489744373465751)
                ·
                  refine ⟨42852413457734616560198627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28568275638489744373465751 42852413457734616560198627)
                  ·
                    refine ⟨64278620186601924840297941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42852413457734616560198627 64278620186601924840297941)
                    ·
                      refine ⟨1506530160623482613444483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64278620186601924840297941 1506530160623482613444483)
                      ·
                        rfl

theorem cell23_2933957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_2933957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933957 prefixEnd_2933957 := by exact prefixLift 2933957
  have htrace : WordTrace (prefixWord ++ tailWord_2933957) baseStart_2933957 baseEnd_2933957 := by
    simpa [prefixWord, tailWord_2933957, baseEnd_2933957] using wordTrace_append hprefix tailTrace_2933957
  have hstable : (prefixWord ++ tailWord_2933957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933957).length < 2 ^ (prefixWord ++ tailWord_2933957).sum := by decide
  have hdescent : baseEnd_2933957 < baseStart_2933957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933977 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 1, 10]
def baseStart_2933977 : Nat := 118140960795 + 2933977 * 2 ^ 59
def prefixEnd_2933977 : Nat := 4983230072969 + 3 ^ 40 * 2933977 * 2
def baseEnd_2933977 : Nat := 502180143412190845064797

theorem tailTrace_2933977 : CollatzResearch.WordTrace tailWord_2933977 prefixEnd_2933977 502180143412190845064797 := by
  unfold tailWord_2933977
  simp only [CollatzResearch.WordTrace]
  refine ⟨107010932491709887223424185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71340621661139924815616123 107010932491709887223424185)
  ·
    refine ⟨80258199368782415417568139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107010932491709887223424185 80258199368782415417568139)
    ·
      refine ⟨120387299053173623126352209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80258199368782415417568139 120387299053173623126352209)
      ·
        refine ⟨90290474289880217344764157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120387299053173623126352209 90290474289880217344764157)
        ·
          refine ⟨33858927858705081504286559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90290474289880217344764157 33858927858705081504286559)
          ·
            refine ⟨50788391788057622256429839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33858927858705081504286559 50788391788057622256429839)
            ·
              refine ⟨76182587682086433384644759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50788391788057622256429839 76182587682086433384644759)
              ·
                refine ⟨114273881523129650076967139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76182587682086433384644759 114273881523129650076967139)
                ·
                  refine ⟨171410822284694475115450709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114273881523129650076967139 171410822284694475115450709)
                  ·
                    refine ⟨502180143412190845064797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 171410822284694475115450709 502180143412190845064797)
                    ·
                      rfl

theorem cell23_2933977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 10].length) (baseStart_2933977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933977 prefixEnd_2933977 := by exact prefixLift 2933977
  have htrace : WordTrace (prefixWord ++ tailWord_2933977) baseStart_2933977 baseEnd_2933977 := by
    simpa [prefixWord, tailWord_2933977, baseEnd_2933977] using wordTrace_append hprefix tailTrace_2933977
  have hstable : (prefixWord ++ tailWord_2933977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933977).length < 2 ^ (prefixWord ++ tailWord_2933977).sum := by decide
  have hdescent : baseEnd_2933977 < baseStart_2933977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2933984 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 4]
def baseStart_2933984 : Nat := 118140960795 + 2933984 * 2 ^ 59
def prefixEnd_2933984 : Nat := 4983230072969 + 3 ^ 40 * 2933984 * 2
def baseEnd_2933984 : Nat := 1506544024601154007806859

theorem tailTrace_2933984 : CollatzResearch.WordTrace tailWord_2933984 prefixEnd_2933984 1506544024601154007806859 := by
  unfold tailWord_2933984
  simp only [CollatzResearch.WordTrace]
  refine ⟨53505593901342263709464503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71340791868456351612619337 53505593901342263709464503)
  ·
    refine ⟨80258390852013395564196755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53505593901342263709464503 80258390852013395564196755)
    ·
      refine ⟨120387586278020093346295133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80258390852013395564196755 120387586278020093346295133)
      ·
        refine ⟨45145344854257535004860675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120387586278020093346295133 45145344854257535004860675)
        ·
          refine ⟨67718017281386302507291013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45145344854257535004860675 67718017281386302507291013)
          ·
            refine ⟨12697128240259931720117065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67718017281386302507291013 12697128240259931720117065)
            ·
              refine ⟨9522846180194948790087799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12697128240259931720117065 9522846180194948790087799)
              ·
                refine ⟨14284269270292423185131699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9522846180194948790087799 14284269270292423185131699)
                ·
                  refine ⟨21426403905438634777697549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14284269270292423185131699 21426403905438634777697549)
                  ·
                    refine ⟨8034901464539488041636581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21426403905438634777697549 8034901464539488041636581)
                    ·
                      refine ⟨1506544024601154007806859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8034901464539488041636581 1506544024601154007806859)
                      ·
                        rfl

theorem cell23_2933984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_2933984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2933984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2933984 prefixEnd_2933984 := by exact prefixLift 2933984
  have htrace : WordTrace (prefixWord ++ tailWord_2933984) baseStart_2933984 baseEnd_2933984 := by
    simpa [prefixWord, tailWord_2933984, baseEnd_2933984] using wordTrace_append hprefix tailTrace_2933984
  have hstable : (prefixWord ++ tailWord_2933984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2933984).length < 2 ^ (prefixWord ++ tailWord_2933984).sum := by decide
  have hdescent : baseEnd_2933984 < baseStart_2933984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2933984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934058 : List Nat := [3, 1, 4, 2, 1, 2, 2, 2, 6]
def baseStart_2934058 : Nat := 118140960795 + 2934058 * 2 ^ 59
def prefixEnd_2934058 : Nat := 4983230072969 + 3 ^ 40 * 2934058 * 2
def baseEnd_2934058 : Nat := 167398002463287413142391

theorem tailTrace_2934058 : CollatzResearch.WordTrace tailWord_2934058 prefixEnd_2934058 167398002463287413142391 := by
  unfold tailWord_2934058
  simp only [CollatzResearch.WordTrace]
  refine ⟨26753471701104109514280707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71342591202944292038081885 26753471701104109514280707)
  ·
    refine ⟨40130207551656164271421061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26753471701104109514280707 40130207551656164271421061)
    ·
      refine ⟨7524413915935530800891449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40130207551656164271421061 7524413915935530800891449)
      ·
        refine ⟨5643310436951648100668587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7524413915935530800891449 5643310436951648100668587)
        ·
          refine ⟨8464965655427472151002881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5643310436951648100668587 8464965655427472151002881)
          ·
            refine ⟨6348724241570604113252161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8464965655427472151002881 6348724241570604113252161)
            ·
              refine ⟨4761543181177953084939121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6348724241570604113252161 4761543181177953084939121)
              ·
                refine ⟨3571157385883464813704341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4761543181177953084939121 3571157385883464813704341)
                ·
                  refine ⟨167398002463287413142391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3571157385883464813704341 167398002463287413142391)
                  ·
                    rfl

theorem cell23_2934058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 6].length) (baseStart_2934058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934058 prefixEnd_2934058 := by exact prefixLift 2934058
  have htrace : WordTrace (prefixWord ++ tailWord_2934058) baseStart_2934058 baseEnd_2934058 := by
    simpa [prefixWord, tailWord_2934058, baseEnd_2934058] using wordTrace_append hprefix tailTrace_2934058
  have hstable : (prefixWord ++ tailWord_2934058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934058).length < 2 ^ (prefixWord ++ tailWord_2934058).sum := by decide
  have hdescent : baseEnd_2934058 < baseStart_2934058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934078 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 1, 5, 2]
def baseStart_2934078 : Nat := 118140960795 + 2934078 * 2 ^ 59
def prefixEnd_2934078 : Nat := 4983230072969 + 3 ^ 40 * 2934078 * 2
def baseEnd_2934078 : Nat := 1506592291782676640031427

theorem tailTrace_2934078 : CollatzResearch.WordTrace tailWord_2934078 prefixEnd_2934078 1506592291782676640031427 := by
  unfold tailWord_2934078
  simp only [CollatzResearch.WordTrace]
  refine ⟨13376827033042997684106361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71343077509562654315233925 13376827033042997684106361)
  ·
    refine ⟨10032620274782248263079771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13376827033042997684106361 10032620274782248263079771)
    ·
      refine ⟨15048930412173372394619657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10032620274782248263079771 15048930412173372394619657)
      ·
        refine ⟨11286697809130029295964743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15048930412173372394619657 11286697809130029295964743)
        ·
          refine ⟨16930046713695043943947115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11286697809130029295964743 16930046713695043943947115)
          ·
            refine ⟨25395070070542565915920673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16930046713695043943947115 25395070070542565915920673)
            ·
              refine ⟨19046302552906924436940505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25395070070542565915920673 19046302552906924436940505)
              ·
                refine ⟨14284726914680193327705379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19046302552906924436940505 14284726914680193327705379)
                ·
                  refine ⟨21427090372020289991558069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14284726914680193327705379 21427090372020289991558069)
                  ·
                    refine ⟨2008789722376902186708569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21427090372020289991558069 2008789722376902186708569)
                    ·
                      refine ⟨1506592291782676640031427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2008789722376902186708569 1506592291782676640031427)
                      ·
                        rfl

theorem cell23_2934078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_2934078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934078 prefixEnd_2934078 := by exact prefixLift 2934078
  have htrace : WordTrace (prefixWord ++ tailWord_2934078) baseStart_2934078 baseEnd_2934078 := by
    simpa [prefixWord, tailWord_2934078, baseEnd_2934078] using wordTrace_append hprefix tailTrace_2934078
  have hstable : (prefixWord ++ tailWord_2934078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934078).length < 2 ^ (prefixWord ++ tailWord_2934078).sum := by decide
  have hdescent : baseEnd_2934078 < baseStart_2934078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934101 : List Nat := [1, 3, 2, 2, 3, 1, 2, 2, 1, 6]
def baseStart_2934101 : Nat := 118140960795 + 2934101 * 2 ^ 59
def prefixEnd_2934101 : Nat := 4983230072969 + 3 ^ 40 * 2934101 * 2
def baseEnd_2934101 : Nat := 502201367279243350014607

theorem tailTrace_2934101 : CollatzResearch.WordTrace tailWord_2934101 prefixEnd_2934101 502201367279243350014607 := by
  unfold tailWord_2934101
  simp only [CollatzResearch.WordTrace]
  refine ⟨107015455143260656400938157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71343636762173770933958771 107015455143260656400938157)
  ·
    refine ⟨40130795678722746150351809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107015455143260656400938157 40130795678722746150351809)
    ·
      refine ⟨30098096759042059612763857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40130795678722746150351809 30098096759042059612763857)
      ·
        refine ⟨22573572569281544709572893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30098096759042059612763857 22573572569281544709572893)
        ·
          refine ⟨8465089713480579266089835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22573572569281544709572893 8465089713480579266089835)
          ·
            refine ⟨12697634570220868899134753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8465089713480579266089835 12697634570220868899134753)
            ·
              refine ⟨9523225927665651674351065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12697634570220868899134753 9523225927665651674351065)
              ·
                refine ⟨7142419445749238755763299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9523225927665651674351065 7142419445749238755763299)
                ·
                  refine ⟨10713629168623858133644949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7142419445749238755763299 10713629168623858133644949)
                  ·
                    refine ⟨502201367279243350014607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10713629168623858133644949 502201367279243350014607)
                    ·
                      rfl

theorem cell23_2934101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_2934101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934101 prefixEnd_2934101 := by exact prefixLift 2934101
  have htrace : WordTrace (prefixWord ++ tailWord_2934101) baseStart_2934101 baseEnd_2934101 := by
    simpa [prefixWord, tailWord_2934101, baseEnd_2934101] using wordTrace_append hprefix tailTrace_2934101
  have hstable : (prefixWord ++ tailWord_2934101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934101).length < 2 ^ (prefixWord ++ tailWord_2934101).sum := by decide
  have hdescent : baseEnd_2934101 < baseStart_2934101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934109 : List Nat := [1, 4, 5, 1, 2, 1, 1, 2, 6]
def baseStart_2934109 : Nat := 118140960795 + 2934109 * 2 ^ 59
def prefixEnd_2934109 : Nat := 4983230072969 + 3 ^ 40 * 2934109 * 2
def baseEnd_2934109 : Nat := 167400912186996224304865

theorem tailTrace_2934109 : CollatzResearch.WordTrace tailWord_2934109 prefixEnd_2934109 167400912186996224304865 := by
  unfold tailWord_2934109
  simp only [CollatzResearch.WordTrace]
  refine ⟨107015746927231673767229381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71343831284821115844819587 107015746927231673767229381)
  ·
    refine ⟨20065452548855938831355509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107015746927231673767229381 20065452548855938831355509)
    ·
      refine ⟨1881136176455244265439579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20065452548855938831355509 1881136176455244265439579)
      ·
        refine ⟨2821704264682866398159369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1881136176455244265439579 2821704264682866398159369)
        ·
          refine ⟨2116278198512149798619527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2821704264682866398159369 2116278198512149798619527)
          ·
            refine ⟨3174417297768224697929291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2116278198512149798619527 3174417297768224697929291)
            ·
              refine ⟨4761625946652337046893937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3174417297768224697929291 4761625946652337046893937)
              ·
                refine ⟨3571219459989252785170453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4761625946652337046893937 3571219459989252785170453)
                ·
                  refine ⟨167400912186996224304865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3571219459989252785170453 167400912186996224304865)
                  ·
                    rfl

theorem cell23_2934109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 6].length) (baseStart_2934109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934109 prefixEnd_2934109 := by exact prefixLift 2934109
  have htrace : WordTrace (prefixWord ++ tailWord_2934109) baseStart_2934109 baseEnd_2934109 := by
    simpa [prefixWord, tailWord_2934109, baseEnd_2934109] using wordTrace_append hprefix tailTrace_2934109
  have hstable : (prefixWord ++ tailWord_2934109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934109).length < 2 ^ (prefixWord ++ tailWord_2934109).sum := by decide
  have hdescent : baseEnd_2934109 < baseStart_2934109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934125 : List Nat := [1, 5, 1, 1, 1, 3, 1, 3, 3, 2, 2]
def baseStart_2934125 : Nat := 118140960795 + 2934125 * 2 ^ 59
def prefixEnd_2934125 : Nat := 4983230072969 + 3 ^ 40 * 2934125 * 2
def baseEnd_2934125 : Nat := 1506616425373437956143711

theorem tailTrace_2934125 : CollatzResearch.WordTrace tailWord_2934125 prefixEnd_2934125 1506616425373437956143711 := by
  unfold tailWord_2934125
  simp only [CollatzResearch.WordTrace]
  refine ⟨107016330495173708499811829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71344220330115805666541219 107016330495173708499811829)
  ·
    refine ⟨10032780983922535171857359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107016330495173708499811829 10032780983922535171857359)
    ·
      refine ⟨15049171475883802757786039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10032780983922535171857359 15049171475883802757786039)
      ·
        refine ⟨22573757213825704136679059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15049171475883802757786039 22573757213825704136679059)
        ·
          refine ⟨33860635820738556205018589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22573757213825704136679059 33860635820738556205018589)
          ·
            refine ⟨12697738432776958576881971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33860635820738556205018589 12697738432776958576881971)
            ·
              refine ⟨19046607649165437865322957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12697738432776958576881971 19046607649165437865322957)
              ·
                refine ⟨7142477868437039199496109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19046607649165437865322957 7142477868437039199496109)
                ·
                  refine ⟨2678429200663889699811041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7142477868437039199496109 2678429200663889699811041)
                  ·
                    refine ⟨2008821900497917274858281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2678429200663889699811041 2008821900497917274858281)
                    ·
                      refine ⟨1506616425373437956143711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2008821900497917274858281 1506616425373437956143711)
                      ·
                        rfl

theorem cell23_2934125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_2934125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934125 prefixEnd_2934125 := by exact prefixLift 2934125
  have htrace : WordTrace (prefixWord ++ tailWord_2934125) baseStart_2934125 baseEnd_2934125 := by
    simpa [prefixWord, tailWord_2934125, baseEnd_2934125] using wordTrace_append hprefix tailTrace_2934125
  have hstable : (prefixWord ++ tailWord_2934125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934125).length < 2 ^ (prefixWord ++ tailWord_2934125).sum := by decide
  have hdescent : baseEnd_2934125 < baseStart_2934125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934144 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 2, 7]
def baseStart_2934144 : Nat := 118140960795 + 2934144 * 2 ^ 59
def prefixEnd_2934144 : Nat := 4983230072969 + 3 ^ 40 * 2934144 * 2
def baseEnd_2934144 : Nat := 502208727168624460602041

theorem tailTrace_2934144 : CollatzResearch.WordTrace tailWord_2934144 prefixEnd_2934144 502208727168624460602041 := by
  unfold tailWord_2934144
  simp only [CollatzResearch.WordTrace]
  refine ⟨53508511741052437372376743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71344682321403249829835657 53508511741052437372376743)
  ·
    refine ⟨80262767611578656058565115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53508511741052437372376743 80262767611578656058565115)
    ·
      refine ⟨120394151417367984087847673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80262767611578656058565115 120394151417367984087847673)
      ·
        refine ⟨90295613563025988065885755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120394151417367984087847673 90295613563025988065885755)
        ·
          refine ⟨135443420344538982098828633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90295613563025988065885755 135443420344538982098828633)
          ·
            refine ⟨101582565258404236574121475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135443420344538982098828633 101582565258404236574121475)
            ·
              refine ⟨152373847887606354861182213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101582565258404236574121475 152373847887606354861182213)
              ·
                refine ⟨28570096478926191536471665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152373847887606354861182213 28570096478926191536471665)
                ·
                  refine ⟨21427572359194643652353749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28570096478926191536471665 21427572359194643652353749)
                  ·
                    refine ⟨502208727168624460602041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21427572359194643652353749 502208727168624460602041)
                    ·
                      rfl

theorem cell23_2934144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 2, 7].length) (baseStart_2934144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934144 prefixEnd_2934144 := by exact prefixLift 2934144
  have htrace : WordTrace (prefixWord ++ tailWord_2934144) baseStart_2934144 baseEnd_2934144 := by
    simpa [prefixWord, tailWord_2934144, baseEnd_2934144] using wordTrace_append hprefix tailTrace_2934144
  have hstable : (prefixWord ++ tailWord_2934144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934144).length < 2 ^ (prefixWord ++ tailWord_2934144).sum := by decide
  have hdescent : baseEnd_2934144 < baseStart_2934144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934148 : List Nat := [2, 3, 2, 1, 1, 5, 2, 7]
def baseStart_2934148 : Nat := 118140960795 + 2934148 * 2 ^ 59
def prefixEnd_2934148 : Nat := 4983230072969 + 3 ^ 40 * 2934148 * 2
def baseEnd_2934148 : Nat := 55801045756610791339115

theorem tailTrace_2934148 : CollatzResearch.WordTrace tailWord_2934148 prefixEnd_2934148 55801045756610791339115 := by
  unfold tailWord_2934148
  simp only [CollatzResearch.WordTrace]
  refine ⟨53508584687045191713949549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71344779582726922285266065 53508584687045191713949549)
  ·
    refine ⟨20065719257641946892731081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53508584687045191713949549 20065719257641946892731081)
    ·
      refine ⟨15049289443231460169548311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20065719257641946892731081 15049289443231460169548311)
      ·
        refine ⟨22573934164847190254322467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15049289443231460169548311 22573934164847190254322467)
        ·
          refine ⟨33860901247270785381483701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22573934164847190254322467 33860901247270785381483701)
          ·
            refine ⟨3174459491931636129514097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33860901247270785381483701 3174459491931636129514097)
            ·
              refine ⟨2380844618948727097135573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3174459491931636129514097 2380844618948727097135573)
              ·
                refine ⟨55801045756610791339115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2380844618948727097135573 55801045756610791339115)
                ·
                  rfl

theorem cell23_2934148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 7].length) (baseStart_2934148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934148 prefixEnd_2934148 := by exact prefixLift 2934148
  have htrace : WordTrace (prefixWord ++ tailWord_2934148) baseStart_2934148 baseEnd_2934148 := by
    simpa [prefixWord, tailWord_2934148, baseEnd_2934148] using wordTrace_append hprefix tailTrace_2934148
  have hstable : (prefixWord ++ tailWord_2934148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934148).length < 2 ^ (prefixWord ++ tailWord_2934148).sum := by decide
  have hdescent : baseEnd_2934148 < baseStart_2934148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934231 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 3]
def baseStart_2934231 : Nat := 118140960795 + 2934231 * 2 ^ 59
def prefixEnd_2934231 : Nat := 4983230072969 + 3 ^ 40 * 2934231 * 2
def baseEnd_2934231 : Nat := 1506670854322814541418223

theorem tailTrace_2934231 : CollatzResearch.WordTrace tailWord_2934231 prefixEnd_2934231 1506670854322814541418223 := by
  unfold tailWord_2934231
  simp only [CollatzResearch.WordTrace]
  refine ⟨107020196632789688603170547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71346797755193125735447031 107020196632789688603170547)
  ·
    refine ⟨160530294949184532904755821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107020196632789688603170547 160530294949184532904755821)
    ·
      refine ⟨60198860605944199839283433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160530294949184532904755821 60198860605944199839283433)
      ·
        refine ⟨45149145454458149879462575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60198860605944199839283433 45149145454458149879462575)
        ·
          refine ⟨67723718181687224819193863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45149145454458149879462575 67723718181687224819193863)
          ·
            refine ⟨101585577272530837228790795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67723718181687224819193863 101585577272530837228790795)
            ·
              refine ⟨152378365908796255843186193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101585577272530837228790795 152378365908796255843186193)
              ·
                refine ⟨114283774431597191882389645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152378365908796255843186193 114283774431597191882389645)
                ·
                  refine ⟨42856415411848946955896117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114283774431597191882389645 42856415411848946955896117)
                  ·
                    refine ⟨4017788944860838777115261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42856415411848946955896117 4017788944860838777115261)
                    ·
                      refine ⟨1506670854322814541418223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4017788944860838777115261 1506670854322814541418223)
                      ·
                        rfl

theorem cell23_2934231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_2934231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934231 prefixEnd_2934231 := by exact prefixLift 2934231
  have htrace : WordTrace (prefixWord ++ tailWord_2934231) baseStart_2934231 baseEnd_2934231 := by
    simpa [prefixWord, tailWord_2934231, baseEnd_2934231] using wordTrace_append hprefix tailTrace_2934231
  have hstable : (prefixWord ++ tailWord_2934231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934231).length < 2 ^ (prefixWord ++ tailWord_2934231).sum := by decide
  have hdescent : baseEnd_2934231 < baseStart_2934231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934248 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_2934248 : Nat := 118140960795 + 2934248 * 2 ^ 59
def prefixEnd_2934248 : Nat := 4983230072969 + 3 ^ 40 * 2934248 * 2
def baseEnd_2934248 : Nat := 1506679583493940974905645

theorem tailTrace_2934248 : CollatzResearch.WordTrace tailWord_2934248 prefixEnd_2934248 1506679583493940974905645 := by
  unfold tailWord_2934248
  simp only [CollatzResearch.WordTrace]
  refine ⟨53510408336864050253269699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71347211115818733671026265 53510408336864050253269699)
  ·
    refine ⟨80265612505296075379904549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53510408336864050253269699 80265612505296075379904549)
    ·
      refine ⟨15049802344743014133732103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80265612505296075379904549 15049802344743014133732103)
      ·
        refine ⟨22574703517114521200598155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15049802344743014133732103 22574703517114521200598155)
        ·
          refine ⟨33862055275671781800897233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22574703517114521200598155 33862055275671781800897233)
          ·
            refine ⟨25396541456753836350672925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33862055275671781800897233 25396541456753836350672925)
            ·
              refine ⟨9523703046282688631502347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25396541456753836350672925 9523703046282688631502347)
              ·
                refine ⟨14285554569424032947253521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9523703046282688631502347 14285554569424032947253521)
                ·
                  refine ⟨10714165927068024710440141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14285554569424032947253521 10714165927068024710440141)
                  ·
                    refine ⟨4017812222650509266415053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10714165927068024710440141 4017812222650509266415053)
                    ·
                      refine ⟨1506679583493940974905645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4017812222650509266415053 1506679583493940974905645)
                      ·
                        rfl

theorem cell23_2934248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_2934248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934248 prefixEnd_2934248 := by exact prefixLift 2934248
  have htrace : WordTrace (prefixWord ++ tailWord_2934248) baseStart_2934248 baseEnd_2934248 := by
    simpa [prefixWord, tailWord_2934248, baseEnd_2934248] using wordTrace_append hprefix tailTrace_2934248
  have hstable : (prefixWord ++ tailWord_2934248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934248).length < 2 ^ (prefixWord ++ tailWord_2934248).sum := by decide
  have hdescent : baseEnd_2934248 < baseStart_2934248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934268 : List Nat := [2, 2, 2, 1, 2, 1, 5, 1, 2, 5]
def baseStart_2934268 : Nat := 118140960795 + 2934268 * 2 ^ 59
def prefixEnd_2934268 : Nat := 4983230072969 + 3 ^ 40 * 2934268 * 2
def baseEnd_2934268 : Nat := 502229951035676965551851

theorem tailTrace_2934268 : CollatzResearch.WordTrace tailWord_2934268 prefixEnd_2934268 502229951035676965551851 := by
  unfold tailWord_2934268
  simp only [CollatzResearch.WordTrace]
  refine ⟨53510773066827821961133729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71347697422437095948178305 53510773066827821961133729)
  ·
    refine ⟨40133079800120866470850297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53510773066827821961133729 40133079800120866470850297)
    ·
      refine ⟨30099809850090649853137723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40133079800120866470850297 30099809850090649853137723)
      ·
        refine ⟨45149714775135974779706585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30099809850090649853137723 45149714775135974779706585)
        ·
          refine ⟨33862286081351981084779939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45149714775135974779706585 33862286081351981084779939)
          ·
            refine ⟨50793429122027971627169909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33862286081351981084779939 50793429122027971627169909)
            ·
              refine ⟨4761883980190122340047179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50793429122027971627169909 4761883980190122340047179)
              ·
                refine ⟨7142825970285183510070769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4761883980190122340047179 7142825970285183510070769)
                ·
                  refine ⟨5357119477713887632553077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7142825970285183510070769 5357119477713887632553077)
                  ·
                    refine ⟨502229951035676965551851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5357119477713887632553077 502229951035676965551851)
                    ·
                      rfl

theorem cell23_2934268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_2934268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934268 prefixEnd_2934268 := by exact prefixLift 2934268
  have htrace : WordTrace (prefixWord ++ tailWord_2934268) baseStart_2934268 baseEnd_2934268 := by
    simpa [prefixWord, tailWord_2934268, baseEnd_2934268] using wordTrace_append hprefix tailTrace_2934268
  have hstable : (prefixWord ++ tailWord_2934268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934268).length < 2 ^ (prefixWord ++ tailWord_2934268).sum := by decide
  have hdescent : baseEnd_2934268 < baseStart_2934268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934305 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 2, 4, 2]
def baseStart_2934305 : Nat := 118140960795 + 2934305 * 2 ^ 59
def prefixEnd_2934305 : Nat := 4983230072969 + 3 ^ 40 * 2934305 * 2
def baseEnd_2934305 : Nat := 1506708851891247251892883

theorem tailTrace_2934305 : CollatzResearch.WordTrace tailWord_2934305 prefixEnd_2934305 1506708851891247251892883 := by
  unfold tailWord_2934305
  simp only [CollatzResearch.WordTrace]
  refine ⟨107022895634521599241364369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71348597089681066160909579 107022895634521599241364369)
  ·
    refine ⟨80267171725891199431023277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107022895634521599241364369 80267171725891199431023277)
    ·
      refine ⟨30100189397209199786633729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80267171725891199431023277 30100189397209199786633729)
      ·
        refine ⟨22575142047906899839975297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30100189397209199786633729 22575142047906899839975297)
        ·
          refine ⟨16931356535930174879981473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22575142047906899839975297 16931356535930174879981473)
          ·
            refine ⟨12698517401947631159986105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16931356535930174879981473 12698517401947631159986105)
            ·
              refine ⟨9523888051460723369989579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12698517401947631159986105 9523888051460723369989579)
              ·
                refine ⟨14285832077191085054984369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9523888051460723369989579 14285832077191085054984369)
                ·
                  refine ⟨10714374057893313791238277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14285832077191085054984369 10714374057893313791238277)
                  ·
                    refine ⟨2008945135854996335857177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10714374057893313791238277 2008945135854996335857177)
                    ·
                      refine ⟨1506708851891247251892883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2008945135854996335857177 1506708851891247251892883)
                      ·
                        rfl

theorem cell23_2934305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 4, 2].length) (baseStart_2934305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934305 prefixEnd_2934305 := by exact prefixLift 2934305
  have htrace : WordTrace (prefixWord ++ tailWord_2934305) baseStart_2934305 baseEnd_2934305 := by
    simpa [prefixWord, tailWord_2934305, baseEnd_2934305] using wordTrace_append hprefix tailTrace_2934305
  have hstable : (prefixWord ++ tailWord_2934305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934305).length < 2 ^ (prefixWord ++ tailWord_2934305).sum := by decide
  have hdescent : baseEnd_2934305 < baseStart_2934305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934349 : List Nat := [1, 6, 1, 1, 3, 2, 1, 1, 3, 4]
def baseStart_2934349 : Nat := 118140960795 + 2934349 * 2 ^ 59
def prefixEnd_2934349 : Nat := 4983230072969 + 3 ^ 40 * 2934349 * 2
def baseEnd_2934349 : Nat := 502243815013348359914227

theorem tailTrace_2934349 : CollatzResearch.WordTrace tailWord_2934349 prefixEnd_2934349 502243815013348359914227 := by
  unfold tailWord_2934349
  simp only [CollatzResearch.WordTrace]
  refine ⟨107024500446362194755966101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71349666964241463170644067 107024500446362194755966101)
  ·
    refine ⟨5016773458423227879185911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 107024500446362194755966101 5016773458423227879185911)
    ·
      refine ⟨7525160187634841818778867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5016773458423227879185911 7525160187634841818778867)
      ·
        refine ⟨11287740281452262728168301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7525160187634841818778867 11287740281452262728168301)
        ·
          refine ⟨4232902605544598523063113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11287740281452262728168301 4232902605544598523063113)
          ·
            refine ⟨3174676954158448892297335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4232902605544598523063113 3174676954158448892297335)
            ·
              refine ⟨4762015431237673338446003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3174676954158448892297335 4762015431237673338446003)
              ·
                refine ⟨7143023146856510007669005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4762015431237673338446003 7143023146856510007669005)
                ·
                  refine ⟨2678633680071191252875877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7143023146856510007669005 2678633680071191252875877)
                  ·
                    refine ⟨502243815013348359914227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2678633680071191252875877 502243815013348359914227)
                    ·
                      rfl

theorem cell23_2934349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_2934349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934349 prefixEnd_2934349 := by exact prefixLift 2934349
  have htrace : WordTrace (prefixWord ++ tailWord_2934349) baseStart_2934349 baseEnd_2934349 := by
    simpa [prefixWord, tailWord_2934349, baseEnd_2934349] using wordTrace_append hprefix tailTrace_2934349
  have hstable : (prefixWord ++ tailWord_2934349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934349).length < 2 ^ (prefixWord ++ tailWord_2934349).sum := by decide
  have hdescent : baseEnd_2934349 < baseStart_2934349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934351 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 7]
def baseStart_2934351 : Nat := 118140960795 + 2934351 * 2 ^ 59
def prefixEnd_2934351 : Nat := 4983230072969 + 3 ^ 40 * 2934351 * 2
def baseEnd_2934351 : Nat := 1506732472001354071917671

theorem tailTrace_2934351 : CollatzResearch.WordTrace tailWord_2934351 prefixEnd_2934351 1506732472001354071917671 := by
  unfold tailWord_2934351
  simp only [CollatzResearch.WordTrace]
  refine ⟨107024573392354949097538907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71349715594903299398359271 107024573392354949097538907)
  ·
    refine ⟨160536860088532423646308361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107024573392354949097538907 160536860088532423646308361)
    ·
      refine ⟨120402645066399317734731271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160536860088532423646308361 120402645066399317734731271)
      ·
        refine ⟨180603967599598976602096907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120402645066399317734731271 180603967599598976602096907)
        ·
          refine ⟨270905951399398464903145361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180603967599598976602096907 270905951399398464903145361)
          ·
            refine ⟨203179463549548848677359021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270905951399398464903145361 203179463549548848677359021)
            ·
              refine ⟨76192298831080818254009633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203179463549548848677359021 76192298831080818254009633)
              ·
                refine ⟨57144224123310613690507225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76192298831080818254009633 57144224123310613690507225)
                ·
                  refine ⟨42858168092482960267880419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57144224123310613690507225 42858168092482960267880419)
                  ·
                    refine ⟨64287252138724440401820629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42858168092482960267880419 64287252138724440401820629)
                    ·
                      refine ⟨1506732472001354071917671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 64287252138724440401820629 1506732472001354071917671)
                      ·
                        rfl

theorem cell23_2934351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_2934351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934351 prefixEnd_2934351 := by exact prefixLift 2934351
  have htrace : WordTrace (prefixWord ++ tailWord_2934351) baseStart_2934351 baseEnd_2934351 := by
    simpa [prefixWord, tailWord_2934351, baseEnd_2934351] using wordTrace_append hprefix tailTrace_2934351
  have hstable : (prefixWord ++ tailWord_2934351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934351).length < 2 ^ (prefixWord ++ tailWord_2934351).sum := by decide
  have hdescent : baseEnd_2934351 < baseStart_2934351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934375 : List Nat := [1, 1, 5, 1, 1, 1, 5, 2, 1, 5]
def baseStart_2934375 : Nat := 118140960795 + 2934375 * 2 ^ 59
def prefixEnd_2934375 : Nat := 4983230072969 + 3 ^ 40 * 2934375 * 2
def baseEnd_2934375 : Nat := 502248265179020659339187

theorem tailTrace_2934375 : CollatzResearch.WordTrace tailWord_2934375 prefixEnd_2934375 502248265179020659339187 := by
  unfold tailWord_2934375
  simp only [CollatzResearch.WordTrace]
  refine ⟨107025448744268001196412579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71350299162845334130941719 107025448744268001196412579)
  ·
    refine ⟨160538173116402001794618869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107025448744268001196412579 160538173116402001794618869)
    ·
      refine ⟨15050453729662687668245519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160538173116402001794618869 15050453729662687668245519)
      ·
        refine ⟨22575680594494031502368279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15050453729662687668245519 22575680594494031502368279)
        ·
          refine ⟨33863520891741047253552419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22575680594494031502368279 33863520891741047253552419)
          ·
            refine ⟨50795281337611570880328629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33863520891741047253552419 50795281337611570880328629)
            ·
              refine ⟨4762057625401084770030809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50795281337611570880328629 4762057625401084770030809)
              ·
                refine ⟨3571543219050813577523107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4762057625401084770030809 3571543219050813577523107)
                ·
                  refine ⟨5357314828576220366284661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3571543219050813577523107 5357314828576220366284661)
                  ·
                    refine ⟨502248265179020659339187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5357314828576220366284661 502248265179020659339187)
                    ·
                      rfl

theorem cell23_2934375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_2934375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934375 prefixEnd_2934375 := by exact prefixLift 2934375
  have htrace : WordTrace (prefixWord ++ tailWord_2934375) baseStart_2934375 baseEnd_2934375 := by
    simpa [prefixWord, tailWord_2934375, baseEnd_2934375] using wordTrace_append hprefix tailTrace_2934375
  have hstable : (prefixWord ++ tailWord_2934375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934375).length < 2 ^ (prefixWord ++ tailWord_2934375).sum := by decide
  have hdescent : baseEnd_2934375 < baseStart_2934375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934412 : List Nat := [2, 2, 1, 2, 1, 1, 4, 3, 3, 2, 2]
def baseStart_2934412 : Nat := 118140960795 + 2934412 * 2 ^ 59
def prefixEnd_2934412 : Nat := 4983230072969 + 3 ^ 40 * 2934412 * 2
def baseEnd_2934412 : Nat := 1506763794321278333254891

theorem tailTrace_2934412 : CollatzResearch.WordTrace tailWord_2934412 prefixEnd_2934412 1506763794321278333254891 := by
  unfold tailWord_2934412
  simp only [CollatzResearch.WordTrace]
  refine ⟨53513399122566978257754745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71351198830089304343672993 53513399122566978257754745)
  ·
    refine ⟨40135049341925233693316059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53513399122566978257754745 40135049341925233693316059)
    ·
      refine ⟨60202574012887850539974089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40135049341925233693316059 60202574012887850539974089)
      ·
        refine ⟨45151930509665887904980567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60202574012887850539974089 45151930509665887904980567)
        ·
          refine ⟨67727895764498831857470851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45151930509665887904980567 67727895764498831857470851)
          ·
            refine ⟨101591843646748247786206277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67727895764498831857470851 101591843646748247786206277)
            ·
              refine ⟨19048470683765296459913677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101591843646748247786206277 19048470683765296459913677)
              ·
                refine ⟨7143176506411986172467629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19048470683765296459913677 7143176506411986172467629)
                ·
                  refine ⟨2678691189904494814675361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7143176506411986172467629 2678691189904494814675361)
                  ·
                    refine ⟨2009018392428371111006521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2678691189904494814675361 2009018392428371111006521)
                    ·
                      refine ⟨1506763794321278333254891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2009018392428371111006521 1506763794321278333254891)
                      ·
                        rfl

theorem cell23_2934412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_2934412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934412 prefixEnd_2934412 := by exact prefixLift 2934412
  have htrace : WordTrace (prefixWord ++ tailWord_2934412) baseStart_2934412 baseEnd_2934412 := by
    simpa [prefixWord, tailWord_2934412, baseEnd_2934412] using wordTrace_append hprefix tailTrace_2934412
  have hstable : (prefixWord ++ tailWord_2934412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934412).length < 2 ^ (prefixWord ++ tailWord_2934412).sum := by decide
  have hdescent : baseEnd_2934412 < baseStart_2934412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934440 : List Nat := [2, 1, 7, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_2934440 : Nat := 118140960795 + 2934440 * 2 ^ 59
def prefixEnd_2934440 : Nat := 4983230072969 + 3 ^ 40 * 2934440 * 2
def baseEnd_2934440 : Nat := 1506778171779604223704763

theorem tailTrace_2934440 : CollatzResearch.WordTrace tailWord_2934440 prefixEnd_2934440 1506778171779604223704763 := by
  unfold tailWord_2934440
  simp only [CollatzResearch.WordTrace]
  refine ⟨53513909744516258648764387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71351879659355011531685849 53513909744516258648764387)
  ·
    refine ⟨80270864616774387973146581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53513909744516258648764387 80270864616774387973146581)
    ·
      refine ⟨1881348389455649718120623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 80270864616774387973146581 1881348389455649718120623)
      ·
        refine ⟨2822022584183474577180935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1881348389455649718120623 2822022584183474577180935)
        ·
          refine ⟨4233033876275211865771403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2822022584183474577180935 4233033876275211865771403)
          ·
            refine ⟨6349550814412817798657105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4233033876275211865771403 6349550814412817798657105)
            ·
              refine ⟨4762163110809613348992829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6349550814412817798657105 4762163110809613348992829)
              ·
                refine ⟨1785811166553605005872311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4762163110809613348992829 1785811166553605005872311)
                ·
                  refine ⟨2678716749830407508808467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1785811166553605005872311 2678716749830407508808467)
                  ·
                    refine ⟨4018075124745611263212701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2678716749830407508808467 4018075124745611263212701)
                    ·
                      refine ⟨1506778171779604223704763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4018075124745611263212701 1506778171779604223704763)
                      ·
                        rfl

theorem cell23_2934440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_2934440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934440 prefixEnd_2934440 := by exact prefixLift 2934440
  have htrace : WordTrace (prefixWord ++ tailWord_2934440) baseStart_2934440 baseEnd_2934440 := by
    simpa [prefixWord, tailWord_2934440, baseEnd_2934440] using wordTrace_append hprefix tailTrace_2934440
  have hstable : (prefixWord ++ tailWord_2934440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934440).length < 2 ^ (prefixWord ++ tailWord_2934440).sum := by decide
  have hdescent : baseEnd_2934440 < baseStart_2934440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934466 : List Nat := [3, 5, 1, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_2934466 : Nat := 118140960795 + 2934466 * 2 ^ 59
def prefixEnd_2934466 : Nat := 4983230072969 + 3 ^ 40 * 2934466 * 2
def baseEnd_2934466 : Nat := 1506791522276621121979643

theorem tailTrace_2934466 : CollatzResearch.WordTrace tailWord_2934466 prefixEnd_2934466 1506791522276621121979643 := by
  unfold tailWord_2934466
  simp only [CollatzResearch.WordTrace]
  refine ⟨26757191946734580934493813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71352511857958882491983501 26757191946734580934493813)
  ·
    refine ⟨2508486745006366962608795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26757191946734580934493813 2508486745006366962608795)
    ·
      refine ⟨3762730117509550443913193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2508486745006366962608795 3762730117509550443913193)
      ·
        refine ⟨2822047588132162832934895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3762730117509550443913193 2822047588132162832934895)
        ·
          refine ⟨4233071382198244249402343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2822047588132162832934895 4233071382198244249402343)
          ·
            refine ⟨6349607073297366374103515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4233071382198244249402343 6349607073297366374103515)
            ·
              refine ⟨9524410609946049561155273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6349607073297366374103515 9524410609946049561155273)
              ·
                refine ⟨7143307957459537170866455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9524410609946049561155273 7143307957459537170866455)
                ·
                  refine ⟨10714961936189305756299683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7143307957459537170866455 10714961936189305756299683)
                  ·
                    refine ⟨16072442904283958634449525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10714961936189305756299683 16072442904283958634449525)
                    ·
                      refine ⟨1506791522276621121979643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16072442904283958634449525 1506791522276621121979643)
                      ·
                        rfl

theorem cell23_2934466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_2934466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934466 prefixEnd_2934466 := by exact prefixLift 2934466
  have htrace : WordTrace (prefixWord ++ tailWord_2934466) baseStart_2934466 baseEnd_2934466 := by
    simpa [prefixWord, tailWord_2934466, baseEnd_2934466] using wordTrace_append hprefix tailTrace_2934466
  have hstable : (prefixWord ++ tailWord_2934466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934466).length < 2 ^ (prefixWord ++ tailWord_2934466).sum := by decide
  have hdescent : baseEnd_2934466 < baseStart_2934466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934486 : List Nat := [5, 2, 1, 3, 1, 2, 2, 7]
def baseStart_2934486 : Nat := 118140960795 + 2934486 * 2 ^ 59
def prefixEnd_2934486 : Nat := 4983230072969 + 3 ^ 40 * 2934486 * 2
def baseEnd_2934486 : Nat := 55807473773693001619613

theorem tailTrace_2934486 : CollatzResearch.WordTrace tailWord_2934486 prefixEnd_2934486 55807473773693001619613 := by
  unfold tailWord_2934486
  simp only [CollatzResearch.WordTrace]
  refine ⟨6689343577929116697106457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71352998164577244769135541 6689343577929116697106457)
  ·
    refine ⟨5017007683446837522829843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6689343577929116697106457 5017007683446837522829843)
    ·
      refine ⟨7525511525170256284244765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5017007683446837522829843 7525511525170256284244765)
      ·
        refine ⟨2822066821938846106591787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7525511525170256284244765 2822066821938846106591787)
        ·
          refine ⟨4233100232908269159887681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2822066821938846106591787 4233100232908269159887681)
          ·
            refine ⟨3174825174681201869915761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4233100232908269159887681 3174825174681201869915761)
            ·
              refine ⟨2381118881010901402436821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3174825174681201869915761 2381118881010901402436821)
              ·
                refine ⟨55807473773693001619613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2381118881010901402436821 55807473773693001619613)
                ·
                  rfl

theorem cell23_2934486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_2934486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934486 prefixEnd_2934486 := by exact prefixLift 2934486
  have htrace : WordTrace (prefixWord ++ tailWord_2934486) baseStart_2934486 baseEnd_2934486 := by
    simpa [prefixWord, tailWord_2934486, baseEnd_2934486] using wordTrace_append hprefix tailTrace_2934486
  have hstable : (prefixWord ++ tailWord_2934486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934486).length < 2 ^ (prefixWord ++ tailWord_2934486).sum := by decide
  have hdescent : baseEnd_2934486 < baseStart_2934486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934489 : List Nat := [1, 2, 1, 2, 3, 4, 2, 2, 1, 3, 2]
def baseStart_2934489 : Nat := 118140960795 + 2934489 * 2 ^ 59
def prefixEnd_2934489 : Nat := 4983230072969 + 3 ^ 40 * 2934489 * 2
def baseEnd_2934489 : Nat := 1506803332331674531992037

theorem tailTrace_2934489 : CollatzResearch.WordTrace tailWord_2934489 prefixEnd_2934489 1506803332331674531992037 := by
  unfold tailWord_2934489
  simp only [CollatzResearch.WordTrace]
  refine ⟨107029606665854998666062521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71353071110569999110708347 107029606665854998666062521)
  ·
    refine ⟨80272204999391248999546891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107029606665854998666062521 80272204999391248999546891)
    ·
      refine ⟨120408307499086873499320337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80272204999391248999546891 120408307499086873499320337)
      ·
        refine ⟨90306230624315155124490253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120408307499086873499320337 90306230624315155124490253)
        ·
          refine ⟨33864836484118183171683845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90306230624315155124490253 33864836484118183171683845)
          ·
            refine ⟨6349656840772159344690721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33864836484118183171683845 6349656840772159344690721)
            ·
              refine ⟨4762242630579119508518041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6349656840772159344690721 4762242630579119508518041)
              ·
                refine ⟨3571681972934339631388531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4762242630579119508518041 3571681972934339631388531)
                ·
                  refine ⟨5357522959401509447082797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3571681972934339631388531 5357522959401509447082797)
                  ·
                    refine ⟨2009071109775566042656049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5357522959401509447082797 2009071109775566042656049)
                    ·
                      refine ⟨1506803332331674531992037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2009071109775566042656049 1506803332331674531992037)
                      ·
                        rfl

theorem cell23_2934489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 2, 1, 3, 2].length) (baseStart_2934489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934489 prefixEnd_2934489 := by exact prefixLift 2934489
  have htrace : WordTrace (prefixWord ++ tailWord_2934489) baseStart_2934489 baseEnd_2934489 := by
    simpa [prefixWord, tailWord_2934489, baseEnd_2934489] using wordTrace_append hprefix tailTrace_2934489
  have hstable : (prefixWord ++ tailWord_2934489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934489).length < 2 ^ (prefixWord ++ tailWord_2934489).sum := by decide
  have hdescent : baseEnd_2934489 < baseStart_2934489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934508 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 9]
def baseStart_2934508 : Nat := 118140960795 + 2934508 * 2 ^ 59
def prefixEnd_2934508 : Nat := 4983230072969 + 3 ^ 40 * 2934508 * 2
def baseEnd_2934508 : Nat := 167423676496012217517161

theorem tailTrace_2934508 : CollatzResearch.WordTrace tailWord_2934508 prefixEnd_2934508 167423676496012217517161 := by
  unfold tailWord_2934508
  simp only [CollatzResearch.WordTrace]
  refine ⟨53515149826393082455502089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71353533101857443274002785 53515149826393082455502089)
  ·
    refine ⟨40136362369794811841626567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53515149826393082455502089 40136362369794811841626567)
    ·
      refine ⟨60204543554692217762439851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40136362369794811841626567 60204543554692217762439851)
      ·
        refine ⟨90306815332038326643659777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60204543554692217762439851 90306815332038326643659777)
        ·
          refine ⟨67730111499028744982744833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90306815332038326643659777 67730111499028744982744833)
          ·
            refine ⟨50797583624271558737058625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67730111499028744982744833 50797583624271558737058625)
            ·
              refine ⟨38098187718203669052793969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50797583624271558737058625 38098187718203669052793969)
              ·
                refine ⟨28573640788652751789595477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38098187718203669052793969 28573640788652751789595477)
                ·
                  refine ⟨167423676496012217517161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 28573640788652751789595477 167423676496012217517161)
                  ·
                    rfl

theorem cell23_2934508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 9].length) (baseStart_2934508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934508 prefixEnd_2934508 := by exact prefixLift 2934508
  have htrace : WordTrace (prefixWord ++ tailWord_2934508) baseStart_2934508 baseEnd_2934508 := by
    simpa [prefixWord, tailWord_2934508, baseEnd_2934508] using wordTrace_append hprefix tailTrace_2934508
  have hstable : (prefixWord ++ tailWord_2934508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934508).length < 2 ^ (prefixWord ++ tailWord_2934508).sum := by decide
  have hdescent : baseEnd_2934508 < baseStart_2934508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934534 : List Nat := [6, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3]
def baseStart_2934534 : Nat := 118140960795 + 2934534 * 2 ^ 59
def prefixEnd_2934534 : Nat := 4983230072969 + 3 ^ 40 * 2934534 * 2
def baseEnd_2934534 : Nat := 1506826438961126855929331

theorem tailTrace_2934534 : CollatzResearch.WordTrace tailWord_2934534 prefixEnd_2934534 1506826438961126855929331 := by
  unfold tailWord_2934534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3344726498459124104732833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71354165300461314234300437 3344726498459124104732833)
  ·
    refine ⟨2508544873844343078549625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3344726498459124104732833 2508544873844343078549625)
    ·
      refine ⟨1881408655383257308912219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2508544873844343078549625 1881408655383257308912219)
      ·
        refine ⟨2822112983074885963368329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1881408655383257308912219 2822112983074885963368329)
        ·
          refine ⟨2116584737306164472526247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2822112983074885963368329 2116584737306164472526247)
          ·
            refine ⟨3174877105959246708789371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2116584737306164472526247 3174877105959246708789371)
            ·
              refine ⟨4762315658938870063184057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3174877105959246708789371 4762315658938870063184057)
              ·
                refine ⟨3571736744204152547388043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4762315658938870063184057 3571736744204152547388043)
                ·
                  refine ⟨5357605116306228821082065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3571736744204152547388043 5357605116306228821082065)
                  ·
                    refine ⟨4018203837229671615811549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5357605116306228821082065 4018203837229671615811549)
                    ·
                      refine ⟨1506826438961126855929331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4018203837229671615811549 1506826438961126855929331)
                      ·
                        rfl

theorem cell23_2934534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_2934534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934534 prefixEnd_2934534 := by exact prefixLift 2934534
  have htrace : WordTrace (prefixWord ++ tailWord_2934534) baseStart_2934534 baseEnd_2934534 := by
    simpa [prefixWord, tailWord_2934534, baseEnd_2934534] using wordTrace_append hprefix tailTrace_2934534
  have hstable : (prefixWord ++ tailWord_2934534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934534).length < 2 ^ (prefixWord ++ tailWord_2934534).sum := by decide
  have hdescent : baseEnd_2934534 < baseStart_2934534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934565 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 1, 2, 5]
def baseStart_2934565 : Nat := 118140960795 + 2934565 * 2 ^ 59
def prefixEnd_2934565 : Nat := 4983230072969 + 3 ^ 40 * 2934565 * 2
def baseEnd_2934565 : Nat := 1506842356861416234641687

theorem tailTrace_2934565 : CollatzResearch.WordTrace tailWord_2934565 prefixEnd_2934565 1506842356861416234641687 := by
  unfold tailWord_2934565
  simp only [CollatzResearch.WordTrace]
  refine ⟨107032378613579663645829149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71354919075719775763886099 107032378613579663645829149)
  ·
    refine ⟨40137141980092373867185931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107032378613579663645829149 40137141980092373867185931)
    ·
      refine ⟨60205712970138560800778897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40137141980092373867185931 60205712970138560800778897)
      ·
        refine ⟨45154284727603920600584173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60205712970138560800778897 45154284727603920600584173)
        ·
          refine ⟨16932856772851470225219065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45154284727603920600584173 16932856772851470225219065)
          ·
            refine ⟨12699642579638602668914299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16932856772851470225219065 12699642579638602668914299)
            ·
              refine ⟨19049463869457904003371449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12699642579638602668914299 19049463869457904003371449)
              ·
                refine ⟨14287097902093428002528587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19049463869457904003371449 14287097902093428002528587)
                ·
                  refine ⟨21430646853140142003792881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14287097902093428002528587 21430646853140142003792881)
                  ·
                    refine ⟨16072985139855106502844661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21430646853140142003792881 16072985139855106502844661)
                    ·
                      refine ⟨1506842356861416234641687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16072985139855106502844661 1506842356861416234641687)
                      ·
                        rfl

theorem cell23_2934565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_2934565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934565 prefixEnd_2934565 := by exact prefixLift 2934565
  have htrace : WordTrace (prefixWord ++ tailWord_2934565) baseStart_2934565 baseEnd_2934565 := by
    simpa [prefixWord, tailWord_2934565, baseEnd_2934565] using wordTrace_append hprefix tailTrace_2934565
  have hstable : (prefixWord ++ tailWord_2934565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934565).length < 2 ^ (prefixWord ++ tailWord_2934565).sum := by decide
  have hdescent : baseEnd_2934565 < baseStart_2934565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934602 : List Nat := [3, 1, 2, 1, 1, 1, 5, 2, 3, 4]
def baseStart_2934602 : Nat := 118140960795 + 2934602 * 2 ^ 59
def prefixEnd_2934602 : Nat := 4983230072969 + 3 ^ 40 * 2934602 * 2
def baseEnd_2934602 : Nat := 502287118548544196626339

theorem tailTrace_2934602 : CollatzResearch.WordTrace tailWord_2934602 prefixEnd_2934602 502287118548544196626339 := by
  unfold tailWord_2934602
  simp only [CollatzResearch.WordTrace]
  refine ⟨26758432028611404741231515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71355818742963745976617373 26758432028611404741231515)
  ·
    refine ⟨40137648042917107111847273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26758432028611404741231515 40137648042917107111847273)
    ·
      refine ⟨30103236032187830333885455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40137648042917107111847273 30103236032187830333885455)
      ·
        refine ⟨45154854048281745500828183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30103236032187830333885455 45154854048281745500828183)
        ·
          refine ⟨67732281072422618251242275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45154854048281745500828183 67732281072422618251242275)
          ·
            refine ⟨101598421608633927376863413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67732281072422618251242275 101598421608633927376863413)
            ·
              refine ⟨9524852025809430691580945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101598421608633927376863413 9524852025809430691580945)
              ·
                refine ⟨7143639019357073018685709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9524852025809430691580945 7143639019357073018685709)
                ·
                  refine ⟨2678864632258902382007141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7143639019357073018685709 2678864632258902382007141)
                  ·
                    refine ⟨502287118548544196626339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2678864632258902382007141 502287118548544196626339)
                    ·
                      rfl

theorem cell23_2934602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_2934602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934602 prefixEnd_2934602 := by exact prefixLift 2934602
  have htrace : WordTrace (prefixWord ++ tailWord_2934602) baseStart_2934602 baseEnd_2934602 := by
    simpa [prefixWord, tailWord_2934602, baseEnd_2934602] using wordTrace_append hprefix tailTrace_2934602
  have hstable : (prefixWord ++ tailWord_2934602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934602).length < 2 ^ (prefixWord ++ tailWord_2934602).sum := by decide
  have hdescent : baseEnd_2934602 < baseStart_2934602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934609 : List Nat := [1, 2, 2, 1, 5, 3, 1, 1, 2, 1, 4]
def baseStart_2934609 : Nat := 118140960795 + 2934609 * 2 ^ 59
def prefixEnd_2934609 : Nat := 4983230072969 + 3 ^ 40 * 2934609 * 2
def baseEnd_2934609 : Nat := 1506864950010214062491485

theorem tailTrace_2934609 : CollatzResearch.WordTrace tailWord_2934609 prefixEnd_2934609 1506864950010214062491485 := by
  unfold tailWord_2934609
  simp only [CollatzResearch.WordTrace]
  refine ⟨107033983425420259160430881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71355988950280172773620587 107033983425420259160430881)
  ·
    refine ⟨80275487569065194370323161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107033983425420259160430881 80275487569065194370323161)
    ·
      refine ⟨60206615676798895777742371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80275487569065194370323161 60206615676798895777742371)
      ·
        refine ⟨90309923515198343666613557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60206615676798895777742371 90309923515198343666613557)
        ·
          refine ⟨8466555329549844718745021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90309923515198343666613557 8466555329549844718745021)
          ·
            refine ⟨3174958248581191769529383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8466555329549844718745021 3174958248581191769529383)
            ·
              refine ⟨4762437372871787654294075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3174958248581191769529383 4762437372871787654294075)
              ·
                refine ⟨7143656059307681481441113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4762437372871787654294075 7143656059307681481441113)
                ·
                  refine ⟨5357742044480761111080835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7143656059307681481441113 5357742044480761111080835)
                  ·
                    refine ⟨8036613066721141666621253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5357742044480761111080835 8036613066721141666621253)
                    ·
                      refine ⟨1506864950010214062491485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8036613066721141666621253 1506864950010214062491485)
                      ·
                        rfl

theorem cell23_2934609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 1, 4].length) (baseStart_2934609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934609 prefixEnd_2934609 := by exact prefixLift 2934609
  have htrace : WordTrace (prefixWord ++ tailWord_2934609) baseStart_2934609 baseEnd_2934609 := by
    simpa [prefixWord, tailWord_2934609, baseEnd_2934609] using wordTrace_append hprefix tailTrace_2934609
  have hstable : (prefixWord ++ tailWord_2934609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934609).length < 2 ^ (prefixWord ++ tailWord_2934609).sum := by decide
  have hdescent : baseEnd_2934609 < baseStart_2934609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934659 : List Nat := [1, 1, 1, 3, 4, 2, 2, 2, 3, 1, 3]
def baseStart_2934659 : Nat := 118140960795 + 2934659 * 2 ^ 59
def prefixEnd_2934659 : Nat := 4983230072969 + 3 ^ 40 * 2934659 * 2
def baseEnd_2934659 : Nat := 1506890624042938866866255

theorem tailTrace_2934659 : CollatzResearch.WordTrace tailWord_2934659 prefixEnd_2934659 1506890624042938866866255 := by
  unfold tailWord_2934659
  simp only [CollatzResearch.WordTrace]
  refine ⟨107035807075239117699751031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71357204716826078466500687 107035807075239117699751031)
  ·
    refine ⟨160553710612858676549626547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107035807075239117699751031 160553710612858676549626547)
    ·
      refine ⟨240830565919288014824439821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160553710612858676549626547 240830565919288014824439821)
      ·
        refine ⟨90311462219733005559164933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240830565919288014824439821 90311462219733005559164933)
        ·
          refine ⟨16933399166199938542343425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90311462219733005559164933 16933399166199938542343425)
          ·
            refine ⟨12700049374649953906757569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16933399166199938542343425 12700049374649953906757569)
            ·
              refine ⟨9525037030987465430068177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12700049374649953906757569 9525037030987465430068177)
              ·
                refine ⟨7143777773240599072551133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9525037030987465430068177 7143777773240599072551133)
                ·
                  refine ⟨2678916664965224652206675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7143777773240599072551133 2678916664965224652206675)
                  ·
                    refine ⟨4018374997447836978310013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2678916664965224652206675 4018374997447836978310013)
                    ·
                      refine ⟨1506890624042938866866255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4018374997447836978310013 1506890624042938866866255)
                      ·
                        rfl

theorem cell23_2934659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3, 1, 3].length) (baseStart_2934659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934659 prefixEnd_2934659 := by exact prefixLift 2934659
  have htrace : WordTrace (prefixWord ++ tailWord_2934659) baseStart_2934659 baseEnd_2934659 := by
    simpa [prefixWord, tailWord_2934659, baseEnd_2934659] using wordTrace_append hprefix tailTrace_2934659
  have hstable : (prefixWord ++ tailWord_2934659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934659).length < 2 ^ (prefixWord ++ tailWord_2934659).sum := by decide
  have hdescent : baseEnd_2934659 < baseStart_2934659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934670 : List Nat := [4, 1, 1, 5, 1, 2, 1, 3, 1, 4]
def baseStart_2934670 : Nat := 118140960795 + 2934670 * 2 ^ 59
def prefixEnd_2934670 : Nat := 4983230072969 + 3 ^ 40 * 2934670 * 2
def baseEnd_2934670 : Nat := 502298757443379441276235

theorem tailTrace_2934670 : CollatzResearch.WordTrace tailWord_2934670 prefixEnd_2934670 502298757443379441276235 := by
  unfold tailWord_2934670
  simp only [CollatzResearch.WordTrace]
  refine ⟨13379526034774908322300183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71357472185466177718934309 13379526034774908322300183)
  ·
    refine ⟨20069289052162362483450275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13379526034774908322300183 20069289052162362483450275)
    ·
      refine ⟨30103933578243543725175413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20069289052162362483450275 30103933578243543725175413)
      ·
        refine ⟨2822243772960332224235195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30103933578243543725175413 2822243772960332224235195)
        ·
          refine ⟨4233365659440498336352793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2822243772960332224235195 4233365659440498336352793)
          ·
            refine ⟨3175024244580373752264595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4233365659440498336352793 3175024244580373752264595)
            ·
              refine ⟨4762536366870560628396893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3175024244580373752264595 4762536366870560628396893)
              ·
                refine ⟨1785951137576460235648835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4762536366870560628396893 1785951137576460235648835)
                ·
                  refine ⟨2678926706364690353473253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1785951137576460235648835 2678926706364690353473253)
                  ·
                    refine ⟨502298757443379441276235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2678926706364690353473253 502298757443379441276235)
                    ·
                      rfl

theorem cell23_2934670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 3, 1, 4].length) (baseStart_2934670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934670 prefixEnd_2934670 := by exact prefixLift 2934670
  have htrace : WordTrace (prefixWord ++ tailWord_2934670) baseStart_2934670 baseEnd_2934670 := by
    simpa [prefixWord, tailWord_2934670, baseEnd_2934670] using wordTrace_append hprefix tailTrace_2934670
  have hstable : (prefixWord ++ tailWord_2934670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934670).length < 2 ^ (prefixWord ++ tailWord_2934670).sum := by decide
  have hdescent : baseEnd_2934670 < baseStart_2934670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934712 : List Nat := [2, 1, 2, 1, 2, 3, 2, 3, 1, 2, 4]
def baseStart_2934712 : Nat := 118140960795 + 2934712 * 2 ^ 59
def prefixEnd_2934712 : Nat := 4983230072969 + 3 ^ 40 * 2934712 * 2
def baseEnd_2934712 : Nat := 1506917838517627159503511

theorem tailTrace_2934712 : CollatzResearch.WordTrace tailWord_2934712 prefixEnd_2934712 1506917838517627159503511 := by
  unfold tailWord_2934712
  simp only [CollatzResearch.WordTrace]
  refine ⟨53518870072023553875715195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71358493429364738500953593 53518870072023553875715195)
  ·
    refine ⟨80278305108035330813572793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53518870072023553875715195 80278305108035330813572793)
    ·
      refine ⟨60208728831026498110179595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80278305108035330813572793 60208728831026498110179595)
      ·
        refine ⟨90313093246539747165269393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60208728831026498110179595 90313093246539747165269393)
        ·
          refine ⟨67734819934904810373952045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90313093246539747165269393 67734819934904810373952045)
          ·
            refine ⟨25400557475589303890232017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67734819934904810373952045 25400557475589303890232017)
            ·
              refine ⟨19050418106691977917674013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25400557475589303890232017 19050418106691977917674013)
              ·
                refine ⟨7143906790009491719127755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19050418106691977917674013 7143906790009491719127755)
                ·
                  refine ⟨10715860185014237578691633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7143906790009491719127755 10715860185014237578691633)
                  ·
                    refine ⟨8036895138760678184018725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10715860185014237578691633 8036895138760678184018725)
                    ·
                      refine ⟨1506917838517627159503511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8036895138760678184018725 1506917838517627159503511)
                      ·
                        rfl

theorem cell23_2934712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_2934712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934712 prefixEnd_2934712 := by exact prefixLift 2934712
  have htrace : WordTrace (prefixWord ++ tailWord_2934712) baseStart_2934712 baseEnd_2934712 := by
    simpa [prefixWord, tailWord_2934712, baseEnd_2934712] using wordTrace_append hprefix tailTrace_2934712
  have hstable : (prefixWord ++ tailWord_2934712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934712).length < 2 ^ (prefixWord ++ tailWord_2934712).sum := by decide
  have hdescent : baseEnd_2934712 < baseStart_2934712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934716 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2934716 : Nat := 118140960795 + 2934716 * 2 ^ 59
def prefixEnd_2934716 : Nat := 4983230072969 + 3 ^ 40 * 2934716 * 2
def baseEnd_2934716 : Nat := 1506919892440245143853493

theorem tailTrace_2934716 : CollatzResearch.WordTrace tailWord_2934716 prefixEnd_2934716 1506919892440245143853493 := by
  unfold tailWord_2934716
  simp only [CollatzResearch.WordTrace]
  refine ⟨53518943018016308217288001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71358590690688410956384001 53518943018016308217288001)
  ·
    refine ⟨40139207263512231162966001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53518943018016308217288001 40139207263512231162966001)
    ·
      refine ⟨30104405447634173372224501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40139207263512231162966001 30104405447634173372224501)
      ·
        refine ⟨2822288010715703753646047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30104405447634173372224501 2822288010715703753646047)
        ·
          refine ⟨4233432016073555630469071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2822288010715703753646047 4233432016073555630469071)
          ·
            refine ⟨6350148024110333445703607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4233432016073555630469071 6350148024110333445703607)
            ·
              refine ⟨9525222036165500168555411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6350148024110333445703607 9525222036165500168555411)
              ·
                refine ⟨14287833054248250252833117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9525222036165500168555411 14287833054248250252833117)
                ·
                  refine ⟨5357937395343093844812419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14287833054248250252833117 5357937395343093844812419)
                  ·
                    refine ⟨8036906093014640767218629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5357937395343093844812419 8036906093014640767218629)
                    ·
                      refine ⟨1506919892440245143853493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8036906093014640767218629 1506919892440245143853493)
                      ·
                        rfl

theorem cell23_2934716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2934716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934716 prefixEnd_2934716 := by exact prefixLift 2934716
  have htrace : WordTrace (prefixWord ++ tailWord_2934716) baseStart_2934716 baseEnd_2934716 := by
    simpa [prefixWord, tailWord_2934716, baseEnd_2934716] using wordTrace_append hprefix tailTrace_2934716
  have hstable : (prefixWord ++ tailWord_2934716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934716).length < 2 ^ (prefixWord ++ tailWord_2934716).sum := by decide
  have hdescent : baseEnd_2934716 < baseStart_2934716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934766 : List Nat := [4, 1, 2, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_2934766 : Nat := 118140960795 + 2934766 * 2 ^ 59
def prefixEnd_2934766 : Nat := 4983230072969 + 3 ^ 40 * 2934766 * 2
def baseEnd_2934766 : Nat := 1506945566472969948228263

theorem tailTrace_2934766 : CollatzResearch.WordTrace tailWord_2934766 prefixEnd_2934766 1506945566472969948228263 := by
  unfold tailWord_2934766
  simp only [CollatzResearch.WordTrace]
  refine ⟨13379963710731434371737019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71359806457234316649264101 13379963710731434371737019)
  ·
    refine ⟨20069945566097151557605529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13379963710731434371737019 20069945566097151557605529)
    ·
      refine ⟨15052459174572863668204147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20069945566097151557605529 15052459174572863668204147)
      ·
        refine ⟨22578688761859295502306221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15052459174572863668204147 22578688761859295502306221)
        ·
          refine ⟨8467008285697235813364833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22578688761859295502306221 8467008285697235813364833)
          ·
            refine ⟨6350256214272926860023625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8467008285697235813364833 6350256214272926860023625)
            ·
              refine ⟨4762692160704695145017719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6350256214272926860023625 4762692160704695145017719)
              ·
                refine ⟨7144038241057042717526579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4762692160704695145017719 7144038241057042717526579)
                ·
                  refine ⟨10716057361585564076289869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7144038241057042717526579 10716057361585564076289869)
                  ·
                    refine ⟨4018521510594586528608701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10716057361585564076289869 4018521510594586528608701)
                    ·
                      refine ⟨1506945566472969948228263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4018521510594586528608701 1506945566472969948228263)
                      ·
                        rfl

theorem cell23_2934766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_2934766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934766 prefixEnd_2934766 := by exact prefixLift 2934766
  have htrace : WordTrace (prefixWord ++ tailWord_2934766) baseStart_2934766 baseEnd_2934766 := by
    simpa [prefixWord, tailWord_2934766, baseEnd_2934766] using wordTrace_append hprefix tailTrace_2934766
  have hstable : (prefixWord ++ tailWord_2934766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934766).length < 2 ^ (prefixWord ++ tailWord_2934766).sum := by decide
  have hdescent : baseEnd_2934766 < baseStart_2934766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934792 : List Nat := [2, 1, 3, 2, 1, 2, 2, 1, 1, 3, 5]
def baseStart_2934792 : Nat := 118140960795 + 2934792 * 2 ^ 59
def prefixEnd_2934792 : Nat := 4983230072969 + 3 ^ 40 * 2934792 * 2
def baseEnd_2934792 : Nat := 1506958916969986846503143

theorem tailTrace_2934792 : CollatzResearch.WordTrace tailWord_2934792 prefixEnd_2934792 1506958916969986846503143 := by
  unfold tailWord_2934792
  simp only [CollatzResearch.WordTrace]
  refine ⟨53520328991878640707171315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71360438655838187609561753 53520328991878640707171315)
  ·
    refine ⟨80280493487817961060756973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53520328991878640707171315 80280493487817961060756973)
    ·
      refine ⟨30105185057931735397783865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80280493487817961060756973 30105185057931735397783865)
      ·
        refine ⟨22578888793448801548337899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30105185057931735397783865 22578888793448801548337899)
        ·
          refine ⟨33868333190173202322506849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22578888793448801548337899 33868333190173202322506849)
          ·
            refine ⟨25401249892629901741880137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33868333190173202322506849 25401249892629901741880137)
            ·
              refine ⟨19050937419472426306410103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25401249892629901741880137 19050937419472426306410103)
              ·
                refine ⟨28576406129208639459615155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19050937419472426306410103 28576406129208639459615155)
                ·
                  refine ⟨42864609193812959189422733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28576406129208639459615155 42864609193812959189422733)
                  ·
                    refine ⟨16074228447679859696033525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42864609193812959189422733 16074228447679859696033525)
                    ·
                      refine ⟨1506958916969986846503143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16074228447679859696033525 1506958916969986846503143)
                      ·
                        rfl

theorem cell23_2934792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_2934792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934792 prefixEnd_2934792 := by exact prefixLift 2934792
  have htrace : WordTrace (prefixWord ++ tailWord_2934792) baseStart_2934792 baseEnd_2934792 := by
    simpa [prefixWord, tailWord_2934792, baseEnd_2934792] using wordTrace_append hprefix tailTrace_2934792
  have hstable : (prefixWord ++ tailWord_2934792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934792).length < 2 ^ (prefixWord ++ tailWord_2934792).sum := by decide
  have hdescent : baseEnd_2934792 < baseStart_2934792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934869 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 1, 2, 5]
def baseStart_2934869 : Nat := 118140960795 + 2934869 * 2 ^ 59
def prefixEnd_2934869 : Nat := 4983230072969 + 3 ^ 40 * 2934869 * 2
def baseEnd_2934869 : Nat := 1506998454980383045240289

theorem tailTrace_2934869 : CollatzResearch.WordTrace tailWord_2934869 prefixEnd_2934869 1506998454980383045240289 := by
  unfold tailWord_2934869
  simp only [CollatzResearch.WordTrace]
  refine ⟨107043466404478323564895661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71362310936318882376597107 107043466404478323564895661)
  ·
    refine ⟨40141299901679371336835873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107043466404478323564895661 40141299901679371336835873)
    ·
      refine ⟨30105974926259528502626905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40141299901679371336835873 30105974926259528502626905)
      ·
        refine ⟨22579481194694646376970179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30105974926259528502626905 22579481194694646376970179)
        ·
          refine ⟨33869221792041969565455269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22579481194694646376970179 33869221792041969565455269)
          ·
            refine ⟨6350479086007869293522863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33869221792041969565455269 6350479086007869293522863)
            ·
              refine ⟨9525718629011803940284295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6350479086007869293522863 9525718629011803940284295)
              ·
                refine ⟨14288577943517705910426443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9525718629011803940284295 14288577943517705910426443)
                ·
                  refine ⟨21432866915276558865639665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14288577943517705910426443 21432866915276558865639665)
                  ·
                    refine ⟨16074650186457419149229749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21432866915276558865639665 16074650186457419149229749)
                    ·
                      refine ⟨1506998454980383045240289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16074650186457419149229749 1506998454980383045240289)
                      ·
                        rfl

theorem cell23_2934869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_2934869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934869 prefixEnd_2934869 := by exact prefixLift 2934869
  have htrace : WordTrace (prefixWord ++ tailWord_2934869) baseStart_2934869 baseEnd_2934869 := by
    simpa [prefixWord, tailWord_2934869, baseEnd_2934869] using wordTrace_append hprefix tailTrace_2934869
  have hstable : (prefixWord ++ tailWord_2934869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934869).length < 2 ^ (prefixWord ++ tailWord_2934869).sum := by decide
  have hdescent : baseEnd_2934869 < baseStart_2934869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934889 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 5, 4]
def baseStart_2934889 : Nat := 118140960795 + 2934889 * 2 ^ 59
def prefixEnd_2934889 : Nat := 4983230072969 + 3 ^ 40 * 2934889 * 2
def baseEnd_2934889 : Nat := 502336241531157655663399

theorem tailTrace_2934889 : CollatzResearch.WordTrace tailWord_2934889 prefixEnd_2934889 502336241531157655663399 := by
  unfold tailWord_2934889
  simp only [CollatzResearch.WordTrace]
  refine ⟨107044195864405866980623721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71362797242937244653749147 107044195864405866980623721)
  ·
    refine ⟨80283146898304400235467791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107044195864405866980623721 80283146898304400235467791)
    ·
      refine ⟨120424720347456600353201687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80283146898304400235467791 120424720347456600353201687)
      ·
        refine ⟨180637080521184900529802531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120424720347456600353201687 180637080521184900529802531)
        ·
          refine ⟨270955620781777350794703797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180637080521184900529802531 270955620781777350794703797)
          ·
            refine ⟨25402089448291626637003481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 270955620781777350794703797 25402089448291626637003481)
            ·
              refine ⟨19051567086218719977752611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25402089448291626637003481 19051567086218719977752611)
              ·
                refine ⟨28577350629328079966628917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19051567086218719977752611 28577350629328079966628917)
                ·
                  refine ⟨2679126621499507496871461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28577350629328079966628917 2679126621499507496871461)
                  ·
                    refine ⟨502336241531157655663399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2679126621499507496871461 502336241531157655663399)
                    ·
                      rfl

theorem cell23_2934889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 4].length) (baseStart_2934889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934889 prefixEnd_2934889 := by exact prefixLift 2934889
  have htrace : WordTrace (prefixWord ++ tailWord_2934889) baseStart_2934889 baseEnd_2934889 := by
    simpa [prefixWord, tailWord_2934889, baseEnd_2934889] using wordTrace_append hprefix tailTrace_2934889
  have hstable : (prefixWord ++ tailWord_2934889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934889).length < 2 ^ (prefixWord ++ tailWord_2934889).sum := by decide
  have hdescent : baseEnd_2934889 < baseStart_2934889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934896 : List Nat := [2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 4]
def baseStart_2934896 : Nat := 118140960795 + 2934896 * 2 ^ 59
def prefixEnd_2934896 : Nat := 4983230072969 + 3 ^ 40 * 2934896 * 2
def baseEnd_2934896 : Nat := 1507012318958054439602665

theorem tailTrace_2934896 : CollatzResearch.WordTrace tailWord_2934896 prefixEnd_2934896 1507012318958054439602665 := by
  unfold tailWord_2934896
  simp only [CollatzResearch.WordTrace]
  refine ⟨53522225587690253588064271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71362967450253671450752361 53522225587690253588064271)
  ·
    refine ⟨80283338381535380382096407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53522225587690253588064271 80283338381535380382096407)
    ·
      refine ⟨120425007572303070573144611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80283338381535380382096407 120425007572303070573144611)
      ·
        refine ⟨180637511358454605859716917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120425007572303070573144611 180637511358454605859716917)
        ·
          refine ⟨16934766689855119299348461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 180637511358454605859716917 16934766689855119299348461)
          ·
            refine ⟨6350537508695669737255673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16934766689855119299348461 6350537508695669737255673)
            ·
              refine ⟨4762903131521752302941755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6350537508695669737255673 4762903131521752302941755)
              ·
                refine ⟨7144354697282628454412633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4762903131521752302941755 7144354697282628454412633)
                ·
                  refine ⟨5358266022961971340809475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7144354697282628454412633 5358266022961971340809475)
                  ·
                    refine ⟨8037399034442957011214213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5358266022961971340809475 8037399034442957011214213)
                    ·
                      refine ⟨1507012318958054439602665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8037399034442957011214213 1507012318958054439602665)
                      ·
                        rfl

theorem cell23_2934896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 4].length) (baseStart_2934896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934896 prefixEnd_2934896 := by exact prefixLift 2934896
  have htrace : WordTrace (prefixWord ++ tailWord_2934896) baseStart_2934896 baseEnd_2934896 := by
    simpa [prefixWord, tailWord_2934896, baseEnd_2934896] using wordTrace_append hprefix tailTrace_2934896
  have hstable : (prefixWord ++ tailWord_2934896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934896).length < 2 ^ (prefixWord ++ tailWord_2934896).sum := by decide
  have hdescent : baseEnd_2934896 < baseStart_2934896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934916 : List Nat := [2, 3, 2, 1, 2, 1, 1, 4, 2, 2, 3]
def baseStart_2934916 : Nat := 118140960795 + 2934916 * 2 ^ 59
def prefixEnd_2934916 : Nat := 4983230072969 + 3 ^ 40 * 2934916 * 2
def baseEnd_2934916 : Nat := 1507022588571144361352573

theorem tailTrace_2934916 : CollatzResearch.WordTrace tailWord_2934916 prefixEnd_2934916 1507022588571144361352573 := by
  unfold tailWord_2934916
  simp only [CollatzResearch.WordTrace]
  refine ⟨53522590317654025295928301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71363453756872033727904401 53522590317654025295928301)
  ·
    refine ⟨20070971369120259485973113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53522590317654025295928301 20070971369120259485973113)
    ·
      refine ⟨15053228526840194614479835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20070971369120259485973113 15053228526840194614479835)
      ·
        refine ⟨22579842790260291921719753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15053228526840194614479835 22579842790260291921719753)
        ·
          refine ⟨16934882092695218941289815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22579842790260291921719753 16934882092695218941289815)
          ·
            refine ⟨25402323139042828411934723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16934882092695218941289815 25402323139042828411934723)
            ·
              refine ⟨38103484708564242617902085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25402323139042828411934723 38103484708564242617902085)
              ·
                refine ⟨7144403382855795490856641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38103484708564242617902085 7144403382855795490856641)
                ·
                  refine ⟨5358302537141846618142481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7144403382855795490856641 5358302537141846618142481)
                  ·
                    refine ⟨4018726902856384963606861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5358302537141846618142481 4018726902856384963606861)
                    ·
                      refine ⟨1507022588571144361352573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4018726902856384963606861 1507022588571144361352573)
                      ·
                        rfl

theorem cell23_2934916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_2934916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934916 prefixEnd_2934916 := by exact prefixLift 2934916
  have htrace : WordTrace (prefixWord ++ tailWord_2934916) baseStart_2934916 baseEnd_2934916 := by
    simpa [prefixWord, tailWord_2934916, baseEnd_2934916] using wordTrace_append hprefix tailTrace_2934916
  have hstable : (prefixWord ++ tailWord_2934916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934916).length < 2 ^ (prefixWord ++ tailWord_2934916).sum := by decide
  have hdescent : baseEnd_2934916 < baseStart_2934916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934919 : List Nat := [1, 1, 4, 2, 1, 1, 3, 4, 6]
def baseStart_2934919 : Nat := 118140960795 + 2934919 * 2 ^ 59
def prefixEnd_2934919 : Nat := 4983230072969 + 3 ^ 40 * 2934919 * 2
def baseEnd_2934919 : Nat := 167447125445900872179451

theorem tailTrace_2934919 : CollatzResearch.WordTrace tailWord_2934919 prefixEnd_2934919 167447125445900872179451 := by
  unfold tailWord_2934919
  simp only [CollatzResearch.WordTrace]
  refine ⟨107045290054297182104215811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71363526702864788069477207 107045290054297182104215811)
  ·
    refine ⟨160567935081445773156323717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107045290054297182104215811 160567935081445773156323717)
    ·
      refine ⟨30106487827771082466810697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160567935081445773156323717 30106487827771082466810697)
      ·
        refine ⟨22579865870828311850108023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30106487827771082466810697 22579865870828311850108023)
        ·
          refine ⟨33869798806242467775162035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22579865870828311850108023 33869798806242467775162035)
          ·
            refine ⟨50804698209363701662743053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33869798806242467775162035 50804698209363701662743053)
            ·
              refine ⟨19051761828511388123528645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50804698209363701662743053 19051761828511388123528645)
              ·
                refine ⟨3572205342845885273161621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19051761828511388123528645 3572205342845885273161621)
                ·
                  refine ⟨167447125445900872179451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3572205342845885273161621 167447125445900872179451)
                  ·
                    rfl

theorem cell23_2934919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 6].length) (baseStart_2934919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934919 prefixEnd_2934919 := by exact prefixLift 2934919
  have htrace : WordTrace (prefixWord ++ tailWord_2934919) baseStart_2934919 baseEnd_2934919 := by
    simpa [prefixWord, tailWord_2934919, baseEnd_2934919] using wordTrace_append hprefix tailTrace_2934919
  have hstable : (prefixWord ++ tailWord_2934919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934919).length < 2 ^ (prefixWord ++ tailWord_2934919).sum := by decide
  have hdescent : baseEnd_2934919 < baseStart_2934919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934949 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 3, 5]
def baseStart_2934949 : Nat := 118140960795 + 2934949 * 2 ^ 59
def prefixEnd_2934949 : Nat := 4983230072969 + 3 ^ 40 * 2934949 * 2
def baseEnd_2934949 : Nat := 502346511144247577413307

theorem tailTrace_2934949 : CollatzResearch.WordTrace tailWord_2934949 prefixEnd_2934949 502346511144247577413307 := by
  unfold tailWord_2934949
  simp only [CollatzResearch.WordTrace]
  refine ⟨107046384244188497227807901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71364256162792331485205267 107046384244188497227807901)
  ·
    refine ⟨40142394091570686460427963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107046384244188497227807901 40142394091570686460427963)
    ·
      refine ⟨60213591137356029690641945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40142394091570686460427963 60213591137356029690641945)
      ·
        refine ⟨45160193353017022267981459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60213591137356029690641945 45160193353017022267981459)
        ·
          refine ⟨67740290029525533401972189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45160193353017022267981459 67740290029525533401972189)
          ·
            refine ⟨25402608761072075025739571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67740290029525533401972189 25402608761072075025739571)
            ·
              refine ⟨38103913141608112538609357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25402608761072075025739571 38103913141608112538609357)
              ·
                refine ⟨14288967428103042201978509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38103913141608112538609357 14288967428103042201978509)
                ·
                  refine ⟨5358362785538640825741941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14288967428103042201978509 5358362785538640825741941)
                  ·
                    refine ⟨502346511144247577413307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5358362785538640825741941 502346511144247577413307)
                    ·
                      rfl

theorem cell23_2934949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 5].length) (baseStart_2934949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934949 prefixEnd_2934949 := by exact prefixLift 2934949
  have htrace : WordTrace (prefixWord ++ tailWord_2934949) baseStart_2934949 baseEnd_2934949 := by
    simpa [prefixWord, tailWord_2934949, baseEnd_2934949] using wordTrace_append hprefix tailTrace_2934949
  have hstable : (prefixWord ++ tailWord_2934949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934949).length < 2 ^ (prefixWord ++ tailWord_2934949).sum := by decide
  have hdescent : baseEnd_2934949 < baseStart_2934949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2934980 : List Nat := [2, 3, 3, 1, 2, 2, 2, 1, 3, 1, 3]
def baseStart_2934980 : Nat := 118140960795 + 2934980 * 2 ^ 59
def prefixEnd_2934980 : Nat := 4983230072969 + 3 ^ 40 * 2934980 * 2
def baseEnd_2934980 : Nat := 1507055451333032110952279

theorem tailTrace_2934980 : CollatzResearch.WordTrace tailWord_2934980 prefixEnd_2934980 1507055451333032110952279 := by
  unfold tailWord_2934980
  simp only [CollatzResearch.WordTrace]
  refine ⟨53523757453538094761093197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71365009938050793014790929 53523757453538094761093197)
  ·
    refine ⟨20071409045076785535409949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53523757453538094761093197 20071409045076785535409949)
    ·
      refine ⟨7526778391903794575778731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20071409045076785535409949 7526778391903794575778731)
      ·
        refine ⟨11290167587855691863668097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7526778391903794575778731 11290167587855691863668097)
        ·
          refine ⟨8467625690891768897751073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11290167587855691863668097 8467625690891768897751073)
          ·
            refine ⟨6350719268168826673313305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8467625690891768897751073 6350719268168826673313305)
            ·
              refine ⟨4763039451126620004984979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6350719268168826673313305 4763039451126620004984979)
              ·
                refine ⟨7144559176689930007477469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4763039451126620004984979 7144559176689930007477469)
                ·
                  refine ⟨2679209691258723752804051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7144559176689930007477469 2679209691258723752804051)
                  ·
                    refine ⟨4018814536888085629206077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2679209691258723752804051 4018814536888085629206077)
                    ·
                      refine ⟨1507055451333032110952279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4018814536888085629206077 1507055451333032110952279)
                      ·
                        rfl

theorem cell23_2934980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_2934980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2934980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2934980 prefixEnd_2934980 := by exact prefixLift 2934980
  have htrace : WordTrace (prefixWord ++ tailWord_2934980) baseStart_2934980 baseEnd_2934980 := by
    simpa [prefixWord, tailWord_2934980, baseEnd_2934980] using wordTrace_append hprefix tailTrace_2934980
  have hstable : (prefixWord ++ tailWord_2934980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2934980).length < 2 ^ (prefixWord ++ tailWord_2934980).sum := by decide
  have hdescent : baseEnd_2934980 < baseStart_2934980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2934980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935009 : List Nat := [1, 2, 3, 1, 3, 1, 3, 9]
def baseStart_2935009 : Nat := 118140960795 + 2935009 * 2 ^ 59
def prefixEnd_2935009 : Nat := 4983230072969 + 3 ^ 40 * 2935009 * 2
def baseEnd_2935009 : Nat := 55817420084148611018135

theorem tailTrace_2935009 : CollatzResearch.WordTrace tailWord_2935009 prefixEnd_2935009 55817420084148611018135 := by
  unfold tailWord_2935009
  simp only [CollatzResearch.WordTrace]
  refine ⟨107048572623971127474992081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71365715082647418316661387 107048572623971127474992081)
  ·
    refine ⟨80286429467978345606244061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107048572623971127474992081 80286429467978345606244061)
    ·
      refine ⟨30107411050491879602341523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80286429467978345606244061 30107411050491879602341523)
      ·
        refine ⟨45161116575737819403512285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30107411050491879602341523 45161116575737819403512285)
        ·
          refine ⟨16935418715901682276317107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45161116575737819403512285 16935418715901682276317107)
          ·
            refine ⟨25403128073852523414475661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16935418715901682276317107 25403128073852523414475661)
            ·
              refine ⟨9526173027694696280428373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25403128073852523414475661 9526173027694696280428373)
              ·
                refine ⟨55817420084148611018135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9526173027694696280428373 55817420084148611018135)
                ·
                  rfl

theorem cell23_2935009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 9].length) (baseStart_2935009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935009 prefixEnd_2935009 := by exact prefixLift 2935009
  have htrace : WordTrace (prefixWord ++ tailWord_2935009) baseStart_2935009 baseEnd_2935009 := by
    simpa [prefixWord, tailWord_2935009, baseEnd_2935009] using wordTrace_append hprefix tailTrace_2935009
  have hstable : (prefixWord ++ tailWord_2935009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935009).length < 2 ^ (prefixWord ++ tailWord_2935009).sum := by decide
  have hdescent : baseEnd_2935009 < baseStart_2935009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935023 : List Nat := [1, 1, 2, 1, 6, 1, 2, 3, 1, 2, 3]
def baseStart_2935023 : Nat := 118140960795 + 2935023 * 2 ^ 59
def prefixEnd_2935023 : Nat := 4983230072969 + 3 ^ 40 * 2935023 * 2
def baseEnd_2935023 : Nat := 1507077531001175442714581

theorem tailTrace_2935023 : CollatzResearch.WordTrace tailWord_2935023 prefixEnd_2935023 1507077531001175442714581 := by
  unfold tailWord_2935023
  simp only [CollatzResearch.WordTrace]
  refine ⟨107049083245920407866001723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71366055497280271910667815 107049083245920407866001723)
  ·
    refine ⟨160573624868880611799002585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107049083245920407866001723 160573624868880611799002585)
    ·
      refine ⟨120430218651660458849251939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160573624868880611799002585 120430218651660458849251939)
      ·
        refine ⟨180645327977490688273877909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120430218651660458849251939 180645327977490688273877909)
        ·
          refine ⟨8467749748944876012838027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 180645327977490688273877909 8467749748944876012838027)
          ·
            refine ⟨12701624623417314019257041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8467749748944876012838027 12701624623417314019257041)
            ·
              refine ⟨9526218467562985514442781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12701624623417314019257041 9526218467562985514442781)
              ·
                refine ⟨3572331925336119567916043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9526218467562985514442781 3572331925336119567916043)
                ·
                  refine ⟨5358497888004179351874065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3572331925336119567916043 5358497888004179351874065)
                  ·
                    refine ⟨4018873416003134513905549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5358497888004179351874065 4018873416003134513905549)
                    ·
                      refine ⟨1507077531001175442714581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4018873416003134513905549 1507077531001175442714581)
                      ·
                        rfl

theorem cell23_2935023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 3, 1, 2, 3].length) (baseStart_2935023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935023 prefixEnd_2935023 := by exact prefixLift 2935023
  have htrace : WordTrace (prefixWord ++ tailWord_2935023) baseStart_2935023 baseEnd_2935023 := by
    simpa [prefixWord, tailWord_2935023, baseEnd_2935023] using wordTrace_append hprefix tailTrace_2935023
  have hstable : (prefixWord ++ tailWord_2935023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935023).length < 2 ^ (prefixWord ++ tailWord_2935023).sum := by decide
  have hdescent : baseEnd_2935023 < baseStart_2935023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935026 : List Nat := [3, 2, 1, 3, 2, 3, 9]
def baseStart_2935026 : Nat := 118140960795 + 2935026 * 2 ^ 59
def prefixEnd_2935026 : Nat := 4983230072969 + 3 ^ 40 * 2935026 * 2
def baseEnd_2935026 : Nat := 18605914462260974456507

theorem tailTrace_2935026 : CollatzResearch.WordTrace tailWord_2935026 prefixEnd_2935026 18605914462260974456507 := by
  unfold tailWord_2935026
  simp only [CollatzResearch.WordTrace]
  refine ⟨26762298166227384844590233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71366128443273026252240621 26762298166227384844590233)
  ·
    refine ⟨20071723624670538633442675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26762298166227384844590233 20071723624670538633442675)
    ·
      refine ⟨30107585437005807950164013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20071723624670538633442675 30107585437005807950164013)
      ·
        refine ⟨11290344538877177981311505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30107585437005807950164013 11290344538877177981311505)
        ·
          refine ⟨8467758404157883485983629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11290344538877177981311505 8467758404157883485983629)
          ·
            refine ⟨3175409401559206307243861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8467758404157883485983629 3175409401559206307243861)
            ·
              refine ⟨18605914462260974456507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3175409401559206307243861 18605914462260974456507)
              ·
                rfl

theorem cell23_2935026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 9].length) (baseStart_2935026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935026 prefixEnd_2935026 := by exact prefixLift 2935026
  have htrace : WordTrace (prefixWord ++ tailWord_2935026) baseStart_2935026 baseEnd_2935026 := by
    simpa [prefixWord, tailWord_2935026, baseEnd_2935026] using wordTrace_append hprefix tailTrace_2935026
  have hstable : (prefixWord ++ tailWord_2935026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935026).length < 2 ^ (prefixWord ++ tailWord_2935026).sum := by decide
  have hdescent : baseEnd_2935026 < baseStart_2935026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935039 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 2, 7]
def baseStart_2935039 : Nat := 118140960795 + 2935039 * 2 ^ 59
def prefixEnd_2935039 : Nat := 4983230072969 + 3 ^ 40 * 2935039 * 2
def baseEnd_2935039 : Nat := 502361915563882460038169

theorem tailTrace_2935039 : CollatzResearch.WordTrace tailWord_2935039 prefixEnd_2935039 502361915563882460038169 := by
  unfold tailWord_2935039
  simp only [CollatzResearch.WordTrace]
  refine ⟨107049666813862442598584171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71366444542574961732389447 107049666813862442598584171)
  ·
    refine ⟨160574500220793663897876257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107049666813862442598584171 160574500220793663897876257)
    ·
      refine ⟨120430875165595247923407193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160574500220793663897876257 120430875165595247923407193)
      ·
        refine ⟨90323156374196435942555395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120430875165595247923407193 90323156374196435942555395)
        ·
          refine ⟨135484734561294653913833093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90323156374196435942555395 135484734561294653913833093)
          ·
            refine ⟨25403387730242747608843705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135484734561294653913833093 25403387730242747608843705)
            ·
              refine ⟨19052540797682060706632779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25403387730242747608843705 19052540797682060706632779)
              ·
                refine ⟨28578811196523091059949169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19052540797682060706632779 28578811196523091059949169)
                ·
                  refine ⟨21434108397392318294961877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28578811196523091059949169 21434108397392318294961877)
                  ·
                    refine ⟨502361915563882460038169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21434108397392318294961877 502361915563882460038169)
                    ·
                      rfl

theorem cell23_2935039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 7].length) (baseStart_2935039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935039 prefixEnd_2935039 := by exact prefixLift 2935039
  have htrace : WordTrace (prefixWord ++ tailWord_2935039) baseStart_2935039 baseEnd_2935039 := by
    simpa [prefixWord, tailWord_2935039, baseEnd_2935039] using wordTrace_append hprefix tailTrace_2935039
  have hstable : (prefixWord ++ tailWord_2935039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935039).length < 2 ^ (prefixWord ++ tailWord_2935039).sum := by decide
  have hdescent : baseEnd_2935039 < baseStart_2935039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935070 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_2935070 : Nat := 118140960795 + 2935070 * 2 ^ 59
def prefixEnd_2935070 : Nat := 4983230072969 + 3 ^ 40 * 2935070 * 2
def baseEnd_2935070 : Nat := 1507101664591936758826865

theorem tailTrace_2935070 : CollatzResearch.WordTrace tailWord_2935070 prefixEnd_2935070 1507101664591936758826865 := by
  unfold tailWord_2935070
  simp only [CollatzResearch.WordTrace]
  refine ⟨13381349684593766861620333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71367198317833423261975109 13381349684593766861620333)
  ·
    refine ⟨5018006131722662573107625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13381349684593766861620333 5018006131722662573107625)
    ·
      refine ⟨3763504598791996929830719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5018006131722662573107625 3763504598791996929830719)
      ·
        refine ⟨5645256898187995394746079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3763504598791996929830719 5645256898187995394746079)
        ·
          refine ⟨8467885347281993092119119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5645256898187995394746079 8467885347281993092119119)
          ·
            refine ⟨12701828020922989638178679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8467885347281993092119119 12701828020922989638178679)
            ·
              refine ⟨19052742031384484457268019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12701828020922989638178679 19052742031384484457268019)
              ·
                refine ⟨28579113047076726685902029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19052742031384484457268019 28579113047076726685902029)
                ·
                  refine ⟨10717167392653772507213261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28579113047076726685902029 10717167392653772507213261)
                  ·
                    refine ⟨4018937772245164690204973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10717167392653772507213261 4018937772245164690204973)
                    ·
                      refine ⟨1507101664591936758826865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4018937772245164690204973 1507101664591936758826865)
                      ·
                        rfl

theorem cell23_2935070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_2935070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935070 prefixEnd_2935070 := by exact prefixLift 2935070
  have htrace : WordTrace (prefixWord ++ tailWord_2935070) baseStart_2935070 baseEnd_2935070 := by
    simpa [prefixWord, tailWord_2935070, baseEnd_2935070] using wordTrace_append hprefix tailTrace_2935070
  have hstable : (prefixWord ++ tailWord_2935070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935070).length < 2 ^ (prefixWord ++ tailWord_2935070).sum := by decide
  have hdescent : baseEnd_2935070 < baseStart_2935070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935093 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 3, 4, 2]
def baseStart_2935093 : Nat := 118140960795 + 2935093 * 2 ^ 59
def prefixEnd_2935093 : Nat := 4983230072969 + 3 ^ 40 * 2935093 * 2
def baseEnd_2935093 : Nat := 1507113474646990168839259

theorem tailTrace_2935093 : CollatzResearch.WordTrace tailWord_2935093 prefixEnd_2935093 1507113474646990168839259 := by
  unfold tailWord_2935093
  simp only [CollatzResearch.WordTrace]
  refine ⟨107051636355666809821049933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71367757570444539880699955 107051636355666809821049933)
  ·
    refine ⟨40144363633375053682893725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107051636355666809821049933 40144363633375053682893725)
    ·
      refine ⟨15054136362515645131085147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40144363633375053682893725 15054136362515645131085147)
      ·
        refine ⟨22581204543773467696627721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15054136362515645131085147 22581204543773467696627721)
        ·
          refine ⟨16935903407830100772470791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22581204543773467696627721 16935903407830100772470791)
          ·
            refine ⟨25403855111745151158706187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16935903407830100772470791 25403855111745151158706187)
            ·
              refine ⟨38105782667617726738059281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25403855111745151158706187 38105782667617726738059281)
              ·
                refine ⟨28579337000713295053544461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38105782667617726738059281 28579337000713295053544461)
                ·
                  refine ⟨10717251375267485645079173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28579337000713295053544461 10717251375267485645079173)
                  ·
                    refine ⟨2009484632862653558452345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10717251375267485645079173 2009484632862653558452345)
                    ·
                      refine ⟨1507113474646990168839259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2009484632862653558452345 1507113474646990168839259)
                      ·
                        rfl

theorem cell23_2935093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_2935093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935093 prefixEnd_2935093 := by exact prefixLift 2935093
  have htrace : WordTrace (prefixWord ++ tailWord_2935093) baseStart_2935093 baseEnd_2935093 := by
    simpa [prefixWord, tailWord_2935093, baseEnd_2935093] using wordTrace_append hprefix tailTrace_2935093
  have hstable : (prefixWord ++ tailWord_2935093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935093).length < 2 ^ (prefixWord ++ tailWord_2935093).sum := by decide
  have hdescent : baseEnd_2935093 < baseStart_2935093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935096 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 2, 4, 3]
def baseStart_2935096 : Nat := 118140960795 + 2935096 * 2 ^ 59
def prefixEnd_2935096 : Nat := 4983230072969 + 3 ^ 40 * 2935096 * 2
def baseEnd_2935096 : Nat := 1507115015088953657101745

theorem tailTrace_2935096 : CollatzResearch.WordTrace tailWord_2935096 prefixEnd_2935096 1507115015088953657101745 := by
  unfold tailWord_2935096
  simp only [CollatzResearch.WordTrace]
  refine ⟨53525872887327970666704571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71367830516437294222272761 53525872887327970666704571)
  ·
    refine ⟨80288809330991956000056857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53525872887327970666704571 80288809330991956000056857)
    ·
      refine ⟨60216606998243967000042643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80288809330991956000056857 60216606998243967000042643)
      ·
        refine ⟨90324910497365950500063965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60216606998243967000042643 90324910497365950500063965)
        ·
          refine ⟨33871841436512231437523987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90324910497365950500063965 33871841436512231437523987)
          ·
            refine ⟨50807762154768347156285981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33871841436512231437523987 50807762154768347156285981)
            ·
              refine ⟨19052910808038130183607243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50807762154768347156285981 19052910808038130183607243)
              ·
                refine ⟨28579366212057195275410865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19052910808038130183607243 28579366212057195275410865)
                ·
                  refine ⟨21434524659042896456558149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28579366212057195275410865 21434524659042896456558149)
                  ·
                    refine ⟨4018973373570543085604653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21434524659042896456558149 4018973373570543085604653)
                    ·
                      refine ⟨1507115015088953657101745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4018973373570543085604653 1507115015088953657101745)
                      ·
                        rfl

theorem cell23_2935096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_2935096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935096 prefixEnd_2935096 := by exact prefixLift 2935096
  have htrace : WordTrace (prefixWord ++ tailWord_2935096) baseStart_2935096 baseEnd_2935096 := by
    simpa [prefixWord, tailWord_2935096, baseEnd_2935096] using wordTrace_append hprefix tailTrace_2935096
  have hstable : (prefixWord ++ tailWord_2935096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935096).length < 2 ^ (prefixWord ++ tailWord_2935096).sum := by decide
  have hdescent : baseEnd_2935096 < baseStart_2935096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935116 : List Nat := [2, 2, 1, 3, 2, 1, 3, 2, 7]
def baseStart_2935116 : Nat := 118140960795 + 2935116 * 2 ^ 59
def prefixEnd_2935116 : Nat := 4983230072969 + 3 ^ 40 * 2935116 * 2
def baseEnd_2935116 : Nat := 167458364966893730983517

theorem tailTrace_2935116 : CollatzResearch.WordTrace tailWord_2935116 prefixEnd_2935116 167458364966893730983517 := by
  unfold tailWord_2935116
  simp only [CollatzResearch.WordTrace]
  refine ⟨53526237617291742374568601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71368316823055656499424801 53526237617291742374568601)
  ·
    refine ⟨40144678212968806780926451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53526237617291742374568601 40144678212968806780926451)
    ·
      refine ⟨60217017319453210171389677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40144678212968806780926451 60217017319453210171389677)
      ·
        refine ⟨22581381494794953814271129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60217017319453210171389677 22581381494794953814271129)
        ·
          refine ⟨16936036121096215360703347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22581381494794953814271129 16936036121096215360703347)
          ·
            refine ⟨25404054181644323041055021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16936036121096215360703347 25404054181644323041055021)
            ·
              refine ⟨9526520318116621140395633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25404054181644323041055021 9526520318116621140395633)
              ·
                refine ⟨7144890238587465855296725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9526520318116621140395633 7144890238587465855296725)
                ·
                  refine ⟨167458364966893730983517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7144890238587465855296725 167458364966893730983517)
                  ·
                    rfl

theorem cell23_2935116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 7].length) (baseStart_2935116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935116 prefixEnd_2935116 := by exact prefixLift 2935116
  have htrace : WordTrace (prefixWord ++ tailWord_2935116) baseStart_2935116 baseEnd_2935116 := by
    simpa [prefixWord, tailWord_2935116, baseEnd_2935116] using wordTrace_append hprefix tailTrace_2935116
  have hstable : (prefixWord ++ tailWord_2935116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935116).length < 2 ^ (prefixWord ++ tailWord_2935116).sum := by decide
  have hdescent : baseEnd_2935116 < baseStart_2935116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935143 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_2935143 : Nat := 118140960795 + 2935143 * 2 ^ 59
def prefixEnd_2935143 : Nat := 4983230072969 + 3 ^ 40 * 2935143 * 2
def baseEnd_2935143 : Nat := 1507139148679714973214029

theorem tailTrace_2935143 : CollatzResearch.WordTrace tailWord_2935143 prefixEnd_2935143 1507139148679714973214029 := by
  unfold tailWord_2935143
  simp only [CollatzResearch.WordTrace]
  refine ⟨107053460005485668360370083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71368973336990445573580055 107053460005485668360370083)
  ·
    refine ⟨160580190008228502540555125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107053460005485668360370083 160580190008228502540555125)
    ·
      refine ⟨15054392813271422113177043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160580190008228502540555125 15054392813271422113177043)
      ·
        refine ⟨22581589219907133169765565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15054392813271422113177043 22581589219907133169765565)
        ·
          refine ⟨8468095957465174938662087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22581589219907133169765565 8468095957465174938662087)
          ·
            refine ⟨12702143936197762407993131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8468095957465174938662087 12702143936197762407993131)
            ·
              refine ⟨19053215904296643611989697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12702143936197762407993131 19053215904296643611989697)
              ·
                refine ⟨14289911928222482708992273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19053215904296643611989697 14289911928222482708992273)
                ·
                  refine ⟨10717433946166862031744205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14289911928222482708992273 10717433946166862031744205)
                  ·
                    refine ⟨4019037729812573261904077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10717433946166862031744205 4019037729812573261904077)
                    ·
                      refine ⟨1507139148679714973214029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4019037729812573261904077 1507139148679714973214029)
                      ·
                        rfl

theorem cell23_2935143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_2935143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935143 prefixEnd_2935143 := by exact prefixLift 2935143
  have htrace : WordTrace (prefixWord ++ tailWord_2935143) baseStart_2935143 baseEnd_2935143 := by
    simpa [prefixWord, tailWord_2935143, baseEnd_2935143] using wordTrace_append hprefix tailTrace_2935143
  have hstable : (prefixWord ++ tailWord_2935143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935143).length < 2 ^ (prefixWord ++ tailWord_2935143).sum := by decide
  have hdescent : baseEnd_2935143 < baseStart_2935143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935144 : List Nat := [2, 1, 4, 2, 2, 3, 1, 2, 2, 2, 2]
def baseStart_2935144 : Nat := 118140960795 + 2935144 * 2 ^ 59
def prefixEnd_2935144 : Nat := 4983230072969 + 3 ^ 40 * 2935144 * 2
def baseEnd_2935144 : Nat := 1507139662160369469301525

theorem tailTrace_2935144 : CollatzResearch.WordTrace tailWord_2935144 prefixEnd_2935144 1507139662160369469301525 := by
  unfold tailWord_2935144
  simp only [CollatzResearch.WordTrace]
  refine ⟨53526748239241022765578243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71368997652321363687437657 53526748239241022765578243)
  ·
    refine ⟨80290122358861534148367365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53526748239241022765578243 80290122358861534148367365)
    ·
      refine ⟨15054397942286537652818881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80290122358861534148367365 15054397942286537652818881)
      ·
        refine ⟨11290798456714903239614161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15054397942286537652818881 11290798456714903239614161)
        ·
          refine ⟨8468098842536177429710621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11290798456714903239614161 8468098842536177429710621)
          ·
            refine ⟨3175537065951066536141483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8468098842536177429710621 3175537065951066536141483)
            ·
              refine ⟨4763305598926599804212225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3175537065951066536141483 4763305598926599804212225)
              ·
                refine ⟨3572479199194949853159169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4763305598926599804212225 3572479199194949853159169)
                ·
                  refine ⟨2679359399396212389869377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3572479199194949853159169 2679359399396212389869377)
                  ·
                    refine ⟨2009519549547159292402033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2679359399396212389869377 2009519549547159292402033)
                    ·
                      refine ⟨1507139662160369469301525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2009519549547159292402033 1507139662160369469301525)
                      ·
                        rfl

theorem cell23_2935144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_2935144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935144 prefixEnd_2935144 := by exact prefixLift 2935144
  have htrace : WordTrace (prefixWord ++ tailWord_2935144) baseStart_2935144 baseEnd_2935144 := by
    simpa [prefixWord, tailWord_2935144, baseEnd_2935144] using wordTrace_append hprefix tailTrace_2935144
  have hstable : (prefixWord ++ tailWord_2935144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935144).length < 2 ^ (prefixWord ++ tailWord_2935144).sum := by decide
  have hdescent : baseEnd_2935144 < baseStart_2935144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935176 : List Nat := [2, 1, 3, 3, 1, 1, 1, 1, 2, 8]
def baseStart_2935176 : Nat := 118140960795 + 2935176 * 2 ^ 59
def prefixEnd_2935176 : Nat := 4983230072969 + 3 ^ 40 * 2935176 * 2
def baseEnd_2935176 : Nat := 502385364513771114700459

theorem tailTrace_2935176 : CollatzResearch.WordTrace tailWord_2935176 prefixEnd_2935176 502385364513771114700459 := by
  unfold tailWord_2935176
  simp only [CollatzResearch.WordTrace]
  refine ⟨53527331807183057498160691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71369775742910743330880921 53527331807183057498160691)
  ·
    refine ⟨80290997710774586247241037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53527331807183057498160691 80290997710774586247241037)
    ·
      refine ⟨30109124141540469842715389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80290997710774586247241037 30109124141540469842715389)
      ·
        refine ⟨11290921553077676191018271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30109124141540469842715389 11290921553077676191018271)
        ·
          refine ⟨16936382329616514286527407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11290921553077676191018271 16936382329616514286527407)
          ·
            refine ⟨25404573494424771429791111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16936382329616514286527407 25404573494424771429791111)
            ·
              refine ⟨38106860241637157144686667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25404573494424771429791111 38106860241637157144686667)
              ·
                refine ⟨57160290362455735717030001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38106860241637157144686667 57160290362455735717030001)
                ·
                  refine ⟨42870217771841801787772501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57160290362455735717030001 42870217771841801787772501)
                  ·
                    refine ⟨502385364513771114700459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42870217771841801787772501 502385364513771114700459)
                    ·
                      rfl

theorem cell23_2935176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_2935176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935176 prefixEnd_2935176 := by exact prefixLift 2935176
  have htrace : WordTrace (prefixWord ++ tailWord_2935176) baseStart_2935176 baseEnd_2935176 := by
    simpa [prefixWord, tailWord_2935176, baseEnd_2935176] using wordTrace_append hprefix tailTrace_2935176
  have hstable : (prefixWord ++ tailWord_2935176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935176).length < 2 ^ (prefixWord ++ tailWord_2935176).sum := by decide
  have hdescent : baseEnd_2935176 < baseStart_2935176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935203 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 3]
def baseStart_2935203 : Nat := 118140960795 + 2935203 * 2 ^ 59
def prefixEnd_2935203 : Nat := 4983230072969 + 3 ^ 40 * 2935203 * 2
def baseEnd_2935203 : Nat := 1507169957518984738463753

theorem tailTrace_2935203 : CollatzResearch.WordTrace tailWord_2935203 prefixEnd_2935203 1507169957518984738463753 := by
  unfold tailWord_2935203
  simp only [CollatzResearch.WordTrace]
  refine ⟨107055648385268298607554263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71370432256845532405036175 107055648385268298607554263)
  ·
    refine ⟨160583472577902447911331395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107055648385268298607554263 160583472577902447911331395)
    ·
      refine ⟨240875208866853671866997093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160583472577902447911331395 240875208866853671866997093)
      ·
        refine ⟨45164101662535063475061955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240875208866853671866997093 45164101662535063475061955)
        ·
          refine ⟨67746152493802595212592933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45164101662535063475061955 67746152493802595212592933)
          ·
            refine ⟨12702403592587986602361175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67746152493802595212592933 12702403592587986602361175)
            ·
              refine ⟨19053605388881979903541763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12702403592587986602361175 19053605388881979903541763)
              ·
                refine ⟨28580408083322969855312645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19053605388881979903541763 28580408083322969855312645)
                ·
                  refine ⟨5358826515623056847871121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28580408083322969855312645 5358826515623056847871121)
                  ·
                    refine ⟨4019119886717292635903341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5358826515623056847871121 4019119886717292635903341)
                    ·
                      refine ⟨1507169957518984738463753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4019119886717292635903341 1507169957518984738463753)
                      ·
                        rfl

theorem cell23_2935203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_2935203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935203 prefixEnd_2935203 := by exact prefixLift 2935203
  have htrace : WordTrace (prefixWord ++ tailWord_2935203) baseStart_2935203 baseEnd_2935203 := by
    simpa [prefixWord, tailWord_2935203, baseEnd_2935203] using wordTrace_append hprefix tailTrace_2935203
  have hstable : (prefixWord ++ tailWord_2935203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935203).length < 2 ^ (prefixWord ++ tailWord_2935203).sum := by decide
  have hdescent : baseEnd_2935203 < baseStart_2935203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935223 : List Nat := [1, 1, 3, 1, 3, 4, 1, 3, 6]
def baseStart_2935223 : Nat := 118140960795 + 2935223 * 2 ^ 59
def prefixEnd_2935223 : Nat := 4983230072969 + 3 ^ 40 * 2935223 * 2
def baseEnd_2935223 : Nat := 167464469681341628912629

theorem tailTrace_2935223 : CollatzResearch.WordTrace tailWord_2935223 prefixEnd_2935223 167464469681341628912629 := by
  unfold tailWord_2935223
  simp only [CollatzResearch.WordTrace]
  refine ⟨107056377845195842023282323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71370918563463894682188215 107056377845195842023282323)
  ·
    refine ⟨160584566767793763034923485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107056377845195842023282323 160584566767793763034923485)
    ·
      refine ⟨60219212537922661138096307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160584566767793763034923485 60219212537922661138096307)
      ·
        refine ⟨90328818806883991707144461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60219212537922661138096307 90328818806883991707144461)
        ·
          refine ⟨33873307052581496890179173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90328818806883991707144461 33873307052581496890179173)
          ·
            refine ⟨6351245072359030666908595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33873307052581496890179173 6351245072359030666908595)
            ·
              refine ⟨9526867608538546000362893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6351245072359030666908595 9526867608538546000362893)
              ·
                refine ⟨3572575353201954750136085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9526867608538546000362893 3572575353201954750136085)
                ·
                  refine ⟨167464469681341628912629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3572575353201954750136085 167464469681341628912629)
                  ·
                    rfl

theorem cell23_2935223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 6].length) (baseStart_2935223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935223 prefixEnd_2935223 := by exact prefixLift 2935223
  have htrace : WordTrace (prefixWord ++ tailWord_2935223) baseStart_2935223 baseEnd_2935223 := by
    simpa [prefixWord, tailWord_2935223, baseEnd_2935223] using wordTrace_append hprefix tailTrace_2935223
  have hstable : (prefixWord ++ tailWord_2935223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935223).length < 2 ^ (prefixWord ++ tailWord_2935223).sum := by decide
  have hdescent : baseEnd_2935223 < baseStart_2935223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935226 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6]
def baseStart_2935226 : Nat := 118140960795 + 2935226 * 2 ^ 59
def prefixEnd_2935226 : Nat := 4983230072969 + 3 ^ 40 * 2935226 * 2
def baseEnd_2935226 : Nat := 1507181767574038148476147

theorem tailTrace_2935226 : CollatzResearch.WordTrace tailWord_2935226 prefixEnd_2935226 1507181767574038148476147 := by
  unfold tailWord_2935226
  simp only [CollatzResearch.WordTrace]
  refine ⟨26764121816046243383910383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71370991509456649023761021 26764121816046243383910383)
  ·
    refine ⟨40146182724069365075865575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26764121816046243383910383 40146182724069365075865575)
    ·
      refine ⟨60219274086104047613798363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40146182724069365075865575 60219274086104047613798363)
      ·
        refine ⟨90328911129156071420697545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60219274086104047613798363 90328911129156071420697545)
        ·
          refine ⟨67746683346867053565523159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90328911129156071420697545 67746683346867053565523159)
          ·
            refine ⟨101620025020300580348284739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67746683346867053565523159 101620025020300580348284739)
            ·
              refine ⟨152430037530450870522427109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101620025020300580348284739 152430037530450870522427109)
              ·
                refine ⟨28580632036959538222955083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152430037530450870522427109 28580632036959538222955083)
                ·
                  refine ⟨42870948055439307334432625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28580632036959538222955083 42870948055439307334432625)
                  ·
                    refine ⟨32153211041579480500824469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42870948055439307334432625 32153211041579480500824469)
                    ·
                      refine ⟨1507181767574038148476147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32153211041579480500824469 1507181767574038148476147)
                      ·
                        rfl

theorem cell23_2935226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_2935226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935226 prefixEnd_2935226 := by exact prefixLift 2935226
  have htrace : WordTrace (prefixWord ++ tailWord_2935226) baseStart_2935226 baseEnd_2935226 := by
    simpa [prefixWord, tailWord_2935226, baseEnd_2935226] using wordTrace_append hprefix tailTrace_2935226
  have hstable : (prefixWord ++ tailWord_2935226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935226).length < 2 ^ (prefixWord ++ tailWord_2935226).sum := by decide
  have hdescent : baseEnd_2935226 < baseStart_2935226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935283 : List Nat := [1, 1, 1, 2, 2, 2, 6, 1, 1, 6]
def baseStart_2935283 : Nat := 118140960795 + 2935283 * 2 ^ 59
def prefixEnd_2935283 : Nat := 4983230072969 + 3 ^ 40 * 2935283 * 2
def baseEnd_2935283 : Nat := 502403678657114808487795

theorem tailTrace_2935283 : CollatzResearch.WordTrace tailWord_2935283 prefixEnd_2935283 502403678657114808487795 := by
  unfold tailWord_2935283
  simp only [CollatzResearch.WordTrace]
  refine ⟨107058566224978472270466503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71372377483318981513644335 107058566224978472270466503)
  ·
    refine ⟨160587849337467708405699755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107058566224978472270466503 160587849337467708405699755)
    ·
      refine ⟨240881774006201562608549633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160587849337467708405699755 240881774006201562608549633)
      ·
        refine ⟨180661330504651171956412225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240881774006201562608549633 180661330504651171956412225)
        ·
          refine ⟨135495997878488378967309169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180661330504651171956412225 135495997878488378967309169)
          ·
            refine ⟨101621998408866284225481877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135495997878488378967309169 101621998408866284225481877)
            ·
              refine ⟨4763531175415607073069463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101621998408866284225481877 4763531175415607073069463)
              ·
                refine ⟨7145296763123410609604195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4763531175415607073069463 7145296763123410609604195)
                ·
                  refine ⟨10717945144685115914406293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7145296763123410609604195 10717945144685115914406293)
                  ·
                    refine ⟨502403678657114808487795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10717945144685115914406293 502403678657114808487795)
                    ·
                      rfl

theorem cell23_2935283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 6].length) (baseStart_2935283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935283 prefixEnd_2935283 := by exact prefixLift 2935283
  have htrace : WordTrace (prefixWord ++ tailWord_2935283) baseStart_2935283 baseEnd_2935283 := by
    simpa [prefixWord, tailWord_2935283, baseEnd_2935283] using wordTrace_append hprefix tailTrace_2935283
  have hstable : (prefixWord ++ tailWord_2935283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935283).length < 2 ^ (prefixWord ++ tailWord_2935283).sum := by decide
  have hdescent : baseEnd_2935283 < baseStart_2935283 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935300 : List Nat := [2, 3, 2, 3, 1, 1, 2, 2, 1, 6]
def baseStart_2935300 : Nat := 118140960795 + 2935300 * 2 ^ 59
def prefixEnd_2935300 : Nat := 4983230072969 + 3 ^ 40 * 2935300 * 2
def baseEnd_2935300 : Nat := 502406588380823619650269

theorem tailTrace_2935300 : CollatzResearch.WordTrace tailWord_2935300 prefixEnd_2935300 502406588380823619650269 := by
  unfold tailWord_2935300
  simp only [CollatzResearch.WordTrace]
  refine ⟨53529593132958442086917677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71372790843944589449223569 53529593132958442086917677)
  ·
    refine ⟨20073597424859415782594129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53529593132958442086917677 20073597424859415782594129)
    ·
      refine ⟨15055198068644561836945597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20073597424859415782594129 15055198068644561836945597)
      ·
        refine ⟨5645699275741710688854599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15055198068644561836945597 5645699275741710688854599)
        ·
          refine ⟨8468548913612566033281899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5645699275741710688854599 8468548913612566033281899)
          ·
            refine ⟨12702823370418849049922849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8468548913612566033281899 12702823370418849049922849)
            ·
              refine ⟨9527117527814136787442137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12702823370418849049922849 9527117527814136787442137)
              ·
                refine ⟨7145338145860602590581603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9527117527814136787442137 7145338145860602590581603)
                ·
                  refine ⟨10718007218790903885872405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7145338145860602590581603 10718007218790903885872405)
                  ·
                    refine ⟨502406588380823619650269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10718007218790903885872405 502406588380823619650269)
                    ·
                      rfl

theorem cell23_2935300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_2935300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935300 prefixEnd_2935300 := by exact prefixLift 2935300
  have htrace : WordTrace (prefixWord ++ tailWord_2935300) baseStart_2935300 baseEnd_2935300 := by
    simpa [prefixWord, tailWord_2935300, baseEnd_2935300] using wordTrace_append hprefix tailTrace_2935300
  have hstable : (prefixWord ++ tailWord_2935300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935300).length < 2 ^ (prefixWord ++ tailWord_2935300).sum := by decide
  have hdescent : baseEnd_2935300 < baseStart_2935300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935307 : List Nat := [1, 1, 1, 1, 7, 1, 4, 1, 1, 1, 4]
def baseStart_2935307 : Nat := 118140960795 + 2935307 * 2 ^ 59
def prefixEnd_2935307 : Nat := 4983230072969 + 3 ^ 40 * 2935307 * 2
def baseEnd_2935307 : Nat := 1507223359507052331563275

theorem tailTrace_2935307 : CollatzResearch.WordTrace tailWord_2935307 prefixEnd_2935307 1507223359507052331563275 := by
  unfold tailWord_2935307
  simp only [CollatzResearch.WordTrace]
  refine ⟨107059441576891524369340175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71372961051261016246226783 107059441576891524369340175)
  ·
    refine ⟨160589162365337286554010263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107059441576891524369340175 160589162365337286554010263)
    ·
      refine ⟨240883743548005929831015395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160589162365337286554010263 240883743548005929831015395)
      ·
        refine ⟨361325615322008894746523093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240883743548005929831015395 361325615322008894746523093)
        ·
          refine ⟨8468569109109583470621635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 361325615322008894746523093 8468569109109583470621635)
          ·
            refine ⟨12702853663664375205932453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8468569109109583470621635 12702853663664375205932453)
            ·
              refine ⟨2381785061937070351112335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12702853663664375205932453 2381785061937070351112335)
              ·
                refine ⟨3572677592905605526668503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2381785061937070351112335 3572677592905605526668503)
                ·
                  refine ⟨5359016389358408290002755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3572677592905605526668503 5359016389358408290002755)
                  ·
                    refine ⟨8038524584037612435004133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5359016389358408290002755 8038524584037612435004133)
                    ·
                      refine ⟨1507223359507052331563275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8038524584037612435004133 1507223359507052331563275)
                      ·
                        rfl

theorem cell23_2935307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 1, 1, 4].length) (baseStart_2935307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935307 prefixEnd_2935307 := by exact prefixLift 2935307
  have htrace : WordTrace (prefixWord ++ tailWord_2935307) baseStart_2935307 baseEnd_2935307 := by
    simpa [prefixWord, tailWord_2935307, baseEnd_2935307] using wordTrace_append hprefix tailTrace_2935307
  have hstable : (prefixWord ++ tailWord_2935307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935307).length < 2 ^ (prefixWord ++ tailWord_2935307).sum := by decide
  have hdescent : baseEnd_2935307 < baseStart_2935307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935324 : List Nat := [2, 2, 3, 1, 2, 3, 2, 1, 3, 2, 2]
def baseStart_2935324 : Nat := 118140960795 + 2935324 * 2 ^ 59
def prefixEnd_2935324 : Nat := 4983230072969 + 3 ^ 40 * 2935324 * 2
def baseEnd_2935324 : Nat := 1507232088678178765050697

theorem tailTrace_2935324 : CollatzResearch.WordTrace tailWord_2935324 prefixEnd_2935324 1507232088678178765050697 := by
  unfold tailWord_2935324
  simp only [CollatzResearch.WordTrace]
  refine ⟨53530030808914968136354513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71373374411886624181806017 53530030808914968136354513)
  ·
    refine ⟨40147523106686226102265885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53530030808914968136354513 40147523106686226102265885)
    ·
      refine ⟨15055321165007334788349707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40147523106686226102265885 15055321165007334788349707)
      ·
        refine ⟨22582981747511002182524561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15055321165007334788349707 22582981747511002182524561)
        ·
          refine ⟨16937236310633251636893421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22582981747511002182524561 16937236310633251636893421)
          ·
            refine ⟨6351463616487469363835033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16937236310633251636893421 6351463616487469363835033)
            ·
              refine ⟨4763597712365602022876275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6351463616487469363835033 4763597712365602022876275)
              ·
                refine ⟨7145396568548403034314413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4763597712365602022876275 7145396568548403034314413)
                ·
                  refine ⟨2679523713205651137867905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7145396568548403034314413 2679523713205651137867905)
                  ·
                    refine ⟨2009642784904238353400929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2679523713205651137867905 2009642784904238353400929)
                    ·
                      refine ⟨1507232088678178765050697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2009642784904238353400929 1507232088678178765050697)
                      ·
                        rfl

theorem cell23_2935324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_2935324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935324 prefixEnd_2935324 := by exact prefixLift 2935324
  have htrace : WordTrace (prefixWord ++ tailWord_2935324) baseStart_2935324 baseEnd_2935324 := by
    simpa [prefixWord, tailWord_2935324, baseEnd_2935324] using wordTrace_append hprefix tailTrace_2935324
  have hstable : (prefixWord ++ tailWord_2935324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935324).length < 2 ^ (prefixWord ++ tailWord_2935324).sum := by decide
  have hdescent : baseEnd_2935324 < baseStart_2935324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935353 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 1, 4, 5]
def baseStart_2935353 : Nat := 118140960795 + 2935353 * 2 ^ 59
def prefixEnd_2935353 : Nat := 4983230072969 + 3 ^ 40 * 2935353 * 2
def baseEnd_2935353 : Nat := 1507246979617159151588063

theorem tailTrace_2935353 : CollatzResearch.WordTrace tailWord_2935353 prefixEnd_2935353 1507246979617159151588063 := by
  unfold tailWord_2935353
  simp only [CollatzResearch.WordTrace]
  refine ⟨107061119334724874225514713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71374079556483249483676475 107061119334724874225514713)
  ·
    refine ⟨80295839501043655669136035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107061119334724874225514713 80295839501043655669136035)
    ·
      refine ⟨120443759251565483503704053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80295839501043655669136035 120443759251565483503704053)
      ·
        refine ⟨11291602429834264078472255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120443759251565483503704053 11291602429834264078472255)
        ·
          refine ⟨16937403644751396117708383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11291602429834264078472255 16937403644751396117708383)
          ·
            refine ⟨25406105467127094176562575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16937403644751396117708383 25406105467127094176562575)
            ·
              refine ⟨38109158200690641264843863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25406105467127094176562575 38109158200690641264843863)
              ·
                refine ⟨57163737301035961897265795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38109158200690641264843863 57163737301035961897265795)
                ·
                  refine ⟨85745605951553942845898693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57163737301035961897265795 85745605951553942845898693)
                  ·
                    refine ⟨16077301115916364283606005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85745605951553942845898693 16077301115916364283606005)
                    ·
                      refine ⟨1507246979617159151588063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16077301115916364283606005 1507246979617159151588063)
                      ·
                        rfl

theorem cell23_2935353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_2935353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935353 prefixEnd_2935353 := by exact prefixLift 2935353
  have htrace : WordTrace (prefixWord ++ tailWord_2935353) baseStart_2935353 baseEnd_2935353 := by
    simpa [prefixWord, tailWord_2935353, baseEnd_2935353] using wordTrace_append hprefix tailTrace_2935353
  have hstable : (prefixWord ++ tailWord_2935353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935353).length < 2 ^ (prefixWord ++ tailWord_2935353).sum := by decide
  have hdescent : baseEnd_2935353 < baseStart_2935353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935357 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 4, 1, 3]
def baseStart_2935357 : Nat := 118140960795 + 2935357 * 2 ^ 59
def prefixEnd_2935357 : Nat := 4983230072969 + 3 ^ 40 * 2935357 * 2
def baseEnd_2935357 : Nat := 1507249033539777135938045

theorem tailTrace_2935357 : CollatzResearch.WordTrace tailWord_2935357 prefixEnd_2935357 1507249033539777135938045 := by
  unfold tailWord_2935357
  simp only [CollatzResearch.WordTrace]
  refine ⟨107061265226710382908660325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71374176817806921939106883 107061265226710382908660325)
  ·
    refine ⟨20073987230008196795373811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107061265226710382908660325 20073987230008196795373811)
    ·
      refine ⟨30110980845012295193060717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20073987230008196795373811 30110980845012295193060717)
      ·
        refine ⟨11291617816879610697397769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30110980845012295193060717 11291617816879610697397769)
        ·
          refine ⟨8468713362659708023048327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11291617816879610697397769 8468713362659708023048327)
          ·
            refine ⟨12703070043989562034572491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8468713362659708023048327 12703070043989562034572491)
            ·
              refine ⟨19054605065984343051858737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12703070043989562034572491 19054605065984343051858737)
              ·
                refine ⟨14290953799488257288894053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19054605065984343051858737 14290953799488257288894053)
                ·
                  refine ⟨2679553837404048241667635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14290953799488257288894053 2679553837404048241667635)
                  ·
                    refine ⟨4019330756106072362501453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2679553837404048241667635 4019330756106072362501453)
                    ·
                      refine ⟨1507249033539777135938045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4019330756106072362501453 1507249033539777135938045)
                      ·
                        rfl

theorem cell23_2935357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_2935357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935357 prefixEnd_2935357 := by exact prefixLift 2935357
  have htrace : WordTrace (prefixWord ++ tailWord_2935357) baseStart_2935357 baseEnd_2935357 := by
    simpa [prefixWord, tailWord_2935357, baseEnd_2935357] using wordTrace_append hprefix tailTrace_2935357
  have hstable : (prefixWord ++ tailWord_2935357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935357).length < 2 ^ (prefixWord ++ tailWord_2935357).sum := by decide
  have hdescent : baseEnd_2935357 < baseStart_2935357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935364 : List Nat := [2, 3, 5, 1, 1, 2, 9]
def baseStart_2935364 : Nat := 118140960795 + 2935364 * 2 ^ 59
def prefixEnd_2935364 : Nat := 4983230072969 + 3 ^ 40 * 2935364 * 2
def baseEnd_2935364 : Nat := 18608057134621711216673

theorem tailTrace_2935364 : CollatzResearch.WordTrace tailWord_2935364 prefixEnd_2935364 18608057134621711216673 := by
  unfold tailWord_2935364
  simp only [CollatzResearch.WordTrace]
  refine ⟨53530760268842511552082573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71374347025123348736110097 53530760268842511552082573)
  ·
    refine ⟨20074035100815941832030965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53530760268842511552082573 20074035100815941832030965)
    ·
      refine ⟨1881940790701494546752903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20074035100815941832030965 1881940790701494546752903)
      ·
        refine ⟨2822911186052241820129355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1881940790701494546752903 2822911186052241820129355)
        ·
          refine ⟨4234366779078362730194033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2822911186052241820129355 4234366779078362730194033)
          ·
            refine ⟨3175775084308772047645525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4234366779078362730194033 3175775084308772047645525)
            ·
              refine ⟨18608057134621711216673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3175775084308772047645525 18608057134621711216673)
              ·
                rfl

theorem cell23_2935364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 9].length) (baseStart_2935364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935364 prefixEnd_2935364 := by exact prefixLift 2935364
  have htrace : WordTrace (prefixWord ++ tailWord_2935364) baseStart_2935364 baseEnd_2935364 := by
    simpa [prefixWord, tailWord_2935364, baseEnd_2935364] using wordTrace_append hprefix tailTrace_2935364
  have hstable : (prefixWord ++ tailWord_2935364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935364).length < 2 ^ (prefixWord ++ tailWord_2935364).sum := by decide
  have hdescent : baseEnd_2935364 < baseStart_2935364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935383 : List Nat := [1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 5]
def baseStart_2935383 : Nat := 118140960795 + 2935383 * 2 ^ 59
def prefixEnd_2935383 : Nat := 4983230072969 + 3 ^ 40 * 2935383 * 2
def baseEnd_2935383 : Nat := 1507262384036794034212925

theorem tailTrace_2935383 : CollatzResearch.WordTrace tailWord_2935383 prefixEnd_2935383 1507262384036794034212925 := by
  unfold tailWord_2935383
  simp only [CollatzResearch.WordTrace]
  refine ⟨107062213524616189349106803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71374809016410792899404535 107062213524616189349106803)
  ·
    refine ⟨160593320286924284023660205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107062213524616189349106803 160593320286924284023660205)
    ·
      refine ⟨60222495107596606508872577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160593320286924284023660205 60222495107596606508872577)
      ·
        refine ⟨45166871330697454881654433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60222495107596606508872577 45166871330697454881654433)
        ·
          refine ⟨33875153498023091161240825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45166871330697454881654433 33875153498023091161240825)
          ·
            refine ⟨25406365123517318370930619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33875153498023091161240825 25406365123517318370930619)
            ·
              refine ⟨38109547685275977556395929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25406365123517318370930619 38109547685275977556395929)
              ·
                refine ⟨28582160763956983167296947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38109547685275977556395929 28582160763956983167296947)
                ·
                  refine ⟨42873241145935474750945421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28582160763956983167296947 42873241145935474750945421)
                  ·
                    refine ⟨16077465429725803031604533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42873241145935474750945421 16077465429725803031604533)
                    ·
                      refine ⟨1507262384036794034212925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16077465429725803031604533 1507262384036794034212925)
                      ·
                        rfl

theorem cell23_2935383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_2935383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935383 prefixEnd_2935383 := by exact prefixLift 2935383
  have htrace : WordTrace (prefixWord ++ tailWord_2935383) baseStart_2935383 baseEnd_2935383 := by
    simpa [prefixWord, tailWord_2935383, baseEnd_2935383] using wordTrace_append hprefix tailTrace_2935383
  have hstable : (prefixWord ++ tailWord_2935383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935383).length < 2 ^ (prefixWord ++ tailWord_2935383).sum := by decide
  have hdescent : baseEnd_2935383 < baseStart_2935383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935426 : List Nat := [3, 4, 3, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_2935426 : Nat := 118140960795 + 2935426 * 2 ^ 59
def prefixEnd_2935426 : Nat := 4983230072969 + 3 ^ 40 * 2935426 * 2
def baseEnd_2935426 : Nat := 1507284463704937365975229

theorem tailTrace_2935426 : CollatzResearch.WordTrace tailWord_2935426 prefixEnd_2935426 1507284463704937365975229 := by
  unfold tailWord_2935426
  simp only [CollatzResearch.WordTrace]
  refine ⟨26765945465865101923230533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71375854575640271795281421 26765945465865101923230533)
  ·
    refine ⟨5018614774849706610605725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26765945465865101923230533 5018614774849706610605725)
    ·
      refine ⟨1881980540568639978977147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5018614774849706610605725 1881980540568639978977147)
      ·
        refine ⟨2822970810852959968465721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1881980540568639978977147 2822970810852959968465721)
        ·
          refine ⟨2117228108139719976349291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2822970810852959968465721 2117228108139719976349291)
          ·
            refine ⟨3175842162209579964523937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2117228108139719976349291 3175842162209579964523937)
            ·
              refine ⟨2381881621657184973392953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3175842162209579964523937 2381881621657184973392953)
              ·
                refine ⟨1786411216242888730044715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2381881621657184973392953 1786411216242888730044715)
                ·
                  refine ⟨2679616824364333095067073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1786411216242888730044715 2679616824364333095067073)
                  ·
                    refine ⟨2009712618273249821300305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2679616824364333095067073 2009712618273249821300305)
                    ·
                      refine ⟨1507284463704937365975229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2009712618273249821300305 1507284463704937365975229)
                      ·
                        rfl

theorem cell23_2935426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_2935426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935426 prefixEnd_2935426 := by exact prefixLift 2935426
  have htrace : WordTrace (prefixWord ++ tailWord_2935426) baseStart_2935426 baseEnd_2935426 := by
    simpa [prefixWord, tailWord_2935426, baseEnd_2935426] using wordTrace_append hprefix tailTrace_2935426
  have hstable : (prefixWord ++ tailWord_2935426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935426).length < 2 ^ (prefixWord ++ tailWord_2935426).sum := by decide
  have hdescent : baseEnd_2935426 < baseStart_2935426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935433 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 3, 7]
def baseStart_2935433 : Nat := 118140960795 + 2935433 * 2 ^ 59
def prefixEnd_2935433 : Nat := 4983230072969 + 3 ^ 40 * 2935433 * 2
def baseEnd_2935433 : Nat := 502429352689839612862565

theorem tailTrace_2935433 : CollatzResearch.WordTrace tailWord_2935433 prefixEnd_2935433 502429352689839612862565 := by
  unfold tailWord_2935433
  simp only [CollatzResearch.WordTrace]
  refine ⟨107064037174435047888426953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71376024782956698592284635 107064037174435047888426953)
  ·
    refine ⟨80298027880826285916320215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107064037174435047888426953 80298027880826285916320215)
    ·
      refine ⟨120447041821239428874480323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80298027880826285916320215 120447041821239428874480323)
      ·
        refine ⟨180670562731859143311720485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120447041821239428874480323 180670562731859143311720485)
        ·
          refine ⟨33875730512223589370947591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180670562731859143311720485 33875730512223589370947591)
          ·
            refine ⟨50813595768335384056421387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33875730512223589370947591 50813595768335384056421387)
            ·
              refine ⟨76220393652503076084632081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50813595768335384056421387 76220393652503076084632081)
              ·
                refine ⟨57165295239377307063474061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76220393652503076084632081 57165295239377307063474061)
                ·
                  refine ⟨21436985714766490148802773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57165295239377307063474061 21436985714766490148802773)
                  ·
                    refine ⟨502429352689839612862565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21436985714766490148802773 502429352689839612862565)
                    ·
                      rfl

theorem cell23_2935433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 7].length) (baseStart_2935433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935433 prefixEnd_2935433 := by exact prefixLift 2935433
  have htrace : WordTrace (prefixWord ++ tailWord_2935433) baseStart_2935433 baseEnd_2935433 := by
    simpa [prefixWord, tailWord_2935433, baseEnd_2935433] using wordTrace_append hprefix tailTrace_2935433
  have hstable : (prefixWord ++ tailWord_2935433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935433).length < 2 ^ (prefixWord ++ tailWord_2935433).sum := by decide
  have hdescent : baseEnd_2935433 < baseStart_2935433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935487 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 2, 4, 2]
def baseStart_2935487 : Nat := 118140960795 + 2935487 * 2 ^ 59
def prefixEnd_2935487 : Nat := 4983230072969 + 3 ^ 40 * 2935487 * 2
def baseEnd_2935487 : Nat := 1507315786024861627312447

theorem tailTrace_2935487 : CollatzResearch.WordTrace tailWord_2935487 prefixEnd_2935487 1507315786024861627312447 := by
  unfold tailWord_2935487
  simp only [CollatzResearch.WordTrace]
  refine ⟨107066006716239415110892715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71377337810826276740595143 107066006716239415110892715)
  ·
    refine ⟨160599010074359122666339073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107066006716239415110892715 160599010074359122666339073)
    ·
      refine ⟨120449257555769341999754305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160599010074359122666339073 120449257555769341999754305)
      ·
        refine ⟨90336943166827006499815729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120449257555769341999754305 90336943166827006499815729)
        ·
          refine ⟨67752707375120254874861797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90336943166827006499815729 67752707375120254874861797)
          ·
            refine ⟨12703632632835047789036587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67752707375120254874861797 12703632632835047789036587)
            ·
              refine ⟨19055448949252571683554881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12703632632835047789036587 19055448949252571683554881)
              ·
                refine ⟨14291586711939428762666161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19055448949252571683554881 14291586711939428762666161)
                ·
                  refine ⟨10718690033954571571999621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14291586711939428762666161 10718690033954571571999621)
                  ·
                    refine ⟨2009754381366482169749929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10718690033954571571999621 2009754381366482169749929)
                    ·
                      refine ⟨1507315786024861627312447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2009754381366482169749929 1507315786024861627312447)
                      ·
                        rfl

theorem cell23_2935487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 4, 2].length) (baseStart_2935487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935487 prefixEnd_2935487 := by exact prefixLift 2935487
  have htrace : WordTrace (prefixWord ++ tailWord_2935487) baseStart_2935487 baseEnd_2935487 := by
    simpa [prefixWord, tailWord_2935487, baseEnd_2935487] using wordTrace_append hprefix tailTrace_2935487
  have hstable : (prefixWord ++ tailWord_2935487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935487).length < 2 ^ (prefixWord ++ tailWord_2935487).sum := by decide
  have hdescent : baseEnd_2935487 < baseStart_2935487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935520 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 3]
def baseStart_2935520 : Nat := 118140960795 + 2935520 * 2 ^ 59
def prefixEnd_2935520 : Nat := 4983230072969 + 3 ^ 40 * 2935520 * 2
def baseEnd_2935520 : Nat := 1507332730886459998199795

theorem tailTrace_2935520 : CollatzResearch.WordTrace tailWord_2935520 prefixEnd_2935520 1507332730886459998199795 := by
  unfold tailWord_2935520
  simp only [CollatzResearch.WordTrace]
  refine ⟨53533605162559930873422007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71378140216746574497896009 53533605162559930873422007)
  ·
    refine ⟨80300407743839896310133011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53533605162559930873422007 80300407743839896310133011)
    ·
      refine ⟨120450611615759844465199517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80300407743839896310133011 120450611615759844465199517)
      ·
        refine ⟨45168979355909941674449819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120450611615759844465199517 45168979355909941674449819)
        ·
          refine ⟨67753469033864912511674729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45168979355909941674449819 67753469033864912511674729)
          ·
            refine ⟨50815101775398684383756047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67753469033864912511674729 50815101775398684383756047)
            ·
              refine ⟨76222652663098026575634071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50815101775398684383756047 76222652663098026575634071)
              ·
                refine ⟨114333978994647039863451107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76222652663098026575634071 114333978994647039863451107)
                ·
                  refine ⟨171500968491970559795176661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114333978994647039863451107 171500968491970559795176661)
                  ·
                    refine ⟨4019553949030559995199453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 171500968491970559795176661 4019553949030559995199453)
                    ·
                      refine ⟨1507332730886459998199795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4019553949030559995199453 1507332730886459998199795)
                      ·
                        rfl

theorem cell23_2935520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_2935520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935520 prefixEnd_2935520 := by exact prefixLift 2935520
  have htrace : WordTrace (prefixWord ++ tailWord_2935520) baseStart_2935520 baseEnd_2935520 := by
    simpa [prefixWord, tailWord_2935520, baseEnd_2935520] using wordTrace_append hprefix tailTrace_2935520
  have hstable : (prefixWord ++ tailWord_2935520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935520).length < 2 ^ (prefixWord ++ tailWord_2935520).sum := by decide
  have hdescent : baseEnd_2935520 < baseStart_2935520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935577 : List Nat := [1, 2, 1, 2, 1, 1, 1, 8, 1, 1, 4]
def baseStart_2935577 : Nat := 118140960795 + 2935577 * 2 ^ 59
def prefixEnd_2935577 : Nat := 4983230072969 + 3 ^ 40 * 2935577 * 2
def baseEnd_2935577 : Nat := 1507361999283766275187033

theorem tailTrace_2935577 : CollatzResearch.WordTrace tailWord_2935577 prefixEnd_2935577 1507361999283766275187033 := by
  unfold tailWord_2935577
  simp only [CollatzResearch.WordTrace]
  refine ⟨107069289285913360481668985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71379526190608906987779323 107069289285913360481668985)
  ·
    refine ⟨80301966964435020361251739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107069289285913360481668985 80301966964435020361251739)
    ·
      refine ⟨120452950446652530541877609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80301966964435020361251739 120452950446652530541877609)
      ·
        refine ⟨90339712834989397906408207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120452950446652530541877609 90339712834989397906408207)
        ·
          refine ⟨135509569252484096859612311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90339712834989397906408207 135509569252484096859612311)
          ·
            refine ⟨203264353878726145289418467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135509569252484096859612311 203264353878726145289418467)
            ·
              refine ⟨304896530818089217934127701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203264353878726145289418467 304896530818089217934127701)
              ·
                refine ⟨3573006220524483022665559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 304896530818089217934127701 3573006220524483022665559)
                ·
                  refine ⟨5359509330786724533998339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3573006220524483022665559 5359509330786724533998339)
                  ·
                    refine ⟨8039263996180086800997509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5359509330786724533998339 8039263996180086800997509)
                    ·
                      refine ⟨1507361999283766275187033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8039263996180086800997509 1507361999283766275187033)
                      ·
                        rfl

theorem cell23_2935577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 1, 4].length) (baseStart_2935577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935577 prefixEnd_2935577 := by exact prefixLift 2935577
  have htrace : WordTrace (prefixWord ++ tailWord_2935577) baseStart_2935577 baseEnd_2935577 := by
    simpa [prefixWord, tailWord_2935577, baseEnd_2935577] using wordTrace_append hprefix tailTrace_2935577
  have hstable : (prefixWord ++ tailWord_2935577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935577).length < 2 ^ (prefixWord ++ tailWord_2935577).sum := by decide
  have hdescent : baseEnd_2935577 < baseStart_2935577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935605 : List Nat := [1, 3, 3, 1, 3, 3, 2, 2, 1, 1, 3]
def baseStart_2935605 : Nat := 118140960795 + 2935605 * 2 ^ 59
def prefixEnd_2935605 : Nat := 4983230072969 + 3 ^ 40 * 2935605 * 2
def baseEnd_2935605 : Nat := 1507376376742092165636905

theorem tailTrace_2935605 : CollatzResearch.WordTrace tailWord_2935605 prefixEnd_2935605 1507376376742092165636905 := by
  unfold tailWord_2935605
  simp only [CollatzResearch.WordTrace]
  refine ⟨107070310529811921263688269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71380207019874614175792179 107070310529811921263688269)
  ·
    refine ⟨40151366448679470473883101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107070310529811921263688269 40151366448679470473883101)
    ·
      refine ⟨15056762418254801427706163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40151366448679470473883101 15056762418254801427706163)
      ·
        refine ⟨22585143627382202141559245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15056762418254801427706163 22585143627382202141559245)
        ·
          refine ⟨8469428860268325803084717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22585143627382202141559245 8469428860268325803084717)
          ·
            refine ⟨3176035822600622176156769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8469428860268325803084717 3176035822600622176156769)
            ·
              refine ⟨2382026866950466632117577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3176035822600622176156769 2382026866950466632117577)
              ·
                refine ⟨1786520150212849974088183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2382026866950466632117577 1786520150212849974088183)
                ·
                  refine ⟨2679780225319274961132275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1786520150212849974088183 2679780225319274961132275)
                  ·
                    refine ⟨4019670337978912441698413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2679780225319274961132275 4019670337978912441698413)
                    ·
                      refine ⟨1507376376742092165636905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4019670337978912441698413 1507376376742092165636905)
                      ·
                        rfl

theorem cell23_2935605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_2935605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935605 prefixEnd_2935605 := by exact prefixLift 2935605
  have htrace : WordTrace (prefixWord ++ tailWord_2935605) baseStart_2935605 baseEnd_2935605 := by
    simpa [prefixWord, tailWord_2935605, baseEnd_2935605] using wordTrace_append hprefix tailTrace_2935605
  have hstable : (prefixWord ++ tailWord_2935605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935605).length < 2 ^ (prefixWord ++ tailWord_2935605).sum := by decide
  have hdescent : baseEnd_2935605 < baseStart_2935605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935677 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 2, 6]
def baseStart_2935677 : Nat := 118140960795 + 2935677 * 2 ^ 59
def prefixEnd_2935677 : Nat := 4983230072969 + 3 ^ 40 * 2935677 * 2
def baseEnd_2935677 : Nat := 502471115783071961312191

theorem tailTrace_2935677 : CollatzResearch.WordTrace tailWord_2935677 prefixEnd_2935677 502471115783071961312191 := by
  unfold tailWord_2935677
  simp only [CollatzResearch.WordTrace]
  refine ⟨107072936585551077560309285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71381957723700718373539523 107072936585551077560309285)
  ·
    refine ⟨20076175609790827042557991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107072936585551077560309285 20076175609790827042557991)
    ·
      refine ⟨30114263414686240563836987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20076175609790827042557991 30114263414686240563836987)
      ·
        refine ⟨45171395122029360845755481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30114263414686240563836987 45171395122029360845755481)
        ·
          refine ⟨33878546341522020634316611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45171395122029360845755481 33878546341522020634316611)
          ·
            refine ⟨50817819512283030951474917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33878546341522020634316611 50817819512283030951474917)
            ·
              refine ⟨9528341158553068303401547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50817819512283030951474917 9528341158553068303401547)
              ·
                refine ⟨14292511737829602455102321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9528341158553068303401547 14292511737829602455102321)
                ·
                  refine ⟨10719383803372201841326741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14292511737829602455102321 10719383803372201841326741)
                  ·
                    refine ⟨502471115783071961312191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10719383803372201841326741 502471115783071961312191)
                    ·
                      rfl

theorem cell23_2935677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_2935677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935677 prefixEnd_2935677 := by exact prefixLift 2935677
  have htrace : WordTrace (prefixWord ++ tailWord_2935677) baseStart_2935677 baseEnd_2935677 := by
    simpa [prefixWord, tailWord_2935677, baseEnd_2935677] using wordTrace_append hprefix tailTrace_2935677
  have hstable : (prefixWord ++ tailWord_2935677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935677).length < 2 ^ (prefixWord ++ tailWord_2935677).sum := by decide
  have hdescent : baseEnd_2935677 < baseStart_2935677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935688 : List Nat := [2, 1, 3, 3, 2, 2, 2, 2, 1, 3, 2]
def baseStart_2935688 : Nat := 118140960795 + 2935688 * 2 ^ 59
def prefixEnd_2935688 : Nat := 4983230072969 + 3 ^ 40 * 2935688 * 2
def baseEnd_2935688 : Nat := 1507418995636415340899023

theorem tailTrace_2935688 : CollatzResearch.WordTrace tailWord_2935688 prefixEnd_2935688 1507418995636415340899023 := by
  unfold tailWord_2935688
  simp only [CollatzResearch.WordTrace]
  refine ⟨53536668894255613219479859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71382225192340817625973145 53536668894255613219479859)
  ·
    refine ⟨80305003341383419829219789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53536668894255613219479859 80305003341383419829219789)
    ·
      refine ⟨30114376253018782435957421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80305003341383419829219789 30114376253018782435957421)
      ·
        refine ⟨11292891094882043413484033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30114376253018782435957421 11292891094882043413484033)
        ·
          refine ⟨8469668321161532560113025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11292891094882043413484033 8469668321161532560113025)
          ·
            refine ⟨6352251240871149420084769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8469668321161532560113025 6352251240871149420084769)
            ·
              refine ⟨4764188430653362065063577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6352251240871149420084769 4764188430653362065063577)
              ·
                refine ⟨3573141322990021548797683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4764188430653362065063577 3573141322990021548797683)
                ·
                  refine ⟨5359711984485032323196525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3573141322990021548797683 5359711984485032323196525)
                  ·
                    refine ⟨2009891994181887121198697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5359711984485032323196525 2009891994181887121198697)
                    ·
                      refine ⟨1507418995636415340899023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2009891994181887121198697 1507418995636415340899023)
                      ·
                        rfl

theorem cell23_2935688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_2935688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935688 prefixEnd_2935688 := by exact prefixLift 2935688
  have htrace : WordTrace (prefixWord ++ tailWord_2935688) baseStart_2935688 baseEnd_2935688 := by
    simpa [prefixWord, tailWord_2935688, baseEnd_2935688] using wordTrace_append hprefix tailTrace_2935688
  have hstable : (prefixWord ++ tailWord_2935688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935688).length < 2 ^ (prefixWord ++ tailWord_2935688).sum := by decide
  have hdescent : baseEnd_2935688 < baseStart_2935688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935701 : List Nat := [1, 3, 2, 1, 1, 4, 1, 2, 4, 2, 2]
def baseStart_2935701 : Nat := 118140960795 + 2935701 * 2 ^ 59
def prefixEnd_2935701 : Nat := 4983230072969 + 3 ^ 40 * 2935701 * 2
def baseEnd_2935701 : Nat := 1507425670884923790036463

theorem tailTrace_2935701 : CollatzResearch.WordTrace tailWord_2935701 prefixEnd_2935701 1507425670884923790036463 := by
  unfold tailWord_2935701
  simp only [CollatzResearch.WordTrace]
  refine ⟨107073811937464129659182957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71382541291642753106121971 107073811937464129659182957)
  ·
    refine ⟨40152679476549048622193609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107073811937464129659182957 40152679476549048622193609)
    ·
      refine ⟨30114509607411786466645207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40152679476549048622193609 30114509607411786466645207)
      ·
        refine ⟨45171764411117679699967811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30114509607411786466645207 45171764411117679699967811)
        ·
          refine ⟨67757646616676519549951717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45171764411117679699967811 67757646616676519549951717)
          ·
            refine ⟨12704558740626847415615947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67757646616676519549951717 12704558740626847415615947)
            ·
              refine ⟨19056838110940271123423921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12704558740626847415615947 19056838110940271123423921)
              ·
                refine ⟨14292628583205203342567941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19056838110940271123423921 14292628583205203342567941)
                ·
                  refine ⟨2679867859350975626731489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14292628583205203342567941 2679867859350975626731489)
                  ·
                    refine ⟨2009900894513231720048617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2679867859350975626731489 2009900894513231720048617)
                    ·
                      refine ⟨1507425670884923790036463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2009900894513231720048617 1507425670884923790036463)
                      ·
                        rfl

theorem cell23_2935701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_2935701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935701 prefixEnd_2935701 := by exact prefixLift 2935701
  have htrace : WordTrace (prefixWord ++ tailWord_2935701) baseStart_2935701 baseEnd_2935701 := by
    simpa [prefixWord, tailWord_2935701, baseEnd_2935701] using wordTrace_append hprefix tailTrace_2935701
  have hstable : (prefixWord ++ tailWord_2935701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935701).length < 2 ^ (prefixWord ++ tailWord_2935701).sum := by decide
  have hdescent : baseEnd_2935701 < baseStart_2935701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935764 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 1, 2, 5]
def baseStart_2935764 : Nat := 118140960795 + 2935764 * 2 ^ 59
def prefixEnd_2935764 : Nat := 4983230072969 + 3 ^ 40 * 2935764 * 2
def baseEnd_2935764 : Nat := 1507458020166157043548673

theorem tailTrace_2935764 : CollatzResearch.WordTrace tailWord_2935764 prefixEnd_2935764 1507458020166157043548673 := by
  unfold tailWord_2935764
  simp only [CollatzResearch.WordTrace]
  refine ⟨53538054868117945709363173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71384073157490594279150897 53538054868117945709363173)
  ·
    refine ⟨10038385287772114820505595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53538054868117945709363173 10038385287772114820505595)
    ·
      refine ⟨15057577931658172230758393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10038385287772114820505595 15057577931658172230758393)
      ·
        refine ⟨11293183448743629173068795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15057577931658172230758393 11293183448743629173068795)
        ·
          refine ⟨16939775173115443759603193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11293183448743629173068795 16939775173115443759603193)
          ·
            refine ⟨12704831379836582819702395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16939775173115443759603193 12704831379836582819702395)
            ·
              refine ⟨19057247069754874229553593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12704831379836582819702395 19057247069754874229553593)
              ·
                refine ⟨14292935302316155672165195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19057247069754874229553593 14292935302316155672165195)
                ·
                  refine ⟨21439402953474233508247793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14292935302316155672165195 21439402953474233508247793)
                  ·
                    refine ⟨16079552215105675131185845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21439402953474233508247793 16079552215105675131185845)
                    ·
                      refine ⟨1507458020166157043548673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16079552215105675131185845 1507458020166157043548673)
                      ·
                        rfl

theorem cell23_2935764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_2935764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935764 prefixEnd_2935764 := by exact prefixLift 2935764
  have htrace : WordTrace (prefixWord ++ tailWord_2935764) baseStart_2935764 baseEnd_2935764 := by
    simpa [prefixWord, tailWord_2935764, baseEnd_2935764] using wordTrace_append hprefix tailTrace_2935764
  have hstable : (prefixWord ++ tailWord_2935764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935764).length < 2 ^ (prefixWord ++ tailWord_2935764).sum := by decide
  have hdescent : baseEnd_2935764 < baseStart_2935764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935775 : List Nat := [1, 1, 2, 3, 6, 1, 2, 2, 5]
def baseStart_2935775 : Nat := 118140960795 + 2935775 * 2 ^ 59
def prefixEnd_2935775 : Nat := 4983230072969 + 3 ^ 40 * 2935775 * 2
def baseEnd_2935775 : Nat := 167495963161484055612347

theorem tailTrace_2935775 : CollatzResearch.WordTrace tailWord_2935775 prefixEnd_2935775 167495963161484055612347 := by
  unfold tailWord_2935775
  simp only [CollatzResearch.WordTrace]
  refine ⟨107076510939196040297376779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71384340626130693531584519 107076510939196040297376779)
  ·
    refine ⟨160614766408794060446065169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107076510939196040297376779 160614766408794060446065169)
    ·
      refine ⟨120461074806595545334548877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160614766408794060446065169 120461074806595545334548877)
      ·
        refine ⟨45172903052473329500455829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120461074806595545334548877 45172903052473329500455829)
        ·
          refine ⟨2117479830584687320333867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45172903052473329500455829 2117479830584687320333867)
          ·
            refine ⟨3176219745877030980500801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2117479830584687320333867 3176219745877030980500801)
            ·
              refine ⟨2382164809407773235375601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3176219745877030980500801 2382164809407773235375601)
              ·
                refine ⟨1786623607055829926531701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2382164809407773235375601 1786623607055829926531701)
                ·
                  refine ⟨167495963161484055612347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1786623607055829926531701 167495963161484055612347)
                  ·
                    rfl

theorem cell23_2935775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 2, 5].length) (baseStart_2935775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935775 prefixEnd_2935775 := by exact prefixLift 2935775
  have htrace : WordTrace (prefixWord ++ tailWord_2935775) baseStart_2935775 baseEnd_2935775 := by
    simpa [prefixWord, tailWord_2935775, baseEnd_2935775] using wordTrace_append hprefix tailTrace_2935775
  have hstable : (prefixWord ++ tailWord_2935775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935775).length < 2 ^ (prefixWord ++ tailWord_2935775).sum := by decide
  have hdescent : baseEnd_2935775 < baseStart_2935775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935777 : List Nat := [1, 2, 3, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_2935777 : Nat := 118140960795 + 2935777 * 2 ^ 59
def prefixEnd_2935777 : Nat := 4983230072969 + 3 ^ 40 * 2935777 * 2
def baseEnd_2935777 : Nat := 1507464695414665492686113

theorem tailTrace_2935777 : CollatzResearch.WordTrace tailWord_2935777 prefixEnd_2935777 1507464695414665492686113 := by
  unfold tailWord_2935777
  simp only [CollatzResearch.WordTrace]
  refine ⟨107076583885188794638949585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71384389256792529759299723 107076583885188794638949585)
  ·
    refine ⟨80307437913891595979212189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107076583885188794638949585 80307437913891595979212189)
    ·
      refine ⟨30115289217709348492204571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80307437913891595979212189 30115289217709348492204571)
      ·
        refine ⟨45172933826564022738306857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30115289217709348492204571 45172933826564022738306857)
        ·
          refine ⟨33879700369923017053730143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45172933826564022738306857 33879700369923017053730143)
          ·
            refine ⟨50819550554884525580595215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33879700369923017053730143 50819550554884525580595215)
            ·
              refine ⟨76229325832326788370892823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50819550554884525580595215 76229325832326788370892823)
              ·
                refine ⟨114343988748490182556339235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76229325832326788370892823 114343988748490182556339235)
                ·
                  refine ⟨171515983122735273834508853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114343988748490182556339235 171515983122735273834508853)
                  ·
                    refine ⟨16079623417756431921985205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 171515983122735273834508853 16079623417756431921985205)
                    ·
                      refine ⟨1507464695414665492686113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16079623417756431921985205 1507464695414665492686113)
                      ·
                        rfl

theorem cell23_2935777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_2935777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935777 prefixEnd_2935777 := by exact prefixLift 2935777
  have htrace : WordTrace (prefixWord ++ tailWord_2935777) baseStart_2935777 baseEnd_2935777 := by
    simpa [prefixWord, tailWord_2935777, baseEnd_2935777] using wordTrace_append hprefix tailTrace_2935777
  have hstable : (prefixWord ++ tailWord_2935777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935777).length < 2 ^ (prefixWord ++ tailWord_2935777).sum := by decide
  have hdescent : baseEnd_2935777 < baseStart_2935777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935778 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_2935778 : Nat := 118140960795 + 2935778 * 2 ^ 59
def prefixEnd_2935778 : Nat := 4983230072969 + 3 ^ 40 * 2935778 * 2
def baseEnd_2935778 : Nat := 1507465208895319988773609

theorem tailTrace_2935778 : CollatzResearch.WordTrace tailWord_2935778 prefixEnd_2935778 1507465208895319988773609 := by
  unfold tailWord_2935778
  simp only [CollatzResearch.WordTrace]
  refine ⟨26769155089546292952433997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71384413572123447873157325 26769155089546292952433997)
  ·
    refine ⟨10038433158579859857162749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26769155089546292952433997 10038433158579859857162749)
    ·
      refine ⟨3764412434467447446436031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10038433158579859857162749 3764412434467447446436031)
      ·
        refine ⟨5646618651701171169654047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3764412434467447446436031 5646618651701171169654047)
        ·
          refine ⟨8469927977551756754481071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5646618651701171169654047 8469927977551756754481071)
          ·
            refine ⟨12704891966327635131721607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8469927977551756754481071 12704891966327635131721607)
            ·
              refine ⟨19057337949491452697582411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12704891966327635131721607 19057337949491452697582411)
              ·
                refine ⟨28586006924237179046373617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19057337949491452697582411 28586006924237179046373617)
                ·
                  refine ⟨21439505193177884284780213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28586006924237179046373617 21439505193177884284780213)
                  ·
                    refine ⟨2009953611860426651698145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21439505193177884284780213 2009953611860426651698145)
                    ·
                      refine ⟨1507465208895319988773609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2009953611860426651698145 1507465208895319988773609)
                      ·
                        rfl

theorem cell23_2935778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_2935778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935778 prefixEnd_2935778 := by exact prefixLift 2935778
  have htrace : WordTrace (prefixWord ++ tailWord_2935778) baseStart_2935778 baseEnd_2935778 := by
    simpa [prefixWord, tailWord_2935778, baseEnd_2935778] using wordTrace_append hprefix tailTrace_2935778
  have hstable : (prefixWord ++ tailWord_2935778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935778).length < 2 ^ (prefixWord ++ tailWord_2935778).sum := by decide
  have hdescent : baseEnd_2935778 < baseStart_2935778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935787 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 4]
def baseStart_2935787 : Nat := 118140960795 + 2935787 * 2 ^ 59
def prefixEnd_2935787 : Nat := 4983230072969 + 3 ^ 40 * 2935787 * 2
def baseEnd_2935787 : Nat := 1507469830221210453561067

theorem tailTrace_2935787 : CollatzResearch.WordTrace tailWord_2935787 prefixEnd_2935787 1507469830221210453561067 := by
  unfold tailWord_2935787
  simp only [CollatzResearch.WordTrace]
  refine ⟨107076948615152566346813615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71384632410101710897875743 107076948615152566346813615)
  ·
    refine ⟨160615422922728849520220423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107076948615152566346813615 160615422922728849520220423)
    ·
      refine ⟨240923134384093274280330635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160615422922728849520220423 240923134384093274280330635)
      ·
        refine ⟨361384701576139911420495953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240923134384093274280330635 361384701576139911420495953)
        ·
          refine ⟨271038526182104933565371965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361384701576139911420495953 271038526182104933565371965)
          ·
            refine ⟨101639447318289350087014487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 271038526182104933565371965 101639447318289350087014487)
            ·
              refine ⟨152459170977434025130521731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101639447318289350087014487 152459170977434025130521731)
              ·
                refine ⟨228688756466151037695782597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152459170977434025130521731 228688756466151037695782597)
                ·
                  refine ⟨42879141837403319567959237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228688756466151037695782597 42879141837403319567959237)
                  ·
                    refine ⟨8039839094513122418992357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42879141837403319567959237 8039839094513122418992357)
                    ·
                      refine ⟨1507469830221210453561067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8039839094513122418992357 1507469830221210453561067)
                      ·
                        rfl

theorem cell23_2935787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 4].length) (baseStart_2935787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935787 prefixEnd_2935787 := by exact prefixLift 2935787
  have htrace : WordTrace (prefixWord ++ tailWord_2935787) baseStart_2935787 baseEnd_2935787 := by
    simpa [prefixWord, tailWord_2935787, baseEnd_2935787] using wordTrace_append hprefix tailTrace_2935787
  have hstable : (prefixWord ++ tailWord_2935787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935787).length < 2 ^ (prefixWord ++ tailWord_2935787).sum := by decide
  have hdescent : baseEnd_2935787 < baseStart_2935787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935791 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 2, 4, 2]
def baseStart_2935791 : Nat := 118140960795 + 2935791 * 2 ^ 59
def prefixEnd_2935791 : Nat := 4983230072969 + 3 ^ 40 * 2935791 * 2
def baseEnd_2935791 : Nat := 1507471884143828437911049

theorem tailTrace_2935791 : CollatzResearch.WordTrace tailWord_2935791 prefixEnd_2935791 1507471884143828437911049 := by
  unfold tailWord_2935791
  simp only [CollatzResearch.WordTrace]
  refine ⟨107077094507138075029959227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71384729671425383353306151 107077094507138075029959227)
  ·
    refine ⟨160615641760707112544938841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107077094507138075029959227 160615641760707112544938841)
    ·
      refine ⟨120461731320530334408704131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160615641760707112544938841 120461731320530334408704131)
      ·
        refine ⟨180692596980795501613056197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120461731320530334408704131 180692596980795501613056197)
        ·
          refine ⟨33879861933899156552448037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180692596980795501613056197 33879861933899156552448037)
          ·
            refine ⟨6352474112606091853584007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33879861933899156552448037 6352474112606091853584007)
            ·
              refine ⟨9528711168909137780376011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6352474112606091853584007 9528711168909137780376011)
              ·
                refine ⟨14293066753363706670564017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9528711168909137780376011 14293066753363706670564017)
                ·
                  refine ⟨10719800065022780002923013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14293066753363706670564017 10719800065022780002923013)
                  ·
                    refine ⟨2009962512191771250548065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10719800065022780002923013 2009962512191771250548065)
                    ·
                      refine ⟨1507471884143828437911049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2009962512191771250548065 1507471884143828437911049)
                      ·
                        rfl

theorem cell23_2935791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 2, 4, 2].length) (baseStart_2935791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935791 prefixEnd_2935791 := by exact prefixLift 2935791
  have htrace : WordTrace (prefixWord ++ tailWord_2935791) baseStart_2935791 baseEnd_2935791 := by
    simpa [prefixWord, tailWord_2935791, baseEnd_2935791] using wordTrace_append hprefix tailTrace_2935791
  have hstable : (prefixWord ++ tailWord_2935791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935791).length < 2 ^ (prefixWord ++ tailWord_2935791).sum := by decide
  have hdescent : baseEnd_2935791 < baseStart_2935791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935817 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 3, 2, 6]
def baseStart_2935817 : Nat := 118140960795 + 2935817 * 2 ^ 59
def prefixEnd_2935817 : Nat := 4983230072969 + 3 ^ 40 * 2935817 * 2
def baseEnd_2935817 : Nat := 1507485234640845336185929

theorem tailTrace_2935817 : CollatzResearch.WordTrace tailWord_2935817 prefixEnd_2935817 1507485234640845336185929 := by
  unfold tailWord_2935817
  simp only [CollatzResearch.WordTrace]
  refine ⟨107078042805043881470405705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71385361870029254313603803 107078042805043881470405705)
  ·
    refine ⟨80308532103782911102804279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107078042805043881470405705 80308532103782911102804279)
    ·
      refine ⟨120462798155674366654206419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80308532103782911102804279 120462798155674366654206419)
      ·
        refine ⟨180694197233511549981309629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120462798155674366654206419 180694197233511549981309629)
        ·
          refine ⟨67760323962566831242991111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180694197233511549981309629 67760323962566831242991111)
          ·
            refine ⟨101640485943850246864486667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67760323962566831242991111 101640485943850246864486667)
            ·
              refine ⟨152460728915775370296730001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101640485943850246864486667 152460728915775370296730001)
              ·
                refine ⟨114345546686831527722547501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152460728915775370296730001 114345546686831527722547501)
                ·
                  refine ⟨42879580007561822895955313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114345546686831527722547501 42879580007561822895955313)
                  ·
                    refine ⟨32159685005671367171966485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42879580007561822895955313 32159685005671367171966485)
                    ·
                      refine ⟨1507485234640845336185929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32159685005671367171966485 1507485234640845336185929)
                      ·
                        rfl

theorem cell23_2935817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_2935817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935817 prefixEnd_2935817 := by exact prefixLift 2935817
  have htrace : WordTrace (prefixWord ++ tailWord_2935817) baseStart_2935817 baseEnd_2935817 := by
    simpa [prefixWord, tailWord_2935817, baseEnd_2935817] using wordTrace_append hprefix tailTrace_2935817
  have hstable : (prefixWord ++ tailWord_2935817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935817).length < 2 ^ (prefixWord ++ tailWord_2935817).sum := by decide
  have hdescent : baseEnd_2935817 < baseStart_2935817 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935818 : List Nat := [3, 1, 2, 2, 3, 1, 1, 5, 1, 4]
def baseStart_2935818 : Nat := 118140960795 + 2935818 * 2 ^ 59
def prefixEnd_2935818 : Nat := 4983230072969 + 3 ^ 40 * 2935818 * 2
def baseEnd_2935818 : Nat := 502495249373833277424475

theorem tailTrace_2935818 : CollatzResearch.WordTrace tailWord_2935818 prefixEnd_2935818 502495249373833277424475 := by
  unfold tailWord_2935818
  simp only [CollatzResearch.WordTrace]
  refine ⟨26769519819510064660298027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71385386185360172427461405 26769519819510064660298027)
  ·
    refine ⟨40154279729265096990447041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26769519819510064660298027 40154279729265096990447041)
    ·
      refine ⟨30115709796948822742835281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40154279729265096990447041 30115709796948822742835281)
      ·
        refine ⟨22586782347711617057126461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30115709796948822742835281 22586782347711617057126461)
        ·
          refine ⟨8470043380391856396422423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22586782347711617057126461 8470043380391856396422423)
          ·
            refine ⟨12705065070587784594633635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8470043380391856396422423 12705065070587784594633635)
            ·
              refine ⟨19057597605881676891950453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12705065070587784594633635 19057597605881676891950453)
              ·
                refine ⟨1786649775551407208620355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19057597605881676891950453 1786649775551407208620355)
                ·
                  refine ⟨2679974663327110812930533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1786649775551407208620355 2679974663327110812930533)
                  ·
                    refine ⟨502495249373833277424475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2679974663327110812930533 502495249373833277424475)
                    ·
                      rfl

theorem cell23_2935818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 5, 1, 4].length) (baseStart_2935818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935818 prefixEnd_2935818 := by exact prefixLift 2935818
  have htrace : WordTrace (prefixWord ++ tailWord_2935818) baseStart_2935818 baseEnd_2935818 := by
    simpa [prefixWord, tailWord_2935818, baseEnd_2935818] using wordTrace_append hprefix tailTrace_2935818
  have hstable : (prefixWord ++ tailWord_2935818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935818).length < 2 ^ (prefixWord ++ tailWord_2935818).sum := by decide
  have hdescent : baseEnd_2935818 < baseStart_2935818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935831 : List Nat := [1, 1, 3, 5, 1, 1, 3, 2, 6]
def baseStart_2935831 : Nat := 118140960795 + 2935831 * 2 ^ 59
def prefixEnd_2935831 : Nat := 4983230072969 + 3 ^ 40 * 2935831 * 2
def baseEnd_2935831 : Nat := 167499158152223142378985

theorem tailTrace_2935831 : CollatzResearch.WordTrace tailWord_2935831 prefixEnd_2935831 167499158152223142378985 := by
  unfold tailWord_2935831
  simp only [CollatzResearch.WordTrace]
  refine ⟨107078553426993161861415347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71385702284662107907610231 107078553426993161861415347)
  ·
    refine ⟨160617830140489742792123021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107078553426993161861415347 160617830140489742792123021)
    ·
      refine ⟨60231686302683653547046133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160617830140489742792123021 60231686302683653547046133)
      ·
        refine ⟨5646720590876592520035575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60231686302683653547046133 5646720590876592520035575)
        ·
          refine ⟨8470080886314888780053363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5646720590876592520035575 8470080886314888780053363)
          ·
            refine ⟨12705121329472333170080045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8470080886314888780053363 12705121329472333170080045)
            ·
              refine ⟨4764420498552124938780017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12705121329472333170080045 4764420498552124938780017)
              ·
                refine ⟨3573315373914093704085013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4764420498552124938780017 3573315373914093704085013)
                ·
                  refine ⟨167499158152223142378985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3573315373914093704085013 167499158152223142378985)
                  ·
                    rfl

theorem cell23_2935831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 6].length) (baseStart_2935831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935831 prefixEnd_2935831 := by exact prefixLift 2935831
  have htrace : WordTrace (prefixWord ++ tailWord_2935831) baseStart_2935831 baseEnd_2935831 := by
    simpa [prefixWord, tailWord_2935831, baseEnd_2935831] using wordTrace_append hprefix tailTrace_2935831
  have hstable : (prefixWord ++ tailWord_2935831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935831).length < 2 ^ (prefixWord ++ tailWord_2935831).sum := by decide
  have hdescent : baseEnd_2935831 < baseStart_2935831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935885 : List Nat := [1, 6, 1, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_2935885 : Nat := 118140960795 + 2935885 * 2 ^ 59
def prefixEnd_2935885 : Nat := 4983230072969 + 3 ^ 40 * 2935885 * 2
def baseEnd_2935885 : Nat := 1507520151325351070135617

theorem tailTrace_2935885 : CollatzResearch.WordTrace tailWord_2935885 prefixEnd_2935885 1507520151325351070135617 := by
  unfold tailWord_2935885
  simp only [CollatzResearch.WordTrace]
  refine ⟨107080522968797529083881109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71387015312531686055920739 107080522968797529083881109)
  ·
    refine ⟨5019399514162384175806927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 107080522968797529083881109 5019399514162384175806927)
    ·
      refine ⟨7529099271243576263710391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5019399514162384175806927 7529099271243576263710391)
      ·
        refine ⟨11293648906865364395565587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7529099271243576263710391 11293648906865364395565587)
        ·
          refine ⟨16940473360298046593348381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11293648906865364395565587 16940473360298046593348381)
          ·
            refine ⟨6352677510111767472505643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16940473360298046593348381 6352677510111767472505643)
            ·
              refine ⟨9529016265167651208758465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6352677510111767472505643 9529016265167651208758465)
              ·
                refine ⟨7146762198875738406568849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9529016265167651208758465 7146762198875738406568849)
                ·
                  refine ⟨5360071649156803804926637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7146762198875738406568849 5360071649156803804926637)
                  ·
                    refine ⟨2010026868433801426847489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5360071649156803804926637 2010026868433801426847489)
                    ·
                      refine ⟨1507520151325351070135617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2010026868433801426847489 1507520151325351070135617)
                      ·
                        rfl

theorem cell23_2935885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_2935885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935885 prefixEnd_2935885 := by exact prefixLift 2935885
  have htrace : WordTrace (prefixWord ++ tailWord_2935885) baseStart_2935885 baseEnd_2935885 := by
    simpa [prefixWord, tailWord_2935885, baseEnd_2935885] using wordTrace_append hprefix tailTrace_2935885
  have hstable : (prefixWord ++ tailWord_2935885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935885).length < 2 ^ (prefixWord ++ tailWord_2935885).sum := by decide
  have hdescent : baseEnd_2935885 < baseStart_2935885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935898 : List Nat := [3, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2]
def baseStart_2935898 : Nat := 118140960795 + 2935898 * 2 ^ 59
def prefixEnd_2935898 : Nat := 4983230072969 + 3 ^ 40 * 2935898 * 2
def baseEnd_2935898 : Nat := 1507526826573859519273057

theorem tailTrace_2935898 : CollatzResearch.WordTrace tailWord_2935898 prefixEnd_2935898 1507526826573859519273057 := by
  unfold tailWord_2935898
  simp only [CollatzResearch.WordTrace]
  refine ⟨26770249279437608076026087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71387331411833621536069565 26770249279437608076026087)
  ·
    refine ⟨40155373919156412114039131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26770249279437608076026087 40155373919156412114039131)
    ·
      refine ⟨60233060878734618171058697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40155373919156412114039131 60233060878734618171058697)
      ·
        refine ⟨45174795659050963628294023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60233060878734618171058697 45174795659050963628294023)
        ·
          refine ⟨67762193488576445442441035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45174795659050963628294023 67762193488576445442441035)
          ·
            refine ⟨101643290232864668163661553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67762193488576445442441035 101643290232864668163661553)
            ·
              refine ⟨76232467674648501122746165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101643290232864668163661553 76232467674648501122746165)
              ·
                refine ⟨7146793844498296980257453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76232467674648501122746165 7146793844498296980257453)
                ·
                  refine ⟨2680047691686861367596545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7146793844498296980257453 2680047691686861367596545)
                  ·
                    refine ⟨2010035768765146025697409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2680047691686861367596545 2010035768765146025697409)
                    ·
                      refine ⟨1507526826573859519273057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2010035768765146025697409 1507526826573859519273057)
                      ·
                        rfl

theorem cell23_2935898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_2935898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935898 prefixEnd_2935898 := by exact prefixLift 2935898
  have htrace : WordTrace (prefixWord ++ tailWord_2935898) baseStart_2935898 baseEnd_2935898 := by
    simpa [prefixWord, tailWord_2935898, baseEnd_2935898] using wordTrace_append hprefix tailTrace_2935898
  have hstable : (prefixWord ++ tailWord_2935898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935898).length < 2 ^ (prefixWord ++ tailWord_2935898).sum := by decide
  have hdescent : baseEnd_2935898 < baseStart_2935898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935904 : List Nat := [2, 1, 1, 3, 2, 2, 4, 8]
def baseStart_2935904 : Nat := 118140960795 + 2935904 * 2 ^ 59
def prefixEnd_2935904 : Nat := 4983230072969 + 3 ^ 40 * 2935904 * 2
def baseEnd_2935904 : Nat := 55834441016955055399927

theorem tailTrace_2935904 : CollatzResearch.WordTrace tailWord_2935904 prefixEnd_2935904 55834441016955055399927 := by
  unfold tailWord_2935904
  simp only [CollatzResearch.WordTrace]
  refine ⟨53540607977864347664411383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71387477303819130219215177 53540607977864347664411383)
  ·
    refine ⟨80310911966796521496617075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53540607977864347664411383 80310911966796521496617075)
    ·
      refine ⟨120466367950194782244925613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80310911966796521496617075 120466367950194782244925613)
      ·
        refine ⟨45174887981323043341847105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120466367950194782244925613 45174887981323043341847105)
        ·
          refine ⟨33881165985992282506385329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45174887981323043341847105 33881165985992282506385329)
          ·
            refine ⟨25410874489494211879788997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33881165985992282506385329 25410874489494211879788997)
            ·
              refine ⟨4764538966780164727460437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25410874489494211879788997 4764538966780164727460437)
              ·
                refine ⟨55834441016955055399927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4764538966780164727460437 55834441016955055399927)
                ·
                  rfl

theorem cell23_2935904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 8].length) (baseStart_2935904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935904 prefixEnd_2935904 := by exact prefixLift 2935904
  have htrace : WordTrace (prefixWord ++ tailWord_2935904) baseStart_2935904 baseEnd_2935904 := by
    simpa [prefixWord, tailWord_2935904, baseEnd_2935904] using wordTrace_append hprefix tailTrace_2935904
  have hstable : (prefixWord ++ tailWord_2935904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935904).length < 2 ^ (prefixWord ++ tailWord_2935904).sum := by decide
  have hdescent : baseEnd_2935904 < baseStart_2935904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935912 : List Nat := [2, 1, 4, 4, 2, 1, 1, 2, 1, 5]
def baseStart_2935912 : Nat := 118140960795 + 2935912 * 2 ^ 59
def prefixEnd_2935912 : Nat := 4983230072969 + 3 ^ 40 * 2935912 * 2
def baseEnd_2935912 : Nat := 502511338434340821499331

theorem tailTrace_2935912 : CollatzResearch.WordTrace tailWord_2935912 prefixEnd_2935912 502511338434340821499331 := by
  unfold tailWord_2935912
  simp only [CollatzResearch.WordTrace]
  refine ⟨53540753869849856347556995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71387671826466475130075993 53540753869849856347556995)
  ·
    refine ⟨80311130804774784521335493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53540753869849856347556995 80311130804774784521335493)
    ·
      refine ⟨15058337025895272097750405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80311130804774784521335493 15058337025895272097750405)
      ·
        refine ⟨2823438192355363518328201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15058337025895272097750405 2823438192355363518328201)
        ·
          refine ⟨2117578644266522638746151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2823438192355363518328201 2117578644266522638746151)
          ·
            refine ⟨3176367966399783958119227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2117578644266522638746151 3176367966399783958119227)
            ·
              refine ⟨4764551949599675937178841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3176367966399783958119227 4764551949599675937178841)
              ·
                refine ⟨3573413962199756952884131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4764551949599675937178841 3573413962199756952884131)
                ·
                  refine ⟨5360120943299635429326197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3573413962199756952884131 5360120943299635429326197)
                  ·
                    refine ⟨502511338434340821499331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5360120943299635429326197 502511338434340821499331)
                    ·
                      rfl

theorem cell23_2935912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_2935912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935912 prefixEnd_2935912 := by exact prefixLift 2935912
  have htrace : WordTrace (prefixWord ++ tailWord_2935912) baseStart_2935912 baseEnd_2935912 := by
    simpa [prefixWord, tailWord_2935912, baseEnd_2935912] using wordTrace_append hprefix tailTrace_2935912
  have hstable : (prefixWord ++ tailWord_2935912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935912).length < 2 ^ (prefixWord ++ tailWord_2935912).sum := by decide
  have hdescent : baseEnd_2935912 < baseStart_2935912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935918 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_2935918 : Nat := 118140960795 + 2935918 * 2 ^ 59
def prefixEnd_2935918 : Nat := 4983230072969 + 3 ^ 40 * 2935918 * 2
def baseEnd_2935918 : Nat := 1507537096186949441022965

theorem tailTrace_2935918 : CollatzResearch.WordTrace tailWord_2935918 prefixEnd_2935918 1507537096186949441022965 := by
  unfold tailWord_2935918
  simp only [CollatzResearch.WordTrace]
  refine ⟨13385215822209746964979051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71387817718451983813221605 13385215822209746964979051)
  ·
    refine ⟨20077823733314620447468577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13385215822209746964979051 20077823733314620447468577)
    ·
      refine ⟨15058367799985965335601433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20077823733314620447468577 15058367799985965335601433)
      ·
        refine ⟨11293775849989474001701075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15058367799985965335601433 11293775849989474001701075)
        ·
          refine ⟨16940663774984211002551613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11293775849989474001701075 16940663774984211002551613)
          ·
            refine ⟨6352748915619079125956855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16940663774984211002551613 6352748915619079125956855)
            ·
              refine ⟨9529123373428618688935283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6352748915619079125956855 9529123373428618688935283)
              ·
                refine ⟨14293685060142928033402925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9529123373428618688935283 14293685060142928033402925)
                ·
                  refine ⟨5360131897553598012526097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14293685060142928033402925 5360131897553598012526097)
                  ·
                    refine ⟨4020098923165198509394573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5360131897553598012526097 4020098923165198509394573)
                    ·
                      refine ⟨1507537096186949441022965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4020098923165198509394573 1507537096186949441022965)
                      ·
                        rfl

theorem cell23_2935918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_2935918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935918 prefixEnd_2935918 := by exact prefixLift 2935918
  have htrace : WordTrace (prefixWord ++ tailWord_2935918) baseStart_2935918 baseEnd_2935918 := by
    simpa [prefixWord, tailWord_2935918, baseEnd_2935918] using wordTrace_append hprefix tailTrace_2935918
  have hstable : (prefixWord ++ tailWord_2935918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935918).length < 2 ^ (prefixWord ++ tailWord_2935918).sum := by decide
  have hdescent : baseEnd_2935918 < baseStart_2935918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935931 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 6, 1, 3]
def baseStart_2935931 : Nat := 118140960795 + 2935931 * 2 ^ 59
def prefixEnd_2935931 : Nat := 4983230072969 + 3 ^ 40 * 2935931 * 2
def baseEnd_2935931 : Nat := 1507543771435457890160405

theorem tailTrace_2935931 : CollatzResearch.WordTrace tailWord_2935931 prefixEnd_2935931 1507543771435457890160405 := by
  unfold tailWord_2935931
  simp only [CollatzResearch.WordTrace]
  refine ⟨107082200726630878940055647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71388133817753919293370431 107082200726630878940055647)
  ·
    refine ⟨160623301089946318410083471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107082200726630878940055647 160623301089946318410083471)
    ·
      refine ⟨240934951634919477615125207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160623301089946318410083471 240934951634919477615125207)
      ·
        refine ⟨361402427452379216422687811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240934951634919477615125207 361402427452379216422687811)
        ·
          refine ⟨542103641178568824634031717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361402427452379216422687811 542103641178568824634031717)
          ·
            refine ⟨101644432720981654618880947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 542103641178568824634031717 101644432720981654618880947)
            ·
              refine ⟨152466649081472481928321421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101644432720981654618880947 152466649081472481928321421)
              ·
                refine ⟨57174993405552180723120533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152466649081472481928321421 57174993405552180723120533)
                ·
                  refine ⟨2680077815885258471396275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57174993405552180723120533 2680077815885258471396275)
                  ·
                    refine ⟨4020116723827887707094413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2680077815885258471396275 4020116723827887707094413)
                    ·
                      refine ⟨1507543771435457890160405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4020116723827887707094413 1507543771435457890160405)
                      ·
                        rfl

theorem cell23_2935931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 1, 3].length) (baseStart_2935931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935931 prefixEnd_2935931 := by exact prefixLift 2935931
  have htrace : WordTrace (prefixWord ++ tailWord_2935931) baseStart_2935931 baseEnd_2935931 := by
    simpa [prefixWord, tailWord_2935931, baseEnd_2935931] using wordTrace_append hprefix tailTrace_2935931
  have hstable : (prefixWord ++ tailWord_2935931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935931).length < 2 ^ (prefixWord ++ tailWord_2935931).sum := by decide
  have hdescent : baseEnd_2935931 < baseStart_2935931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935975 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_2935975 : Nat := 118140960795 + 2935975 * 2 ^ 59
def prefixEnd_2935975 : Nat := 4983230072969 + 3 ^ 40 * 2935975 * 2
def baseEnd_2935975 : Nat := 1507566364584255718010203

theorem tailTrace_2935975 : CollatzResearch.WordTrace tailWord_2935975 prefixEnd_2935975 1507566364584255718010203 := by
  unfold tailWord_2935975
  simp only [CollatzResearch.WordTrace]
  refine ⟨107083805538471474454657379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71389203692314316303104919 107083805538471474454657379)
  ·
    refine ⟨160625708307707211681986069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107083805538471474454657379 160625708307707211681986069)
    ·
      refine ⟨7529330076923775547593097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 160625708307707211681986069 7529330076923775547593097)
      ·
        refine ⟨5646997557692831660694823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7529330076923775547593097 5646997557692831660694823)
        ·
          refine ⟨8470496336539247491042235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5646997557692831660694823 8470496336539247491042235)
          ·
            refine ⟨12705744504808871236563353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8470496336539247491042235 12705744504808871236563353)
            ·
              refine ⟨9529308378606653427422515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12705744504808871236563353 9529308378606653427422515)
              ·
                refine ⟨14293962567909980141133773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9529308378606653427422515 14293962567909980141133773)
                ·
                  refine ⟨5360235962966242552925165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14293962567909980141133773 5360235962966242552925165)
                  ·
                    refine ⟨2010088486112340957346937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5360235962966242552925165 2010088486112340957346937)
                    ·
                      refine ⟨1507566364584255718010203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2010088486112340957346937 1507566364584255718010203)
                      ·
                        rfl

theorem cell23_2935975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_2935975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935975 prefixEnd_2935975 := by exact prefixLift 2935975
  have htrace : WordTrace (prefixWord ++ tailWord_2935975) baseStart_2935975 baseEnd_2935975 := by
    simpa [prefixWord, tailWord_2935975, baseEnd_2935975] using wordTrace_append hprefix tailTrace_2935975
  have hstable : (prefixWord ++ tailWord_2935975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935975).length < 2 ^ (prefixWord ++ tailWord_2935975).sum := by decide
  have hdescent : baseEnd_2935975 < baseStart_2935975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2935994 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 11]
def baseStart_2935994 : Nat := 118140960795 + 2935994 * 2 ^ 59
def prefixEnd_2935994 : Nat := 4983230072969 + 3 ^ 40 * 2935994 * 2
def baseEnd_2935994 : Nat := 167508457857410127074735

theorem tailTrace_2935994 : CollatzResearch.WordTrace tailWord_2935994 prefixEnd_2935994 167508457857410127074735 := by
  unfold tailWord_2935994
  simp only [CollatzResearch.WordTrace]
  refine ⟨26771124631350660174899759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71389665683601760466399357 26771124631350660174899759)
  ·
    refine ⟨40156686947025990262349639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26771124631350660174899759 40156686947025990262349639)
    ·
      refine ⟨60235030420538985393524459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40156686947025990262349639 60235030420538985393524459)
      ·
        refine ⟨90352545630808478090286689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60235030420538985393524459 90352545630808478090286689)
        ·
          refine ⟨67764409223106358567715017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90352545630808478090286689 67764409223106358567715017)
          ·
            refine ⟨50823306917329768925786263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67764409223106358567715017 50823306917329768925786263)
            ·
              refine ⟨76234960375994653388679395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50823306917329768925786263 76234960375994653388679395)
              ·
                refine ⟨114352440563991980083019093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76234960375994653388679395 114352440563991980083019093)
                ·
                  refine ⟨167508457857410127074735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 114352440563991980083019093 167508457857410127074735)
                  ·
                    rfl

theorem cell23_2935994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 11].length) (baseStart_2935994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2935994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2935994 prefixEnd_2935994 := by exact prefixLift 2935994
  have htrace : WordTrace (prefixWord ++ tailWord_2935994) baseStart_2935994 baseEnd_2935994 := by
    simpa [prefixWord, tailWord_2935994, baseEnd_2935994] using wordTrace_append hprefix tailTrace_2935994
  have hstable : (prefixWord ++ tailWord_2935994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2935994).length < 2 ^ (prefixWord ++ tailWord_2935994).sum := by decide
  have hdescent : baseEnd_2935994 < baseStart_2935994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2935994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936045 : List Nat := [1, 5, 1, 2, 2, 1, 3, 3, 5]
def baseStart_2936045 : Nat := 118140960795 + 2936045 * 2 ^ 59
def prefixEnd_2936045 : Nat := 4983230072969 + 3 ^ 40 * 2936045 * 2
def baseEnd_2936045 : Nat := 167511367581118938237209

theorem tailTrace_2936045 : CollatzResearch.WordTrace tailWord_2936045 prefixEnd_2936045 167511367581118938237209 := by
  unfold tailWord_2936045
  simp only [CollatzResearch.WordTrace]
  refine ⟨107086358648217876409705589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71390905765478584273137059 107086358648217876409705589)
  ·
    refine ⟨10039346123270425913409899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107086358648217876409705589 10039346123270425913409899)
    ·
      refine ⟨15059019184905638870114849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10039346123270425913409899 15059019184905638870114849)
      ·
        refine ⟨11294264388679229152586137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15059019184905638870114849 11294264388679229152586137)
        ·
          refine ⟨8470698291509421864439603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11294264388679229152586137 8470698291509421864439603)
          ·
            refine ⟨12706047437264132796659405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8470698291509421864439603 12706047437264132796659405)
            ·
              refine ⟨4764767788974049798747277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12706047437264132796659405 4764767788974049798747277)
              ·
                refine ⟨1786787920865268674530229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4764767788974049798747277 1786787920865268674530229)
                ·
                  refine ⟨167511367581118938237209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1786787920865268674530229 167511367581118938237209)
                  ·
                    rfl

theorem cell23_2936045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_2936045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936045 prefixEnd_2936045 := by exact prefixLift 2936045
  have htrace : WordTrace (prefixWord ++ tailWord_2936045) baseStart_2936045 baseEnd_2936045 := by
    simpa [prefixWord, tailWord_2936045, baseEnd_2936045] using wordTrace_append hprefix tailTrace_2936045
  have hstable : (prefixWord ++ tailWord_2936045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936045).length < 2 ^ (prefixWord ++ tailWord_2936045).sum := by decide
  have hdescent : baseEnd_2936045 < baseStart_2936045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936062 : List Nat := [4, 2, 2, 1, 1, 3, 3, 2, 5]
def baseStart_2936062 : Nat := 118140960795 + 2936062 * 2 ^ 59
def prefixEnd_2936062 : Nat := 4983230072969 + 3 ^ 40 * 2936062 * 2
def baseEnd_2936062 : Nat := 167512337489021875291367

theorem tailTrace_2936062 : CollatzResearch.WordTrace tailWord_2936062 prefixEnd_2936062 167512337489021875291367 := by
  unfold tailWord_2936062
  simp only [CollatzResearch.WordTrace]
  refine ⟨13385872336144536039134305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71391319126104192208716293 13385872336144536039134305)
  ·
    refine ⟨10039404252108402029350729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13385872336144536039134305 10039404252108402029350729)
    ·
      refine ⟨7529553189081301522013047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10039404252108402029350729 7529553189081301522013047)
      ·
        refine ⟨11294329783621952283019571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7529553189081301522013047 11294329783621952283019571)
        ·
          refine ⟨16941494675432928424529357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11294329783621952283019571 16941494675432928424529357)
          ·
            refine ⟨6353060503287348159198509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16941494675432928424529357 6353060503287348159198509)
            ·
              refine ⟨2382397688732755559699441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6353060503287348159198509 2382397688732755559699441)
              ·
                refine ⟨1786798266549566669774581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2382397688732755559699441 1786798266549566669774581)
                ·
                  refine ⟨167512337489021875291367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1786798266549566669774581 167512337489021875291367)
                  ·
                    rfl

theorem cell23_2936062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_2936062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936062 prefixEnd_2936062 := by exact prefixLift 2936062
  have htrace : WordTrace (prefixWord ++ tailWord_2936062) baseStart_2936062 baseEnd_2936062 := by
    simpa [prefixWord, tailWord_2936062, baseEnd_2936062] using wordTrace_append hprefix tailTrace_2936062
  have hstable : (prefixWord ++ tailWord_2936062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936062).length < 2 ^ (prefixWord ++ tailWord_2936062).sum := by decide
  have hdescent : baseEnd_2936062 < baseStart_2936062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936068 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 1, 2, 5]
def baseStart_2936068 : Nat := 118140960795 + 2936068 * 2 ^ 59
def prefixEnd_2936068 : Nat := 4983230072969 + 3 ^ 40 * 2936068 * 2
def baseEnd_2936068 : Nat := 1507614118285123854147275

theorem tailTrace_2936068 : CollatzResearch.WordTrace tailWord_2936068 prefixEnd_2936068 1507614118285123854147275 := by
  unfold tailWord_2936068
  simp only [CollatzResearch.WordTrace]
  refine ⟨53543598763567275668896429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71391465018089700891861905 53543598763567275668896429)
  ·
    refine ⟨20078849536337728375836161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53543598763567275668896429 20078849536337728375836161)
    ·
      refine ⟨15059137152253296281877121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20078849536337728375836161 15059137152253296281877121)
      ·
        refine ⟨11294352864189972211407841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15059137152253296281877121 11294352864189972211407841)
        ·
          refine ⟨8470764648142479158555881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11294352864189972211407841 8470764648142479158555881)
          ·
            refine ⟨6353073486106859368916911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8470764648142479158555881 6353073486106859368916911)
            ·
              refine ⟨9529610229160289053375367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6353073486106859368916911 9529610229160289053375367)
              ·
                refine ⟨14294415343740433580063051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9529610229160289053375367 14294415343740433580063051)
                ·
                  refine ⟨21441623015610650370094577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14294415343740433580063051 21441623015610650370094577)
                  ·
                    refine ⟨16081217261707987777570933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21441623015610650370094577 16081217261707987777570933)
                    ·
                      refine ⟨1507614118285123854147275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16081217261707987777570933 1507614118285123854147275)
                      ·
                        rfl

theorem cell23_2936068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_2936068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936068 prefixEnd_2936068 := by exact prefixLift 2936068
  have htrace : WordTrace (prefixWord ++ tailWord_2936068) baseStart_2936068 baseEnd_2936068 := by
    simpa [prefixWord, tailWord_2936068, baseEnd_2936068] using wordTrace_append hprefix tailTrace_2936068
  have hstable : (prefixWord ++ tailWord_2936068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936068).length < 2 ^ (prefixWord ++ tailWord_2936068).sum := by decide
  have hdescent : baseEnd_2936068 < baseStart_2936068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936095 : List Nat := [1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 4]
def baseStart_2936095 : Nat := 118140960795 + 2936095 * 2 ^ 59
def prefixEnd_2936095 : Nat := 4983230072969 + 3 ^ 40 * 2936095 * 2
def baseEnd_2936095 : Nat := 1507627982262795248509651

theorem tailTrace_2936095 : CollatzResearch.WordTrace tailWord_2936095 prefixEnd_2936095 1507627982262795248509651 := by
  unfold tailWord_2936095
  simp only [CollatzResearch.WordTrace]
  refine ⟨107088182298036734949025739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71392121532024489966017159 107088182298036734949025739)
  ·
    refine ⟨160632273447055102423538609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107088182298036734949025739 160632273447055102423538609)
    ·
      refine ⟨120474205085291326817653957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160632273447055102423538609 120474205085291326817653957)
      ·
        refine ⟨22588913453492123778310117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120474205085291326817653957 22588913453492123778310117)
        ·
          refine ⟨4235421272529773208433147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22588913453492123778310117 4235421272529773208433147)
          ·
            refine ⟨6353131908794659812649721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4235421272529773208433147 6353131908794659812649721)
            ·
              refine ⟨4764848931595994859487291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6353131908794659812649721 4764848931595994859487291)
              ·
                refine ⟨7147273397393992289230937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4764848931595994859487291 7147273397393992289230937)
                ·
                  refine ⟨5360455048045494216923203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7147273397393992289230937 5360455048045494216923203)
                  ·
                    refine ⟨8040682572068241325384805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5360455048045494216923203 8040682572068241325384805)
                    ·
                      refine ⟨1507627982262795248509651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8040682572068241325384805 1507627982262795248509651)
                      ·
                        rfl

theorem cell23_2936095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_2936095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936095 prefixEnd_2936095 := by exact prefixLift 2936095
  have htrace : WordTrace (prefixWord ++ tailWord_2936095) baseStart_2936095 baseEnd_2936095 := by
    simpa [prefixWord, tailWord_2936095, baseEnd_2936095] using wordTrace_append hprefix tailTrace_2936095
  have hstable : (prefixWord ++ tailWord_2936095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936095).length < 2 ^ (prefixWord ++ tailWord_2936095).sum := by decide
  have hdescent : baseEnd_2936095 < baseStart_2936095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936145 : List Nat := [1, 2, 2, 1, 4, 1, 3, 2, 3, 1, 3]
def baseStart_2936145 : Nat := 118140960795 + 2936145 * 2 ^ 59
def prefixEnd_2936145 : Nat := 4983230072969 + 3 ^ 40 * 2936145 * 2
def baseEnd_2936145 : Nat := 1507653656295520052884421

theorem tailTrace_2936145 : CollatzResearch.WordTrace tailWord_2936145 prefixEnd_2936145 1507653656295520052884421 := by
  unfold tailWord_2936145
  simp only [CollatzResearch.WordTrace]
  refine ⟨107090005947855593488345889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71393337298570395658897259 107090005947855593488345889)
  ·
    refine ⟨80317504460891695116259417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107090005947855593488345889 80317504460891695116259417)
    ·
      refine ⟨60238128345668771337194563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80317504460891695116259417 60238128345668771337194563)
      ·
        refine ⟨90357192518503157005791845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60238128345668771337194563 90357192518503157005791845)
        ·
          refine ⟨16941973597219341938585971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90357192518503157005791845 16941973597219341938585971)
          ·
            refine ⟨25412960395829012907878957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16941973597219341938585971 25412960395829012907878957)
            ·
              refine ⟨9529860148435879840454609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25412960395829012907878957 9529860148435879840454609)
              ·
                refine ⟨7147395111326909880340957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9529860148435879840454609 7147395111326909880340957)
                ·
                  refine ⟨2680273166747591205127859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7147395111326909880340957 2680273166747591205127859)
                  ·
                    refine ⟨4020409750121386807691789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2680273166747591205127859 4020409750121386807691789)
                    ·
                      refine ⟨1507653656295520052884421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4020409750121386807691789 1507653656295520052884421)
                      ·
                        rfl

theorem cell23_2936145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 1, 3].length) (baseStart_2936145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936145 prefixEnd_2936145 := by exact prefixLift 2936145
  have htrace : WordTrace (prefixWord ++ tailWord_2936145) baseStart_2936145 baseEnd_2936145 := by
    simpa [prefixWord, tailWord_2936145, baseEnd_2936145] using wordTrace_append hprefix tailTrace_2936145
  have hstable : (prefixWord ++ tailWord_2936145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936145).length < 2 ^ (prefixWord ++ tailWord_2936145).sum := by decide
  have hdescent : baseEnd_2936145 < baseStart_2936145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936148 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 3, 5]
def baseStart_2936148 : Nat := 118140960795 + 2936148 * 2 ^ 59
def prefixEnd_2936148 : Nat := 4983230072969 + 3 ^ 40 * 2936148 * 2
def baseEnd_2936148 : Nat := 502551732245827847048969

theorem tailTrace_2936148 : CollatzResearch.WordTrace tailWord_2936148 prefixEnd_2936148 502551732245827847048969 := by
  unfold tailWord_2936148
  simp only [CollatzResearch.WordTrace]
  refine ⟨53545057683422362500352549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71393410244563150000470065 53545057683422362500352549)
  ·
    refine ⟨10039698315641692968816103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53545057683422362500352549 10039698315641692968816103)
    ·
      refine ⟨15059547473462539453224155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10039698315641692968816103 15059547473462539453224155)
      ·
        refine ⟨22589321210193809179836233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15059547473462539453224155 22589321210193809179836233)
        ·
          refine ⟨16941990907645356884877175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22589321210193809179836233 16941990907645356884877175)
          ·
            refine ⟨25412986361468035327315763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16941990907645356884877175 25412986361468035327315763)
            ·
              refine ⟨38119479542202052990973645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25412986361468035327315763 38119479542202052990973645)
              ·
                refine ⟨14294804828325769871615117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38119479542202052990973645 14294804828325769871615117)
                ·
                  refine ⟨5360551810622163701855669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14294804828325769871615117 5360551810622163701855669)
                  ·
                    refine ⟨502551732245827847048969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5360551810622163701855669 502551732245827847048969)
                    ·
                      rfl

theorem cell23_2936148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_2936148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936148 prefixEnd_2936148 := by exact prefixLift 2936148
  have htrace : WordTrace (prefixWord ++ tailWord_2936148) baseStart_2936148 baseEnd_2936148 := by
    simpa [prefixWord, tailWord_2936148, baseEnd_2936148] using wordTrace_append hprefix tailTrace_2936148
  have hstable : (prefixWord ++ tailWord_2936148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936148).length < 2 ^ (prefixWord ++ tailWord_2936148).sum := by decide
  have hdescent : baseEnd_2936148 < baseStart_2936148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936188 : List Nat := [2, 2, 2, 1, 1, 1, 5, 2, 1, 1, 5]
def baseStart_2936188 : Nat := 118140960795 + 2936188 * 2 ^ 59
def prefixEnd_2936188 : Nat := 4983230072969 + 3 ^ 40 * 2936188 * 2
def baseEnd_2936188 : Nat := 1507675735963663384646723

theorem tailTrace_2936188 : CollatzResearch.WordTrace tailWord_2936188 prefixEnd_2936188 1507675735963663384646723 := by
  unfold tailWord_2936188
  simp only [CollatzResearch.WordTrace]
  refine ⟨53545787143349905916080609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71394382857799874554774145 53545787143349905916080609)
  ·
    refine ⟨40159340357512429437060457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53545787143349905916080609 40159340357512429437060457)
    ·
      refine ⟨30119505268134322077795343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40159340357512429437060457 30119505268134322077795343)
      ·
        refine ⟨45179257902201483116693015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30119505268134322077795343 45179257902201483116693015)
        ·
          refine ⟨67768886853302224675039523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45179257902201483116693015 67768886853302224675039523)
          ·
            refine ⟨101653330279953337012559285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67768886853302224675039523 101653330279953337012559285)
            ·
              refine ⟨9529999713745625344927433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101653330279953337012559285 9529999713745625344927433)
              ·
                refine ⟨7147499785309219008695575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9529999713745625344927433 7147499785309219008695575)
                ·
                  refine ⟨10721249677963828513043363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7147499785309219008695575 10721249677963828513043363)
                  ·
                    refine ⟨16081874516945742769565045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10721249677963828513043363 16081874516945742769565045)
                    ·
                      refine ⟨1507675735963663384646723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16081874516945742769565045 1507675735963663384646723)
                      ·
                        rfl

theorem cell23_2936188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_2936188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936188 prefixEnd_2936188 := by exact prefixLift 2936188
  have htrace : WordTrace (prefixWord ++ tailWord_2936188) baseStart_2936188 baseEnd_2936188 := by
    simpa [prefixWord, tailWord_2936188, baseEnd_2936188] using wordTrace_append hprefix tailTrace_2936188
  have hstable : (prefixWord ++ tailWord_2936188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936188).length < 2 ^ (prefixWord ++ tailWord_2936188).sum := by decide
  have hdescent : baseEnd_2936188 < baseStart_2936188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936195 : List Nat := [1, 1, 1, 3, 5, 3, 1, 1, 1, 6]
def baseStart_2936195 : Nat := 118140960795 + 2936195 * 2 ^ 59
def prefixEnd_2936195 : Nat := 4983230072969 + 3 ^ 40 * 2936195 * 2
def baseEnd_2936195 : Nat := 502559776776081619086397

theorem tailTrace_2936195 : CollatzResearch.WordTrace tailWord_2936195 prefixEnd_2936195 502559776776081619086397 := by
  unfold tailWord_2936195
  simp only [CollatzResearch.WordTrace]
  refine ⟨107091829597674452027666039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71394553065116301351777359 107091829597674452027666039)
  ·
    refine ⟨160637744396511678041499059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107091829597674452027666039 160637744396511678041499059)
    ·
      refine ⟨240956616594767517062248589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160637744396511678041499059 240956616594767517062248589)
      ·
        refine ⟨90358731223037818898343221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240956616594767517062248589 90358731223037818898343221)
        ·
          refine ⟨8471131052159795521719677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90358731223037818898343221 8471131052159795521719677)
          ·
            refine ⟨3176674144559923320644879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8471131052159795521719677 3176674144559923320644879)
            ·
              refine ⟨4765011216839884980967319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3176674144559923320644879 4765011216839884980967319)
              ·
                refine ⟨7147516825259827471450979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4765011216839884980967319 7147516825259827471450979)
                ·
                  refine ⟨10721275237889741207176469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7147516825259827471450979 10721275237889741207176469)
                  ·
                    refine ⟨502559776776081619086397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10721275237889741207176469 502559776776081619086397)
                    ·
                      rfl

theorem cell23_2936195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 6].length) (baseStart_2936195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936195 prefixEnd_2936195 := by exact prefixLift 2936195
  have htrace : WordTrace (prefixWord ++ tailWord_2936195) baseStart_2936195 baseEnd_2936195 := by
    simpa [prefixWord, tailWord_2936195, baseEnd_2936195] using wordTrace_append hprefix tailTrace_2936195
  have hstable : (prefixWord ++ tailWord_2936195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936195).length < 2 ^ (prefixWord ++ tailWord_2936195).sum := by decide
  have hdescent : baseEnd_2936195 < baseStart_2936195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936211 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 6]
def baseStart_2936211 : Nat := 118140960795 + 2936211 * 2 ^ 59
def prefixEnd_2936211 : Nat := 4983230072969 + 3 ^ 40 * 2936211 * 2
def baseEnd_2936211 : Nat := 1507687546018716794659117

theorem tailTrace_2936211 : CollatzResearch.WordTrace tailWord_2936211 prefixEnd_2936211 1507687546018716794659117 := by
  unfold tailWord_2936211
  simp only [CollatzResearch.WordTrace]
  refine ⟨107092413165616486760248487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71394942110410991173498991 107092413165616486760248487)
  ·
    refine ⟨160638619748424730140372731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107092413165616486760248487 160638619748424730140372731)
    ·
      refine ⟨240957929622637095210559097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160638619748424730140372731 240957929622637095210559097)
      ·
        refine ⟨180718447216977821407919323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240957929622637095210559097 180718447216977821407919323)
        ·
          refine ⟨271077670825466732111878985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180718447216977821407919323 271077670825466732111878985)
          ·
            refine ⟨203308253119100049083909239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 271077670825466732111878985 203308253119100049083909239)
            ·
              refine ⟨304962379678650073625863859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203308253119100049083909239 304962379678650073625863859)
              ·
                refine ⟨457443569517975110438795789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304962379678650073625863859 457443569517975110438795789)
                ·
                  refine ⟨171541338569240666414548421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 457443569517975110438795789 171541338569240666414548421)
                  ·
                    refine ⟨32164000981732624952727829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 171541338569240666414548421 32164000981732624952727829)
                    ·
                      refine ⟨1507687546018716794659117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32164000981732624952727829 1507687546018716794659117)
                      ·
                        rfl

theorem cell23_2936211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_2936211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936211 prefixEnd_2936211 := by exact prefixLift 2936211
  have htrace : WordTrace (prefixWord ++ tailWord_2936211) baseStart_2936211 baseEnd_2936211 := by
    simpa [prefixWord, tailWord_2936211, baseEnd_2936211] using wordTrace_append hprefix tailTrace_2936211
  have hstable : (prefixWord ++ tailWord_2936211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936211).length < 2 ^ (prefixWord ++ tailWord_2936211).sum := by decide
  have hdescent : baseEnd_2936211 < baseStart_2936211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936292 : List Nat := [2, 3, 1, 1, 1, 1, 1, 5, 4, 2, 2]
def baseStart_2936292 : Nat := 118140960795 + 2936292 * 2 ^ 59
def prefixEnd_2936292 : Nat := 4983230072969 + 3 ^ 40 * 2936292 * 2
def baseEnd_2936292 : Nat := 1507729137951730977746245

theorem tailTrace_2936292 : CollatzResearch.WordTrace tailWord_2936292 prefixEnd_2936292 1507729137951730977746245 := by
  unfold tailWord_2936292
  simp only [CollatzResearch.WordTrace]
  refine ⟨53547683739161518796973565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71396911652215358395964753 53547683739161518796973565)
  ·
    refine ⟨20080381402185569548865087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53547683739161518796973565 20080381402185569548865087)
    ·
      refine ⟨30120572103278354323297631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20080381402185569548865087 30120572103278354323297631)
      ·
        refine ⟨45180858154917531484946447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30120572103278354323297631 45180858154917531484946447)
        ·
          refine ⟨67771287232376297227419671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45180858154917531484946447 67771287232376297227419671)
          ·
            refine ⟨101656930848564445841129507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67771287232376297227419671 101656930848564445841129507)
            ·
              refine ⟨152485396272846668761694261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101656930848564445841129507 152485396272846668761694261)
              ·
                refine ⟨14295505900579375196408837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152485396272846668761694261 14295505900579375196408837)
                ·
                  refine ⟨2680407356358632849326657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14295505900579375196408837 2680407356358632849326657)
                  ·
                    refine ⟨2010305517268974636994993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2680407356358632849326657 2010305517268974636994993)
                    ·
                      refine ⟨1507729137951730977746245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2010305517268974636994993 1507729137951730977746245)
                      ·
                        rfl

theorem cell23_2936292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 4, 2, 2].length) (baseStart_2936292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936292 prefixEnd_2936292 := by exact prefixLift 2936292
  have htrace : WordTrace (prefixWord ++ tailWord_2936292) baseStart_2936292 baseEnd_2936292 := by
    simpa [prefixWord, tailWord_2936292, baseEnd_2936292] using wordTrace_append hprefix tailTrace_2936292
  have hstable : (prefixWord ++ tailWord_2936292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936292).length < 2 ^ (prefixWord ++ tailWord_2936292).sum := by decide
  have hdescent : baseEnd_2936292 < baseStart_2936292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936295 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_2936295 : Nat := 118140960795 + 2936295 * 2 ^ 59
def prefixEnd_2936295 : Nat := 4983230072969 + 3 ^ 40 * 2936295 * 2
def baseEnd_2936295 : Nat := 1507730678393694466008731

theorem tailTrace_2936295 : CollatzResearch.WordTrace tailWord_2936295 prefixEnd_2936295 1507730678393694466008731 := by
  unfold tailWord_2936295
  simp only [CollatzResearch.WordTrace]
  refine ⟨107095476897312169106306339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71396984598208112737537559 107095476897312169106306339)
  ·
    refine ⟨160643215345968253659459509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107095476897312169106306339 160643215345968253659459509)
    ·
      refine ⟨15060301438684523780574329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160643215345968253659459509 15060301438684523780574329)
      ·
        refine ⟨11295226079013392835430747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15060301438684523780574329 11295226079013392835430747)
        ·
          refine ⟨16942839118520089253146121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11295226079013392835430747 16942839118520089253146121)
          ·
            refine ⟨12707129338890066939859591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16942839118520089253146121 12707129338890066939859591)
            ·
              refine ⟨19060694008335100409789387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12707129338890066939859591 19060694008335100409789387)
              ·
                refine ⟨28591041012502650614684081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19060694008335100409789387 28591041012502650614684081)
                ·
                  refine ⟨21443280759376987961013061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28591041012502650614684081 21443280759376987961013061)
                  ·
                    refine ⟨4020615142383185242689949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21443280759376987961013061 4020615142383185242689949)
                    ·
                      refine ⟨1507730678393694466008731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4020615142383185242689949 1507730678393694466008731)
                      ·
                        rfl

theorem cell23_2936295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_2936295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936295 prefixEnd_2936295 := by exact prefixLift 2936295
  have htrace : WordTrace (prefixWord ++ tailWord_2936295) baseStart_2936295 baseEnd_2936295 := by
    simpa [prefixWord, tailWord_2936295, baseEnd_2936295] using wordTrace_append hprefix tailTrace_2936295
  have hstable : (prefixWord ++ tailWord_2936295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936295).length < 2 ^ (prefixWord ++ tailWord_2936295).sum := by decide
  have hdescent : baseEnd_2936295 < baseStart_2936295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936305 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 2, 2, 4]
def baseStart_2936305 : Nat := 118140960795 + 2936305 * 2 ^ 59
def prefixEnd_2936305 : Nat := 4983230072969 + 3 ^ 40 * 2936305 * 2
def baseEnd_2936305 : Nat := 1507735813200239426883685

theorem tailTrace_2936305 : CollatzResearch.WordTrace tailWord_2936305 prefixEnd_2936305 1507735813200239426883685 := by
  unfold tailWord_2936305
  simp only [CollatzResearch.WordTrace]
  refine ⟨107095841627275940814170369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71397227751517293876113579 107095841627275940814170369)
  ·
    refine ⟨80321881220456955610627777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107095841627275940814170369 80321881220456955610627777)
    ·
      refine ⟨60241410915342716707970833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80321881220456955610627777 60241410915342716707970833)
      ·
        refine ⟨45181058186507037530978125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60241410915342716707970833 45181058186507037530978125)
        ·
          refine ⟨16942896819940139074116797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45181058186507037530978125 16942896819940139074116797)
          ·
            refine ⟨6353586307477552152793799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16942896819940139074116797 6353586307477552152793799)
            ·
              refine ⟨9530379461216328229190699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6353586307477552152793799 9530379461216328229190699)
              ·
                refine ⟨14295569191824492343786049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9530379461216328229190699 14295569191824492343786049)
                ·
                  refine ⟨10721676893868369257839537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14295569191824492343786049 10721676893868369257839537)
                  ·
                    refine ⟨8041257670401276943379653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10721676893868369257839537 8041257670401276943379653)
                    ·
                      refine ⟨1507735813200239426883685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8041257670401276943379653 1507735813200239426883685)
                      ·
                        rfl

theorem cell23_2936305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_2936305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936305 prefixEnd_2936305 := by exact prefixLift 2936305
  have htrace : WordTrace (prefixWord ++ tailWord_2936305) baseStart_2936305 baseEnd_2936305 := by
    simpa [prefixWord, tailWord_2936305, baseEnd_2936305] using wordTrace_append hprefix tailTrace_2936305
  have hstable : (prefixWord ++ tailWord_2936305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936305).length < 2 ^ (prefixWord ++ tailWord_2936305).sum := by decide
  have hdescent : baseEnd_2936305 < baseStart_2936305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936309 : List Nat := [1, 3, 5, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_2936309 : Nat := 118140960795 + 2936309 * 2 ^ 59
def prefixEnd_2936309 : Nat := 4983230072969 + 3 ^ 40 * 2936309 * 2
def baseEnd_2936309 : Nat := 1507737867122857411233667

theorem tailTrace_2936309 : CollatzResearch.WordTrace tailWord_2936309 prefixEnd_2936309 1507737867122857411233667 := by
  unfold tailWord_2936309
  simp only [CollatzResearch.WordTrace]
  refine ⟨107095987519261449497315981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71397325012840966331543987 107095987519261449497315981)
  ·
    refine ⟨40160995319723043561493493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107095987519261449497315981 40160995319723043561493493)
    ·
      refine ⟨3765093311224035333890015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 40160995319723043561493493 3765093311224035333890015)
      ·
        refine ⟨5647639966836053000835023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3765093311224035333890015 5647639966836053000835023)
        ·
          refine ⟨8471459950254079501252535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5647639966836053000835023 8471459950254079501252535)
          ·
            refine ⟨12707189925381119251878803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8471459950254079501252535 12707189925381119251878803)
            ·
              refine ⟨19060784888071678877818205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12707189925381119251878803 19060784888071678877818205)
              ·
                refine ⟨7147794333026879579181827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19060784888071678877818205 7147794333026879579181827)
                ·
                  refine ⟨10721691499540319368772741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7147794333026879579181827 10721691499540319368772741)
                  ·
                    refine ⟨2010317156163809881644889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10721691499540319368772741 2010317156163809881644889)
                    ·
                      refine ⟨1507737867122857411233667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2010317156163809881644889 1507737867122857411233667)
                      ·
                        rfl

theorem cell23_2936309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_2936309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936309 prefixEnd_2936309 := by exact prefixLift 2936309
  have htrace : WordTrace (prefixWord ++ tailWord_2936309) baseStart_2936309 baseEnd_2936309 := by
    simpa [prefixWord, tailWord_2936309, baseEnd_2936309] using wordTrace_append hprefix tailTrace_2936309
  have hstable : (prefixWord ++ tailWord_2936309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936309).length < 2 ^ (prefixWord ++ tailWord_2936309).sum := by decide
  have hdescent : baseEnd_2936309 < baseStart_2936309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936402 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_2936402 : Nat := 118140960795 + 2936402 * 2 ^ 59
def prefixEnd_2936402 : Nat := 4983230072969 + 3 ^ 40 * 2936402 * 2
def baseEnd_2936402 : Nat := 1507785620823725547370739

theorem tailTrace_2936402 : CollatzResearch.WordTrace tailWord_2936402 prefixEnd_2936402 1507785620823725547370739 := by
  unfold tailWord_2936402
  simp only [CollatzResearch.WordTrace]
  refine ⟨26774844876981131595112865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71399586338616350920300973 26774844876981131595112865)
  ·
    refine ⟨20081133657735848696334649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26774844876981131595112865 20081133657735848696334649)
    ·
      refine ⟨15060850243301886522250987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20081133657735848696334649 15060850243301886522250987)
      ·
        refine ⟨22591275364952829783376481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15060850243301886522250987 22591275364952829783376481)
        ·
          refine ⟨16943456523714622337532361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22591275364952829783376481 16943456523714622337532361)
          ·
            refine ⟨12707592392785966753149271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16943456523714622337532361 12707592392785966753149271)
            ·
              refine ⟨19061388589178950129723907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12707592392785966753149271 19061388589178950129723907)
              ·
                refine ⟨28592082883768425194585861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19061388589178950129723907 28592082883768425194585861)
                ·
                  refine ⟨5361015540706579723984849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28592082883768425194585861 5361015540706579723984849)
                  ·
                    refine ⟨4020761655529934792988637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5361015540706579723984849 4020761655529934792988637)
                    ·
                      refine ⟨1507785620823725547370739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4020761655529934792988637 1507785620823725547370739)
                      ·
                        rfl

theorem cell23_2936402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_2936402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936402 prefixEnd_2936402 := by exact prefixLift 2936402
  have htrace : WordTrace (prefixWord ++ tailWord_2936402) baseStart_2936402 baseEnd_2936402 := by
    simpa [prefixWord, tailWord_2936402, baseEnd_2936402] using wordTrace_append hprefix tailTrace_2936402
  have hstable : (prefixWord ++ tailWord_2936402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936402).length < 2 ^ (prefixWord ++ tailWord_2936402).sum := by decide
  have hdescent : baseEnd_2936402 < baseStart_2936402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936405 : List Nat := [1, 3, 2, 2, 1, 1, 1, 6, 6]
def baseStart_2936405 : Nat := 118140960795 + 2936405 * 2 ^ 59
def prefixEnd_2936405 : Nat := 4983230072969 + 3 ^ 40 * 2936405 * 2
def baseEnd_2936405 : Nat := 167531906807298781737025

theorem tailTrace_2936405 : CollatzResearch.WordTrace tailWord_2936405 prefixEnd_2936405 167531906807298781737025 := by
  unfold tailWord_2936405
  simp only [CollatzResearch.WordTrace]
  refine ⟨107099488926913657892810669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71399659284609105261873779 107099488926913657892810669)
  ·
    refine ⟨40162308347592621709804001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107099488926913657892810669 40162308347592621709804001)
    ·
      refine ⟨30121731260694466282353001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40162308347592621709804001 30121731260694466282353001)
      ·
        refine ⟨22591298445520849711764751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30121731260694466282353001 22591298445520849711764751)
        ·
          refine ⟨33886947668281274567647127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22591298445520849711764751 33886947668281274567647127)
          ·
            refine ⟨50830421502421911851470691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33886947668281274567647127 50830421502421911851470691)
            ·
              refine ⟨76245632253632867777206037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50830421502421911851470691 76245632253632867777206037)
              ·
                refine ⟨3574014011889040677056533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76245632253632867777206037 3574014011889040677056533)
                ·
                  refine ⟨167531906807298781737025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3574014011889040677056533 167531906807298781737025)
                  ·
                    rfl

theorem cell23_2936405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 6].length) (baseStart_2936405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936405 prefixEnd_2936405 := by exact prefixLift 2936405
  have htrace : WordTrace (prefixWord ++ tailWord_2936405) baseStart_2936405 baseEnd_2936405 := by
    simpa [prefixWord, tailWord_2936405, baseEnd_2936405] using wordTrace_append hprefix tailTrace_2936405
  have hstable : (prefixWord ++ tailWord_2936405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936405).length < 2 ^ (prefixWord ++ tailWord_2936405).sum := by decide
  have hdescent : baseEnd_2936405 < baseStart_2936405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936406 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_2936406 : Nat := 118140960795 + 2936406 * 2 ^ 59
def prefixEnd_2936406 : Nat := 4983230072969 + 3 ^ 40 * 2936406 * 2
def baseEnd_2936406 : Nat := 1507787674746343531720721

theorem tailTrace_2936406 : CollatzResearch.WordTrace tailWord_2936406 prefixEnd_2936406 1507787674746343531720721 := by
  unfold tailWord_2936406
  simp only [CollatzResearch.WordTrace]
  refine ⟨6693720337494377191474817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71399683599940023375731381 6693720337494377191474817)
  ·
    refine ⟨5020290253120782893606113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6693720337494377191474817 5020290253120782893606113)
    ·
      refine ⟨3765217689840587170204585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5020290253120782893606113 3765217689840587170204585)
      ·
        refine ⟨2823913267380440377653439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3765217689840587170204585 2823913267380440377653439)
        ·
          refine ⟨4235869901070660566480159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2823913267380440377653439 4235869901070660566480159)
          ·
            refine ⟨6353804851605990849720239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4235869901070660566480159 6353804851605990849720239)
            ·
              refine ⟨9530707277408986274580359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6353804851605990849720239 9530707277408986274580359)
              ·
                refine ⟨14296060916113479411870539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9530707277408986274580359 14296060916113479411870539)
                ·
                  refine ⟨21444091374170219117805809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14296060916113479411870539 21444091374170219117805809)
                  ·
                    refine ⟨16083068530627664338354357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21444091374170219117805809 16083068530627664338354357)
                    ·
                      refine ⟨1507787674746343531720721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16083068530627664338354357 1507787674746343531720721)
                      ·
                        rfl

theorem cell23_2936406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_2936406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936406 prefixEnd_2936406 := by exact prefixLift 2936406
  have htrace : WordTrace (prefixWord ++ tailWord_2936406) baseStart_2936406 baseEnd_2936406 := by
    simpa [prefixWord, tailWord_2936406, baseEnd_2936406] using wordTrace_append hprefix tailTrace_2936406
  have hstable : (prefixWord ++ tailWord_2936406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936406).length < 2 ^ (prefixWord ++ tailWord_2936406).sum := by decide
  have hdescent : baseEnd_2936406 < baseStart_2936406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936472 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 3, 1, 4]
def baseStart_2936472 : Nat := 118140960795 + 2936472 * 2 ^ 59
def prefixEnd_2936472 : Nat := 4983230072969 + 3 ^ 40 * 2936472 * 2
def baseEnd_2936472 : Nat := 1507821564469540273495417

theorem tailTrace_2936472 : CollatzResearch.WordTrace tailWord_2936472 prefixEnd_2936472 1507821564469540273495417 := by
  unfold tailWord_2936472
  simp only [CollatzResearch.WordTrace]
  refine ⟨53550966308835464167749835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71401288411780618890333113 53550966308835464167749835)
  ·
    refine ⟨80326449463253196251624753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53550966308835464167749835 80326449463253196251624753)
    ·
      refine ⟨60244837097439897188718565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80326449463253196251624753 60244837097439897188718565)
      ·
        refine ⟨11295906955769980722884731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60244837097439897188718565 11295906955769980722884731)
        ·
          refine ⟨16943860433654971084327097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11295906955769980722884731 16943860433654971084327097)
          ·
            refine ⟨12707895325241228313245323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16943860433654971084327097 12707895325241228313245323)
            ·
              refine ⟨19061842987861842469867985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12707895325241228313245323 19061842987861842469867985)
              ·
                refine ⟨14296382240896381852400989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19061842987861842469867985 14296382240896381852400989)
                ·
                  refine ⟨5361143340336143194650371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14296382240896381852400989 5361143340336143194650371)
                  ·
                    refine ⟨8041715010504214791975557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5361143340336143194650371 8041715010504214791975557)
                    ·
                      refine ⟨1507821564469540273495417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8041715010504214791975557 1507821564469540273495417)
                      ·
                        rfl

theorem cell23_2936472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_2936472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936472 prefixEnd_2936472 := by exact prefixLift 2936472
  have htrace : WordTrace (prefixWord ++ tailWord_2936472) baseStart_2936472 baseEnd_2936472 := by
    simpa [prefixWord, tailWord_2936472, baseEnd_2936472] using wordTrace_append hprefix tailTrace_2936472
  have hstable : (prefixWord ++ tailWord_2936472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936472).length < 2 ^ (prefixWord ++ tailWord_2936472).sum := by decide
  have hdescent : baseEnd_2936472 < baseStart_2936472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936485 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 1, 1, 6]
def baseStart_2936485 : Nat := 118140960795 + 2936485 * 2 ^ 59
def prefixEnd_2936485 : Nat := 4983230072969 + 3 ^ 40 * 2936485 * 2
def baseEnd_2936485 : Nat := 1507828239718048722632857

theorem tailTrace_2936485 : CollatzResearch.WordTrace tailWord_2936485 prefixEnd_2936485 1507828239718048722632857 := by
  unfold tailWord_2936485
  simp only [CollatzResearch.WordTrace]
  refine ⟨107102406766623831555722909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71401604511082554370481939 107102406766623831555722909)
  ·
    refine ⟨40163402537483936833396091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107102406766623831555722909 40163402537483936833396091)
    ·
      refine ⟨60245103806225905250094137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40163402537483936833396091 60245103806225905250094137)
      ·
        refine ⟨45183827854669428937570603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60245103806225905250094137 45183827854669428937570603)
        ·
          refine ⟨67775741782004143406355905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45183827854669428937570603 67775741782004143406355905)
          ·
            refine ⟨50831806336503107554766929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67775741782004143406355905 50831806336503107554766929)
            ·
              refine ⟨38123854752377330666075197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50831806336503107554766929 38123854752377330666075197)
              ·
                refine ⟨14296445532141498999778199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38123854752377330666075197 14296445532141498999778199)
                ·
                  refine ⟨21444668298212248499667299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14296445532141498999778199 21444668298212248499667299)
                  ·
                    refine ⟨32167002447318372749500949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21444668298212248499667299 32167002447318372749500949)
                    ·
                      refine ⟨1507828239718048722632857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32167002447318372749500949 1507828239718048722632857)
                      ·
                        rfl

theorem cell23_2936485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_2936485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936485 prefixEnd_2936485 := by exact prefixLift 2936485
  have htrace : WordTrace (prefixWord ++ tailWord_2936485) baseStart_2936485 baseEnd_2936485 := by
    simpa [prefixWord, tailWord_2936485, baseEnd_2936485] using wordTrace_append hprefix tailTrace_2936485
  have hstable : (prefixWord ++ tailWord_2936485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936485).length < 2 ^ (prefixWord ++ tailWord_2936485).sum := by decide
  have hdescent : baseEnd_2936485 < baseStart_2936485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936506 : List Nat := [3, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4]
def baseStart_2936506 : Nat := 118140960795 + 2936506 * 2 ^ 59
def prefixEnd_2936506 : Nat := 4983230072969 + 3 ^ 40 * 2936506 * 2
def baseEnd_2936506 : Nat := 1507839022811793140470261

theorem tailTrace_2936506 : CollatzResearch.WordTrace tailWord_2936506 prefixEnd_2936506 1507839022811793140470261 := by
  unfold tailWord_2936506
  simp only [CollatzResearch.WordTrace]
  refine ⟨26775793174886938035559343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71402115133031834761491581 26775793174886938035559343)
  ·
    refine ⟨40163689762330407053339015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26775793174886938035559343 40163689762330407053339015)
    ·
      refine ⟨60245534643495610580008523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40163689762330407053339015 60245534643495610580008523)
      ·
        refine ⟨90368301965243415870012785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60245534643495610580008523 90368301965243415870012785)
        ·
          refine ⟨67776226473932561902509589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90368301965243415870012785 67776226473932561902509589)
          ·
            refine ⟨3177010615965588839180137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67776226473932561902509589 3177010615965588839180137)
            ·
              refine ⟨2382757961974191629385103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3177010615965588839180137 2382757961974191629385103)
              ·
                refine ⟨3574136942961287444077655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2382757961974191629385103 3574136942961287444077655)
                ·
                  refine ⟨5361205414441931166116483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3574136942961287444077655 5361205414441931166116483)
                  ·
                    refine ⟨8041808121662896749174725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5361205414441931166116483 8041808121662896749174725)
                    ·
                      refine ⟨1507839022811793140470261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8041808121662896749174725 1507839022811793140470261)
                      ·
                        rfl

theorem cell23_2936506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4].length) (baseStart_2936506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936506 prefixEnd_2936506 := by exact prefixLift 2936506
  have htrace : WordTrace (prefixWord ++ tailWord_2936506) baseStart_2936506 baseEnd_2936506 := by
    simpa [prefixWord, tailWord_2936506, baseEnd_2936506] using wordTrace_append hprefix tailTrace_2936506
  have hstable : (prefixWord ++ tailWord_2936506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936506).length < 2 ^ (prefixWord ++ tailWord_2936506).sum := by decide
  have hdescent : baseEnd_2936506 < baseStart_2936506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936509 : List Nat := [1, 4, 1, 2, 1, 2, 3, 3, 1, 2, 3]
def baseStart_2936509 : Nat := 118140960795 + 2936509 * 2 ^ 59
def prefixEnd_2936509 : Nat := 4983230072969 + 3 ^ 40 * 2936509 * 2
def baseEnd_2936509 : Nat := 1507840563253756628732747

theorem tailTrace_2936509 : CollatzResearch.WordTrace tailWord_2936509 prefixEnd_2936509 1507840563253756628732747 := by
  unfold tailWord_2936509
  simp only [CollatzResearch.WordTrace]
  refine ⟨107103282118536883654596581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71402188079024589103064387 107103282118536883654596581)
  ·
    refine ⟨20081865397225665685236859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107103282118536883654596581 20081865397225665685236859)
    ·
      refine ⟨30122798095838498527855289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20081865397225665685236859 30122798095838498527855289)
      ·
        refine ⟨22592098571878873895891467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30122798095838498527855289 22592098571878873895891467)
        ·
          refine ⟨33888147857818310843837201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22592098571878873895891467 33888147857818310843837201)
          ·
            refine ⟨25416110893363733132877901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33888147857818310843837201 25416110893363733132877901)
            ·
              refine ⟨9531041585011399924829213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25416110893363733132877901 9531041585011399924829213)
              ·
                refine ⟨3574140594379274971810955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9531041585011399924829213 3574140594379274971810955)
                ·
                  refine ⟨5361210891568912457716433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3574140594379274971810955 5361210891568912457716433)
                  ·
                    refine ⟨4020908168676684343287325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5361210891568912457716433 4020908168676684343287325)
                    ·
                      refine ⟨1507840563253756628732747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4020908168676684343287325 1507840563253756628732747)
                      ·
                        rfl

theorem cell23_2936509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_2936509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936509 prefixEnd_2936509 := by exact prefixLift 2936509
  have htrace : WordTrace (prefixWord ++ tailWord_2936509) baseStart_2936509 baseEnd_2936509 := by
    simpa [prefixWord, tailWord_2936509, baseEnd_2936509] using wordTrace_append hprefix tailTrace_2936509
  have hstable : (prefixWord ++ tailWord_2936509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936509).length < 2 ^ (prefixWord ++ tailWord_2936509).sum := by decide
  have hdescent : baseEnd_2936509 < baseStart_2936509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936552 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_2936552 : Nat := 118140960795 + 2936552 * 2 ^ 59
def prefixEnd_2936552 : Nat := 4983230072969 + 3 ^ 40 * 2936552 * 2
def baseEnd_2936552 : Nat := 1507862642921899960495049

theorem tailTrace_2936552 : CollatzResearch.WordTrace tailWord_2936552 prefixEnd_2936552 1507862642921899960495049 := by
  unfold tailWord_2936552
  simp only [CollatzResearch.WordTrace]
  refine ⟨53552425228690550999205955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71403233638254067998941273 53552425228690550999205955)
  ·
    refine ⟨80328637843035826498808933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53552425228690550999205955 80328637843035826498808933)
    ·
      refine ⟨15061619595569217468526675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80328637843035826498808933 15061619595569217468526675)
      ·
        refine ⟨22592429393353826202790013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15061619595569217468526675 22592429393353826202790013)
        ·
          refine ⟨8472161022507684826046255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22592429393353826202790013 8472161022507684826046255)
          ·
            refine ⟨12708241533761527239069383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8472161022507684826046255 12708241533761527239069383)
            ·
              refine ⟨19062362300642290858604075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12708241533761527239069383 19062362300642290858604075)
              ·
                refine ⟨28593543450963436287906113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19062362300642290858604075 28593543450963436287906113)
                ·
                  refine ⟨21445157588222577215929585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28593543450963436287906113 21445157588222577215929585)
                  ·
                    refine ⟨16083868191166932911947189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21445157588222577215929585 16083868191166932911947189)
                    ·
                      refine ⟨1507862642921899960495049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16083868191166932911947189 1507862642921899960495049)
                      ·
                        rfl

theorem cell23_2936552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_2936552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936552 prefixEnd_2936552 := by exact prefixLift 2936552
  have htrace : WordTrace (prefixWord ++ tailWord_2936552) baseStart_2936552 baseEnd_2936552 := by
    simpa [prefixWord, tailWord_2936552, baseEnd_2936552] using wordTrace_append hprefix tailTrace_2936552
  have hstable : (prefixWord ++ tailWord_2936552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936552).length < 2 ^ (prefixWord ++ tailWord_2936552).sum := by decide
  have hdescent : baseEnd_2936552 < baseStart_2936552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936555 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 1, 8]
def baseStart_2936555 : Nat := 118140960795 + 2936555 * 2 ^ 59
def prefixEnd_2936555 : Nat := 4983230072969 + 3 ^ 40 * 2936555 * 2
def baseEnd_2936555 : Nat := 502621394454621149585845

theorem tailTrace_2936555 : CollatzResearch.WordTrace tailWord_2936555 prefixEnd_2936555 502621394454621149585845 := by
  unfold tailWord_2936555
  simp only [CollatzResearch.WordTrace]
  refine ⟨107104959876370233510771119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71403306584246822340514079 107104959876370233510771119)
  ·
    refine ⟨160657439814555350266156679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107104959876370233510771119 160657439814555350266156679)
    ·
      refine ⟨240986159721833025399235019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160657439814555350266156679 240986159721833025399235019)
      ·
        refine ⟨361479239582749538098852529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240986159721833025399235019 361479239582749538098852529)
        ·
          refine ⟨271109429687062153574139397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361479239582749538098852529 271109429687062153574139397)
          ·
            refine ⟨50833018066324153795151137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 271109429687062153574139397 50833018066324153795151137)
            ·
              refine ⟨38124763549743115346363353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50833018066324153795151137 38124763549743115346363353)
              ·
                refine ⟨28593572662307336509772515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38124763549743115346363353 28593572662307336509772515)
                ·
                  refine ⟨42890358993461004764658773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28593572662307336509772515 42890358993461004764658773)
                  ·
                    refine ⟨502621394454621149585845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 42890358993461004764658773 502621394454621149585845)
                    ·
                      rfl

theorem cell23_2936555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 8].length) (baseStart_2936555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936555 prefixEnd_2936555 := by exact prefixLift 2936555
  have htrace : WordTrace (prefixWord ++ tailWord_2936555) baseStart_2936555 baseEnd_2936555 := by
    simpa [prefixWord, tailWord_2936555, baseEnd_2936555] using wordTrace_append hprefix tailTrace_2936555
  have hstable : (prefixWord ++ tailWord_2936555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936555).length < 2 ^ (prefixWord ++ tailWord_2936555).sum := by decide
  have hdescent : baseEnd_2936555 < baseStart_2936555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936630 : List Nat := [5, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_2936630 : Nat := 118140960795 + 2936630 * 2 ^ 59
def prefixEnd_2936630 : Nat := 4983230072969 + 3 ^ 40 * 2936630 * 2
def baseEnd_2936630 : Nat := 1507902694412950655319691

theorem tailTrace_2936630 : CollatzResearch.WordTrace tailWord_2936630 prefixEnd_2936630 1507902694412950655319691 := by
  unfold tailWord_2936630
  simp only [CollatzResearch.WordTrace]
  refine ⟨6694230959443657582484459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71405130234065680879834229 6694230959443657582484459)
  ·
    refine ⟨10041346439165486373726689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6694230959443657582484459 10041346439165486373726689)
    ·
      refine ⟨7531009829374114780295017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10041346439165486373726689 7531009829374114780295017)
      ·
        refine ⟨5648257372030586085221263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7531009829374114780295017 5648257372030586085221263)
        ·
          refine ⟨8472386058045879127831895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5648257372030586085221263 8472386058045879127831895)
          ·
            refine ⟨12708579087068818691747843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8472386058045879127831895 12708579087068818691747843)
            ·
              refine ⟨19062868630603228037621765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12708579087068818691747843 19062868630603228037621765)
              ·
                refine ⟨3574287868238105257054081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19062868630603228037621765 3574287868238105257054081)
                ·
                  refine ⟨2680715901178578942790561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3574287868238105257054081 2680715901178578942790561)
                  ·
                    refine ⟨2010536925883934207092921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2680715901178578942790561 2010536925883934207092921)
                    ·
                      refine ⟨1507902694412950655319691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2010536925883934207092921 1507902694412950655319691)
                      ·
                        rfl

theorem cell23_2936630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_2936630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936630 prefixEnd_2936630 := by exact prefixLift 2936630
  have htrace : WordTrace (prefixWord ++ tailWord_2936630) baseStart_2936630 baseEnd_2936630 := by
    simpa [prefixWord, tailWord_2936630, baseEnd_2936630] using wordTrace_append hprefix tailTrace_2936630
  have hstable : (prefixWord ++ tailWord_2936630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936630).length < 2 ^ (prefixWord ++ tailWord_2936630).sum := by decide
  have hdescent : baseEnd_2936630 < baseStart_2936630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936636 : List Nat := [2, 2, 2, 2, 1, 1, 6, 2, 5]
def baseStart_2936636 : Nat := 118140960795 + 2936636 * 2 ^ 59
def prefixEnd_2936636 : Nat := 4983230072969 + 3 ^ 40 * 2936636 * 2
def baseEnd_2936636 : Nat := 167545086144097514649407

theorem tailTrace_2936636 : CollatzResearch.WordTrace tailWord_2936636 prefixEnd_2936636 167545086144097514649407 := by
  unfold tailWord_2936636
  simp only [CollatzResearch.WordTrace]
  refine ⟨53553957094538392172234881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71405276126051189562979841 53553957094538392172234881)
  ·
    refine ⟨40165467820903794129176161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53553957094538392172234881 40165467820903794129176161)
    ·
      refine ⟨30124100865677845596882121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40165467820903794129176161 30124100865677845596882121)
      ·
        refine ⟨22593075649258384197661591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30124100865677845596882121 22593075649258384197661591)
        ·
          refine ⟨33889613473887576296492387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22593075649258384197661591 33889613473887576296492387)
          ·
            refine ⟨50834420210831364444738581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33889613473887576296492387 50834420210831364444738581)
            ·
              refine ⟨2382863447382720208347121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50834420210831364444738581 2382863447382720208347121)
              ·
                refine ⟨1787147585537040156260341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2382863447382720208347121 1787147585537040156260341)
                ·
                  refine ⟨167545086144097514649407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1787147585537040156260341 167545086144097514649407)
                  ·
                    rfl

theorem cell23_2936636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 2, 5].length) (baseStart_2936636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936636 prefixEnd_2936636 := by exact prefixLift 2936636
  have htrace : WordTrace (prefixWord ++ tailWord_2936636) baseStart_2936636 baseEnd_2936636 := by
    simpa [prefixWord, tailWord_2936636, baseEnd_2936636] using wordTrace_append hprefix tailTrace_2936636
  have hstable : (prefixWord ++ tailWord_2936636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936636).length < 2 ^ (prefixWord ++ tailWord_2936636).sum := by decide
  have hdescent : baseEnd_2936636 < baseStart_2936636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936679 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 5, 4]
def baseStart_2936679 : Nat := 118140960795 + 2936679 * 2 ^ 59
def prefixEnd_2936679 : Nat := 4983230072969 + 3 ^ 40 * 2936679 * 2
def baseEnd_2936679 : Nat := 502642618321673654535655

theorem tailTrace_2936679 : CollatzResearch.WordTrace tailWord_2936679 prefixEnd_2936679 502642618321673654535655 := by
  unfold tailWord_2936679
  simp only [CollatzResearch.WordTrace]
  refine ⟨107109482527921002688285091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71406321685280668458856727 107109482527921002688285091)
  ·
    refine ⟨160664223791881504032427637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107109482527921002688285091 160664223791881504032427637)
    ·
      refine ⟨15062270980488891003040091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160664223791881504032427637 15062270980488891003040091)
      ·
        refine ⟨22593406470733336504560137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15062270980488891003040091 22593406470733336504560137)
        ·
          refine ⟨16945054853050002378420103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22593406470733336504560137 16945054853050002378420103)
          ·
            refine ⟨25417582279575003567630155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16945054853050002378420103 25417582279575003567630155)
            ·
              refine ⟨38126373419362505351445233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25417582279575003567630155 38126373419362505351445233)
              ·
                refine ⟨28594780064521879013583925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38126373419362505351445233 28594780064521879013583925)
                ·
                  refine ⟨2680760631048926157523493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28594780064521879013583925 2680760631048926157523493)
                  ·
                    refine ⟨502642618321673654535655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2680760631048926157523493 502642618321673654535655)
                    ·
                      rfl

theorem cell23_2936679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_2936679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936679 prefixEnd_2936679 := by exact prefixLift 2936679
  have htrace : WordTrace (prefixWord ++ tailWord_2936679) baseStart_2936679 baseEnd_2936679 := by
    simpa [prefixWord, tailWord_2936679, baseEnd_2936679] using wordTrace_append hprefix tailTrace_2936679
  have hstable : (prefixWord ++ tailWord_2936679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936679).length < 2 ^ (prefixWord ++ tailWord_2936679).sum := by decide
  have hdescent : baseEnd_2936679 < baseStart_2936679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936689 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 4, 2, 3]
def baseStart_2936689 : Nat := 118140960795 + 2936689 * 2 ^ 59
def prefixEnd_2936689 : Nat := 4983230072969 + 3 ^ 40 * 2936689 * 2
def baseEnd_2936689 : Nat := 1507932989771565924481919

theorem tailTrace_2936689 : CollatzResearch.WordTrace tailWord_2936689 prefixEnd_2936689 1507932989771565924481919 := by
  unfold tailWord_2936689
  simp only [CollatzResearch.WordTrace]
  refine ⟨107109847257884774396149121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71406564838589849597432747 107109847257884774396149121)
  ·
    refine ⟨80332385443413580797111841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107109847257884774396149121 80332385443413580797111841)
    ·
      refine ⟨60249289082560185597833881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80332385443413580797111841 60249289082560185597833881)
      ·
        refine ⟨45186966811920139198375411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60249289082560185597833881 45186966811920139198375411)
        ·
          refine ⟨67780450217880208797563117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45186966811920139198375411 67780450217880208797563117)
          ·
            refine ⟨25417668831705078299086169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67780450217880208797563117 25417668831705078299086169)
            ·
              refine ⟨19063251623778808724314627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25417668831705078299086169 19063251623778808724314627)
              ·
                refine ⟨28594877435668213086471941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19063251623778808724314627 28594877435668213086471941)
                ·
                  refine ⟨5361539519187789953713489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28594877435668213086471941 5361539519187789953713489)
                  ·
                    refine ⟨4021154639390842465285117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5361539519187789953713489 4021154639390842465285117)
                    ·
                      refine ⟨1507932989771565924481919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4021154639390842465285117 1507932989771565924481919)
                      ·
                        rfl

theorem cell23_2936689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_2936689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936689 prefixEnd_2936689 := by exact prefixLift 2936689
  have htrace : WordTrace (prefixWord ++ tailWord_2936689) baseStart_2936689 baseEnd_2936689 := by
    simpa [prefixWord, tailWord_2936689, baseEnd_2936689] using wordTrace_append hprefix tailTrace_2936689
  have hstable : (prefixWord ++ tailWord_2936689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936689).length < 2 ^ (prefixWord ++ tailWord_2936689).sum := by decide
  have hdescent : baseEnd_2936689 < baseStart_2936689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936730 : List Nat := [3, 1, 1, 4, 2, 3, 1, 3, 1, 4]
def baseStart_2936730 : Nat := 118140960795 + 2936730 * 2 ^ 59
def prefixEnd_2936730 : Nat := 4983230072969 + 3 ^ 40 * 2936730 * 2
def baseEnd_2936730 : Nat := 502651347492800088023077

theorem tailTrace_2936730 : CollatzResearch.WordTrace tailWord_2936730 prefixEnd_2936730 502651347492800088023077 := by
  unfold tailWord_2936730
  simp only [CollatzResearch.WordTrace]
  refine ⟨26777835662684059599597911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71407561767157492265594429 26777835662684059599597911)
  ·
    refine ⟨40166753494026089399396867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26777835662684059599597911 40166753494026089399396867)
    ·
      refine ⟨60250130241039134099095301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40166753494026089399396867 60250130241039134099095301)
      ·
        refine ⟨11296899420194837643580369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60250130241039134099095301 11296899420194837643580369)
        ·
          refine ⟨8472674565146128232685277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11296899420194837643580369 8472674565146128232685277)
          ·
            refine ⟨3177252961929798087256979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8472674565146128232685277 3177252961929798087256979)
            ·
              refine ⟨4765879442894697130885469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3177252961929798087256979 4765879442894697130885469)
              ·
                refine ⟨1787204791085511424082051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4765879442894697130885469 1787204791085511424082051)
                ·
                  refine ⟨2680807186628267136123077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1787204791085511424082051 2680807186628267136123077)
                  ·
                    refine ⟨502651347492800088023077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2680807186628267136123077 502651347492800088023077)
                    ·
                      rfl

theorem cell23_2936730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 1, 4].length) (baseStart_2936730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936730 prefixEnd_2936730 := by exact prefixLift 2936730
  have htrace : WordTrace (prefixWord ++ tailWord_2936730) baseStart_2936730 baseEnd_2936730 := by
    simpa [prefixWord, tailWord_2936730, baseEnd_2936730] using wordTrace_append hprefix tailTrace_2936730
  have hstable : (prefixWord ++ tailWord_2936730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936730).length < 2 ^ (prefixWord ++ tailWord_2936730).sum := by decide
  have hdescent : baseEnd_2936730 < baseStart_2936730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936753 : List Nat := [1, 2, 2, 4, 2, 1, 3, 1, 3, 1, 3]
def baseStart_2936753 : Nat := 118140960795 + 2936753 * 2 ^ 59
def prefixEnd_2936753 : Nat := 4983230072969 + 3 ^ 40 * 2936753 * 2
def baseEnd_2936753 : Nat := 1507965852533453674081625

theorem tailTrace_2936753 : CollatzResearch.WordTrace tailWord_2936753 prefixEnd_2936753 1507965852533453674081625 := by
  unfold tailWord_2936753
  simp only [CollatzResearch.WordTrace]
  refine ⟨107112181529652913326478913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71408121019768608884319275 107112181529652913326478913)
  ·
    refine ⟨80334136147239684994859185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107112181529652913326478913 80334136147239684994859185)
    ·
      refine ⟨60250602110429763746144389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80334136147239684994859185 60250602110429763746144389)
      ·
        refine ⟨11296987895705580702402073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60250602110429763746144389 11296987895705580702402073)
        ·
          refine ⟨8472740921779185526801555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11296987895705580702402073 8472740921779185526801555)
          ·
            refine ⟨12709111382668778290202333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8472740921779185526801555 12709111382668778290202333)
            ·
              refine ⟨4765916768500791858825875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12709111382668778290202333 4765916768500791858825875)
              ·
                refine ⟨7148875152751187788238813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4765916768500791858825875 7148875152751187788238813)
                ·
                  refine ⟨2680828182281695420589555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7148875152751187788238813 2680828182281695420589555)
                  ·
                    refine ⟨4021242273422543130884333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2680828182281695420589555 4021242273422543130884333)
                    ·
                      refine ⟨1507965852533453674081625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4021242273422543130884333 1507965852533453674081625)
                      ·
                        rfl

theorem cell23_2936753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_2936753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936753 prefixEnd_2936753 := by exact prefixLift 2936753
  have htrace : WordTrace (prefixWord ++ tailWord_2936753) baseStart_2936753 baseEnd_2936753 := by
    simpa [prefixWord, tailWord_2936753, baseEnd_2936753] using wordTrace_append hprefix tailTrace_2936753
  have hstable : (prefixWord ++ tailWord_2936753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936753).length < 2 ^ (prefixWord ++ tailWord_2936753).sum := by decide
  have hdescent : baseEnd_2936753 < baseStart_2936753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936759 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 4]
def baseStart_2936759 : Nat := 118140960795 + 2936759 * 2 ^ 59
def prefixEnd_2936759 : Nat := 4983230072969 + 3 ^ 40 * 2936759 * 2
def baseEnd_2936759 : Nat := 1507968933417380650606597

theorem tailTrace_2936759 : CollatzResearch.WordTrace tailWord_2936759 prefixEnd_2936759 1507968933417380650606597 := by
  unfold tailWord_2936759
  simp only [CollatzResearch.WordTrace]
  refine ⟨107112400367631176351197331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71408266911754117567464887 107112400367631176351197331)
  ·
    refine ⟨160668600551446764526795997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107112400367631176351197331 160668600551446764526795997)
    ·
      refine ⟨60250725206792536697548499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160668600551446764526795997 60250725206792536697548499)
      ·
        refine ⟨90376087810188805046322749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60250725206792536697548499 90376087810188805046322749)
        ·
          refine ⟨33891032928820801892371031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90376087810188805046322749 33891032928820801892371031)
          ·
            refine ⟨50836549393231202838556547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33891032928820801892371031 50836549393231202838556547)
            ·
              refine ⟨76254824089846804257834821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50836549393231202838556547 76254824089846804257834821)
              ·
                refine ⟨14297779516846275798344029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76254824089846804257834821 14297779516846275798344029)
                ·
                  refine ⟨5361667318817353424379011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14297779516846275798344029 5361667318817353424379011)
                  ·
                    refine ⟨8042500978226030136568517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5361667318817353424379011 8042500978226030136568517)
                    ·
                      refine ⟨1507968933417380650606597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8042500978226030136568517 1507968933417380650606597)
                      ·
                        rfl

theorem cell23_2936759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_2936759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936759 prefixEnd_2936759 := by exact prefixLift 2936759
  have htrace : WordTrace (prefixWord ++ tailWord_2936759) baseStart_2936759 baseEnd_2936759 := by
    simpa [prefixWord, tailWord_2936759, baseEnd_2936759] using wordTrace_append hprefix tailTrace_2936759
  have hstable : (prefixWord ++ tailWord_2936759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936759).length < 2 ^ (prefixWord ++ tailWord_2936759).sum := by decide
  have hdescent : baseEnd_2936759 < baseStart_2936759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936776 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 3, 1, 4]
def baseStart_2936776 : Nat := 118140960795 + 2936776 * 2 ^ 59
def prefixEnd_2936776 : Nat := 4983230072969 + 3 ^ 40 * 2936776 * 2
def baseEnd_2936776 : Nat := 1507977662588507084094019

theorem tailTrace_2936776 : CollatzResearch.WordTrace tailWord_2936776 prefixEnd_2936776 1507977662588507084094019 := by
  unfold tailWord_2936776
  simp only [CollatzResearch.WordTrace]
  refine ⟨53556510204284794127283091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71408680272379725503044121 53556510204284794127283091)
  ·
    refine ⟨80334765306427191190924637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53556510204284794127283091 80334765306427191190924637)
    ·
      refine ⟨30125536989910196696596739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80334765306427191190924637 30125536989910196696596739)
      ·
        refine ⟨45188305484865295044895109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30125536989910196696596739 45188305484865295044895109)
        ·
          refine ⟨8472807278412242820917833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45188305484865295044895109 8472807278412242820917833)
          ·
            refine ⟨6354605458809182115688375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8472807278412242820917833 6354605458809182115688375)
            ·
              refine ⟨9531908188213773173532563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6354605458809182115688375 9531908188213773173532563)
              ·
                refine ⟨14297862282320659760298845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9531908188213773173532563 14297862282320659760298845)
                ·
                  refine ⟨5361698355870247410112067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14297862282320659760298845 5361698355870247410112067)
                  ·
                    refine ⟨8042547533805371115168101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5361698355870247410112067 8042547533805371115168101)
                    ·
                      refine ⟨1507977662588507084094019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8042547533805371115168101 1507977662588507084094019)
                      ·
                        rfl

theorem cell23_2936776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_2936776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936776 prefixEnd_2936776 := by exact prefixLift 2936776
  have htrace : WordTrace (prefixWord ++ tailWord_2936776) baseStart_2936776 baseEnd_2936776 := by
    simpa [prefixWord, tailWord_2936776, baseEnd_2936776] using wordTrace_append hprefix tailTrace_2936776
  have hstable : (prefixWord ++ tailWord_2936776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936776).length < 2 ^ (prefixWord ++ tailWord_2936776).sum := by decide
  have hdescent : baseEnd_2936776 < baseStart_2936776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936803 : List Nat := [1, 1, 1, 6, 1, 3, 2, 2, 2, 4]
def baseStart_2936803 : Nat := 118140960795 + 2936803 * 2 ^ 59
def prefixEnd_2936803 : Nat := 4983230072969 + 3 ^ 40 * 2936803 * 2
def baseEnd_2936803 : Nat := 502663842188726159485465

theorem tailTrace_2936803 : CollatzResearch.WordTrace tailWord_2936803 prefixEnd_2936803 502663842188726159485465 := by
  unfold tailWord_2936803
  simp only [CollatzResearch.WordTrace]
  refine ⟨107114005179471771865799063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71409336786314514577199375 107114005179471771865799063)
  ·
    refine ⟨160671007769207657798698595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107114005179471771865799063 160671007769207657798698595)
    ·
      refine ⟨241006511653811486698047893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160671007769207657798698595 241006511653811486698047893)
      ·
        refine ⟨11297180233772413438970995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 241006511653811486698047893 11297180233772413438970995)
        ·
          refine ⟨16945770350658620158456493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11297180233772413438970995 16945770350658620158456493)
          ·
            refine ⟨6354663881496982559421185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16945770350658620158456493 6354663881496982559421185)
            ·
              refine ⟨4765997911122736919565889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6354663881496982559421185 4765997911122736919565889)
              ·
                refine ⟨3574498433342052689674417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4765997911122736919565889 3574498433342052689674417)
                ·
                  refine ⟨2680873825006539517255813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3574498433342052689674417 2680873825006539517255813)
                  ·
                    refine ⟨502663842188726159485465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2680873825006539517255813 502663842188726159485465)
                    ·
                      rfl

theorem cell23_2936803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 4].length) (baseStart_2936803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936803 prefixEnd_2936803 := by exact prefixLift 2936803
  have htrace : WordTrace (prefixWord ++ tailWord_2936803) baseStart_2936803 baseEnd_2936803 := by
    simpa [prefixWord, tailWord_2936803, baseEnd_2936803] using wordTrace_append hprefix tailTrace_2936803
  have hstable : (prefixWord ++ tailWord_2936803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936803).length < 2 ^ (prefixWord ++ tailWord_2936803).sum := by decide
  have hdescent : baseEnd_2936803 < baseStart_2936803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936826 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3]
def baseStart_2936826 : Nat := 118140960795 + 2936826 * 2 ^ 59
def prefixEnd_2936826 : Nat := 4983230072969 + 3 ^ 40 * 2936826 * 2
def baseEnd_2936826 : Nat := 1508003336621231888468789

theorem tailTrace_2936826 : CollatzResearch.WordTrace tailWord_2936826 prefixEnd_2936826 1508003336621231888468789 := by
  unfold tailWord_2936826
  simp only [CollatzResearch.WordTrace]
  refine ⟨26778711014597111698471583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71409896038925631195924221 26778711014597111698471583)
  ·
    refine ⟨40168066521895667547707375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26778711014597111698471583 40168066521895667547707375)
    ·
      refine ⟨60252099782843501321561063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40168066521895667547707375 60252099782843501321561063)
      ·
        refine ⟨90378149674265251982341595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60252099782843501321561063 90378149674265251982341595)
        ·
          refine ⟨135567224511397877973512393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90378149674265251982341595 135567224511397877973512393)
          ·
            refine ⟨101675418383548408480134295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135567224511397877973512393 101675418383548408480134295)
            ·
              refine ⟨152513127575322612720201443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101675418383548408480134295 152513127575322612720201443)
              ·
                refine ⟨228769691362983919080302165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152513127575322612720201443 228769691362983919080302165)
                ·
                  refine ⟨2680894820659967801722291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 228769691362983919080302165 2680894820659967801722291)
                  ·
                    refine ⟨4021342230989951702583437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2680894820659967801722291 4021342230989951702583437)
                    ·
                      refine ⟨1508003336621231888468789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4021342230989951702583437 1508003336621231888468789)
                      ·
                        rfl

theorem cell23_2936826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3].length) (baseStart_2936826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936826 prefixEnd_2936826 := by exact prefixLift 2936826
  have htrace : WordTrace (prefixWord ++ tailWord_2936826) baseStart_2936826 baseEnd_2936826 := by
    simpa [prefixWord, tailWord_2936826, baseEnd_2936826] using wordTrace_append hprefix tailTrace_2936826
  have hstable : (prefixWord ++ tailWord_2936826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936826).length < 2 ^ (prefixWord ++ tailWord_2936826).sum := by decide
  have hdescent : baseEnd_2936826 < baseStart_2936826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936838 : List Nat := [6, 2, 1, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_2936838 : Nat := 118140960795 + 2936838 * 2 ^ 59
def prefixEnd_2936838 : Nat := 4983230072969 + 3 ^ 40 * 2936838 * 2
def baseEnd_2936838 : Nat := 1508009498389085841518735

theorem tailTrace_2936838 : CollatzResearch.WordTrace tailWord_2936838 prefixEnd_2936838 1508009498389085841518735 := by
  unfold tailWord_2936838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3347352554198280401353849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71410187822896648562215445 3347352554198280401353849)
  ·
    refine ⟨2510514415648710301015387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3347352554198280401353849 2510514415648710301015387)
    ·
      refine ⟨3765771623473065451523081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2510514415648710301015387 3765771623473065451523081)
      ·
        refine ⟨2824328717604799088642311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3765771623473065451523081 2824328717604799088642311)
        ·
          refine ⟨4236493076407198632963467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2824328717604799088642311 4236493076407198632963467)
          ·
            refine ⟨6354739614610797949445201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4236493076407198632963467 6354739614610797949445201)
            ·
              refine ⟨4766054710958098462083901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6354739614610797949445201 4766054710958098462083901)
              ·
                refine ⟨1787270516609286923281463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4766054710958098462083901 1787270516609286923281463)
                ·
                  refine ⟨2680905774913930384922195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1787270516609286923281463 2680905774913930384922195)
                  ·
                    refine ⟨4021358662370895577383293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2680905774913930384922195 4021358662370895577383293)
                    ·
                      refine ⟨1508009498389085841518735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4021358662370895577383293 1508009498389085841518735)
                      ·
                        rfl

theorem cell23_2936838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_2936838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936838 prefixEnd_2936838 := by exact prefixLift 2936838
  have htrace : WordTrace (prefixWord ++ tailWord_2936838) baseStart_2936838 baseEnd_2936838 := by
    simpa [prefixWord, tailWord_2936838, baseEnd_2936838] using wordTrace_append hprefix tailTrace_2936838
  have hstable : (prefixWord ++ tailWord_2936838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936838).length < 2 ^ (prefixWord ++ tailWord_2936838).sum := by decide
  have hdescent : baseEnd_2936838 < baseStart_2936838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936860 : List Nat := [2, 2, 3, 1, 3, 1, 3, 2, 2, 1, 3]
def baseStart_2936860 : Nat := 118140960795 + 2936860 * 2 ^ 59
def prefixEnd_2936860 : Nat := 4983230072969 + 3 ^ 40 * 2936860 * 2
def baseEnd_2936860 : Nat := 1508020794963484755443633

theorem tailTrace_2936860 : CollatzResearch.WordTrace tailWord_2936860 prefixEnd_2936860 1508020794963484755443633 := by
  unfold tailWord_2936860
  simp only [CollatzResearch.WordTrace]
  refine ⟨53558042070132635300312017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71410722760176847067082689 53558042070132635300312017)
  ·
    refine ⟨40168531552599476475234013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53558042070132635300312017 40168531552599476475234013)
    ·
      refine ⟨15063199332224803678212755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40168531552599476475234013 15063199332224803678212755)
      ·
        refine ⟨22594798998337205517319133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15063199332224803678212755 22594798998337205517319133)
        ·
          refine ⟨8473049624376452068994675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22594798998337205517319133 8473049624376452068994675)
          ·
            refine ⟨12709574436564678103492013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8473049624376452068994675 12709574436564678103492013)
            ·
              refine ⟨4766090413711754288809505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12709574436564678103492013 4766090413711754288809505)
              ·
                refine ⟨3574567810283815716607129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4766090413711754288809505 3574567810283815716607129)
                ·
                  refine ⟨2680925857712861787455347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3574567810283815716607129 2680925857712861787455347)
                  ·
                    refine ⟨4021388786569292681183021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2680925857712861787455347 4021388786569292681183021)
                    ·
                      refine ⟨1508020794963484755443633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4021388786569292681183021 1508020794963484755443633)
                      ·
                        rfl

theorem cell23_2936860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_2936860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936860 prefixEnd_2936860 := by exact prefixLift 2936860
  have htrace : WordTrace (prefixWord ++ tailWord_2936860) baseStart_2936860 baseEnd_2936860 := by
    simpa [prefixWord, tailWord_2936860, baseEnd_2936860] using wordTrace_append hprefix tailTrace_2936860
  have hstable : (prefixWord ++ tailWord_2936860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936860).length < 2 ^ (prefixWord ++ tailWord_2936860).sum := by decide
  have hdescent : baseEnd_2936860 < baseStart_2936860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936879 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 4]
def baseStart_2936879 : Nat := 118140960795 + 2936879 * 2 ^ 59
def prefixEnd_2936879 : Nat := 4983230072969 + 3 ^ 40 * 2936879 * 2
def baseEnd_2936879 : Nat := 1508030551095920181106045

theorem tailTrace_2936879 : CollatzResearch.WordTrace tailWord_2936879 prefixEnd_2936879 1508030551095920181106045 := by
  unfold tailWord_2936879
  simp only [CollatzResearch.WordTrace]
  refine ⟨107116777127196436845565691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71411184751464291230377127 107116777127196436845565691)
  ·
    refine ⟨160675165690794655268348537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107116777127196436845565691 160675165690794655268348537)
    ·
      refine ⟨120506374268095991451261403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160675165690794655268348537 120506374268095991451261403)
      ·
        refine ⟨180759561402143987176892105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120506374268095991451261403 180759561402143987176892105)
        ·
          refine ⟨135569671051607990382669079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180759561402143987176892105 135569671051607990382669079)
          ·
            refine ⟨203354506577411985574003619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135569671051607990382669079 203354506577411985574003619)
            ·
              refine ⟨305031759866117978361005429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203354506577411985574003619 305031759866117978361005429)
              ·
                refine ⟨28596727487448560471344259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 305031759866117978361005429 28596727487448560471344259)
                ·
                  refine ⟨42895091231172840707016389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28596727487448560471344259 42895091231172840707016389)
                  ·
                    refine ⟨8042829605844907632565573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42895091231172840707016389 8042829605844907632565573)
                    ·
                      refine ⟨1508030551095920181106045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8042829605844907632565573 1508030551095920181106045)
                      ·
                        rfl

theorem cell23_2936879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 4].length) (baseStart_2936879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936879 prefixEnd_2936879 := by exact prefixLift 2936879
  have htrace : WordTrace (prefixWord ++ tailWord_2936879) baseStart_2936879 baseEnd_2936879 := by
    simpa [prefixWord, tailWord_2936879, baseEnd_2936879] using wordTrace_append hprefix tailTrace_2936879
  have hstable : (prefixWord ++ tailWord_2936879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936879).length < 2 ^ (prefixWord ++ tailWord_2936879).sum := by decide
  have hdescent : baseEnd_2936879 < baseStart_2936879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936883 : List Nat := [1, 1, 1, 2, 4, 1, 5, 1, 1, 4, 2]
def baseStart_2936883 : Nat := 118140960795 + 2936883 * 2 ^ 59
def prefixEnd_2936883 : Nat := 4983230072969 + 3 ^ 40 * 2936883 * 2
def baseEnd_2936883 : Nat := 1508032605018538165456027

theorem tailTrace_2936883 : CollatzResearch.WordTrace tailWord_2936883 prefixEnd_2936883 1508032605018538165456027 := by
  unfold tailWord_2936883
  simp only [CollatzResearch.WordTrace]
  refine ⟨107116923019181945528711303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71411282012787963685807535 107116923019181945528711303)
  ·
    refine ⟨160675384528772918293066955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107116923019181945528711303 160675384528772918293066955)
    ·
      refine ⟨241013076793159377439600433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160675384528772918293066955 241013076793159377439600433)
      ·
        refine ⟨180759807594869533079700325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241013076793159377439600433 180759807594869533079700325)
        ·
          refine ⟨33892463924038037452443811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180759807594869533079700325 33892463924038037452443811)
          ·
            refine ⟨50838695886057056178665717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33892463924038037452443811 50838695886057056178665717)
            ·
              refine ⟨4766127739317849016749911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50838695886057056178665717 4766127739317849016749911)
              ·
                refine ⟨7149191608976773525124867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4766127739317849016749911 7149191608976773525124867)
                ·
                  refine ⟨10723787413465160287687301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7149191608976773525124867 10723787413465160287687301)
                  ·
                    refine ⟨2010710140024717553941369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10723787413465160287687301 2010710140024717553941369)
                    ·
                      refine ⟨1508032605018538165456027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2010710140024717553941369 1508032605018538165456027)
                      ·
                        rfl

theorem cell23_2936883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 4, 2].length) (baseStart_2936883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936883 prefixEnd_2936883 := by exact prefixLift 2936883
  have htrace : WordTrace (prefixWord ++ tailWord_2936883) baseStart_2936883 baseEnd_2936883 := by
    simpa [prefixWord, tailWord_2936883, baseEnd_2936883] using wordTrace_append hprefix tailTrace_2936883
  have hstable : (prefixWord ++ tailWord_2936883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936883).length < 2 ^ (prefixWord ++ tailWord_2936883).sum := by decide
  have hdescent : baseEnd_2936883 < baseStart_2936883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936953 : List Nat := [1, 2, 1, 3, 4, 2, 2, 1, 2, 5]
def baseStart_2936953 : Nat := 118140960795 + 2936953 * 2 ^ 59
def prefixEnd_2936953 : Nat := 4983230072969 + 3 ^ 40 * 2936953 * 2
def baseEnd_2936953 : Nat := 502689516221450963860235

theorem tailTrace_2936953 : CollatzResearch.WordTrace tailWord_2936953 prefixEnd_2936953 502689516221450963860235 := by
  unfold tailWord_2936953
  simp only [CollatzResearch.WordTrace]
  refine ⟨107119476128928347483759513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71412984085952231655839675 107119476128928347483759513)
  ·
    refine ⟨80339607096696260612819635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107119476128928347483759513 80339607096696260612819635)
    ·
      refine ⟨120509410645044390919229453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80339607096696260612819635 120509410645044390919229453)
      ·
        refine ⟨45191028991891646594711045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120509410645044390919229453 45191028991891646594711045)
        ·
          refine ⟨8473317935979683736508321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45191028991891646594711045 8473317935979683736508321)
          ·
            refine ⟨6354988451984762802381241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8473317935979683736508321 6354988451984762802381241)
            ·
              refine ⟨4766241338988572101785931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6354988451984762802381241 4766241338988572101785931)
              ·
                refine ⟨7149362008482858152678897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4766241338988572101785931 7149362008482858152678897)
                ·
                  refine ⟨5362021506362143614509173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7149362008482858152678897 5362021506362143614509173)
                  ·
                    refine ⟨502689516221450963860235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5362021506362143614509173 502689516221450963860235)
                    ·
                      rfl

theorem cell23_2936953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 5].length) (baseStart_2936953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936953 prefixEnd_2936953 := by exact prefixLift 2936953
  have htrace : WordTrace (prefixWord ++ tailWord_2936953) baseStart_2936953 baseEnd_2936953 := by
    simpa [prefixWord, tailWord_2936953, baseEnd_2936953] using wordTrace_append hprefix tailTrace_2936953
  have hstable : (prefixWord ++ tailWord_2936953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936953).length < 2 ^ (prefixWord ++ tailWord_2936953).sum := by decide
  have hdescent : baseEnd_2936953 < baseStart_2936953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936959 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 11]
def baseStart_2936959 : Nat := 118140960795 + 2936959 * 2 ^ 59
def prefixEnd_2936959 : Nat := 4983230072969 + 3 ^ 40 * 2936959 * 2
def baseEnd_2936959 : Nat := 1508071629548279868105677

theorem tailTrace_2936959 : CollatzResearch.WordTrace tailWord_2936959 prefixEnd_2936959 1508071629548279868105677 := by
  unfold tailWord_2936959
  simp only [CollatzResearch.WordTrace]
  refine ⟨107119694966906610508477931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71413129977937740338985287 107119694966906610508477931)
  ·
    refine ⟨160679542450359915762716897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107119694966906610508477931 160679542450359915762716897)
    ·
      refine ⟨120509656837769936822037673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160679542450359915762716897 120509656837769936822037673)
      ·
        refine ⟨90382242628327452616528255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120509656837769936822037673 90382242628327452616528255)
        ·
          refine ⟨135573363942491178924792383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90382242628327452616528255 135573363942491178924792383)
          ·
            refine ⟨203360045913736768387188575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135573363942491178924792383 203360045913736768387188575)
            ·
              refine ⟨305040068870605152580782863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203360045913736768387188575 305040068870605152580782863)
              ·
                refine ⟨457560103305907728871174295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305040068870605152580782863 457560103305907728871174295)
                ·
                  refine ⟨686340154958861593306761443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 457560103305907728871174295 686340154958861593306761443)
                  ·
                    refine ⟨1029510232438292389960142165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 686340154958861593306761443 1029510232438292389960142165)
                    ·
                      refine ⟨1508071629548279868105677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 1029510232438292389960142165 1508071629548279868105677)
                      ·
                        rfl

theorem cell23_2936959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_2936959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936959 prefixEnd_2936959 := by exact prefixLift 2936959
  have htrace : WordTrace (prefixWord ++ tailWord_2936959) baseStart_2936959 baseEnd_2936959 := by
    simpa [prefixWord, tailWord_2936959, baseEnd_2936959] using wordTrace_append hprefix tailTrace_2936959
  have hstable : (prefixWord ++ tailWord_2936959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936959).length < 2 ^ (prefixWord ++ tailWord_2936959).sum := by decide
  have hdescent : baseEnd_2936959 < baseStart_2936959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2936974 : List Nat := [4, 1, 1, 3, 4, 1, 2, 2, 5]
def baseStart_2936974 : Nat := 118140960795 + 2936974 * 2 ^ 59
def prefixEnd_2936974 : Nat := 4983230072969 + 3 ^ 40 * 2936974 * 2
def baseEnd_2936974 : Nat := 167564370195344145490901

theorem tailTrace_2936974 : CollatzResearch.WordTrace tailWord_2936974 prefixEnd_2936974 167564370195344145490901 := by
  unfold tailWord_2936974
  simp only [CollatzResearch.WordTrace]
  refine ⟨13390030257731533508784247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71413494707901512046849317 13390030257731533508784247)
  ·
    refine ⟨20085045386597300263176371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13390030257731533508784247 20085045386597300263176371)
    ·
      refine ⟨30127568079895950394764557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20085045386597300263176371 30127568079895950394764557)
      ·
        refine ⟨11297838029960981398036709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30127568079895950394764557 11297838029960981398036709)
        ·
          refine ⟨2118344630617684012131883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11297838029960981398036709 2118344630617684012131883)
          ·
            refine ⟨3177516945926526018197825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118344630617684012131883 3177516945926526018197825)
            ·
              refine ⟨2383137709444894513648369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3177516945926526018197825 2383137709444894513648369)
              ·
                refine ⟨1787353282083670885236277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2383137709444894513648369 1787353282083670885236277)
                ·
                  refine ⟨167564370195344145490901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1787353282083670885236277 167564370195344145490901)
                  ·
                    rfl

theorem cell23_2936974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_2936974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2936974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2936974 prefixEnd_2936974 := by exact prefixLift 2936974
  have htrace : WordTrace (prefixWord ++ tailWord_2936974) baseStart_2936974 baseEnd_2936974 := by
    simpa [prefixWord, tailWord_2936974, baseEnd_2936974] using wordTrace_append hprefix tailTrace_2936974
  have hstable : (prefixWord ++ tailWord_2936974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2936974).length < 2 ^ (prefixWord ++ tailWord_2936974).sum := by decide
  have hdescent : baseEnd_2936974 < baseStart_2936974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2936974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937023 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 7, 1, 3]
def baseStart_2937023 : Nat := 118140960795 + 2937023 * 2 ^ 59
def prefixEnd_2937023 : Nat := 4983230072969 + 3 ^ 40 * 2937023 * 2
def baseEnd_2937023 : Nat := 1508104492310167617705383

theorem tailTrace_2937023 : CollatzResearch.WordTrace tailWord_2937023 prefixEnd_2937023 1508104492310167617705383 := by
  unfold tailWord_2937023
  simp only [CollatzResearch.WordTrace]
  refine ⟨107122029238674749438807723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71414686159116499625871815 107122029238674749438807723)
  ·
    refine ⟨160683043858012124158211585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107122029238674749438807723 160683043858012124158211585)
    ·
      refine ⟨120512282893509093118658689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160683043858012124158211585 120512282893509093118658689)
      ·
        refine ⟨90384212170131819838994017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120512282893509093118658689 90384212170131819838994017)
        ·
          refine ⟨67788159127598864879245513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90384212170131819838994017 67788159127598864879245513)
          ·
            refine ⟨50841119345699148659434135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67788159127598864879245513 50841119345699148659434135)
            ·
              refine ⟨76261679018548722989151203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50841119345699148659434135 76261679018548722989151203)
              ·
                refine ⟨114392518527823084483726805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76261679018548722989151203 114392518527823084483726805)
                ·
                  refine ⟨2681074652995853542587347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 114392518527823084483726805 2681074652995853542587347)
                  ·
                    refine ⟨4021611979493780313881021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2681074652995853542587347 4021611979493780313881021)
                    ·
                      refine ⟨1508104492310167617705383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4021611979493780313881021 1508104492310167617705383)
                      ·
                        rfl

theorem cell23_2937023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 1, 3].length) (baseStart_2937023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937023 prefixEnd_2937023 := by exact prefixLift 2937023
  have htrace : WordTrace (prefixWord ++ tailWord_2937023) baseStart_2937023 baseEnd_2937023 := by
    simpa [prefixWord, tailWord_2937023, baseEnd_2937023] using wordTrace_append hprefix tailTrace_2937023
  have hstable : (prefixWord ++ tailWord_2937023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937023).length < 2 ^ (prefixWord ++ tailWord_2937023).sum := by decide
  have hdescent : baseEnd_2937023 < baseStart_2937023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937073 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 4, 4]
def baseStart_2937073 : Nat := 118140960795 + 2937073 * 2 ^ 59
def prefixEnd_2937073 : Nat := 4983230072969 + 3 ^ 40 * 2937073 * 2
def baseEnd_2937073 : Nat := 502710055447630807360051

theorem tailTrace_2937073 : CollatzResearch.WordTrace tailWord_2937073 prefixEnd_2937073 502710055447630807360051 := by
  unfold tailWord_2937073
  simp only [CollatzResearch.WordTrace]
  refine ⟨107123852888493607978127873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71415901925662405318751915 107123852888493607978127873)
  ·
    refine ⟨80342889666370205983595905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107123852888493607978127873 80342889666370205983595905)
    ·
      refine ⟨60257167249777654487696929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80342889666370205983595905 60257167249777654487696929)
      ·
        refine ⟨45192875437333240865772697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60257167249777654487696929 45192875437333240865772697)
        ·
          refine ⟨33894656577999930649329523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45192875437333240865772697 33894656577999930649329523)
          ·
            refine ⟨50841984866999895973994285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33894656577999930649329523 50841984866999895973994285)
            ·
              refine ⟨19065744325124960990247857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50841984866999895973994285 19065744325124960990247857)
              ·
                refine ⟨14299308243843720742685893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19065744325124960990247857 14299308243843720742685893)
                ·
                  refine ⟨2681120295720697639253605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14299308243843720742685893 2681120295720697639253605)
                  ·
                    refine ⟨502710055447630807360051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2681120295720697639253605 502710055447630807360051)
                    ·
                      rfl

theorem cell23_2937073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 4].length) (baseStart_2937073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937073 prefixEnd_2937073 := by exact prefixLift 2937073
  have htrace : WordTrace (prefixWord ++ tailWord_2937073) baseStart_2937073 baseEnd_2937073 := by
    simpa [prefixWord, tailWord_2937073, baseEnd_2937073] using wordTrace_append hprefix tailTrace_2937073
  have hstable : (prefixWord ++ tailWord_2937073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937073).length < 2 ^ (prefixWord ++ tailWord_2937073).sum := by decide
  have hdescent : baseEnd_2937073 < baseStart_2937073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937074 : List Nat := [3, 2, 1, 3, 2, 1, 3, 3, 1, 1, 3]
def baseStart_2937074 : Nat := 118140960795 + 2937074 * 2 ^ 59
def prefixEnd_2937074 : Nat := 4983230072969 + 3 ^ 40 * 2937074 * 2
def baseEnd_2937074 : Nat := 1508130679823546918167649

theorem tailTrace_2937074 : CollatzResearch.WordTrace tailWord_2937074 prefixEnd_2937074 1508130679823546918167649 := by
  unfold tailWord_2937074
  simp only [CollatzResearch.WordTrace]
  refine ⟨26780972340372496287228569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71415926240993323432609517 26780972340372496287228569)
  ·
    refine ⟨20085729255279372215421427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26780972340372496287228569 20085729255279372215421427)
    ·
      refine ⟨30128593882919058323132141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20085729255279372215421427 30128593882919058323132141)
      ·
        refine ⟨11298222706094646871174553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30128593882919058323132141 11298222706094646871174553)
        ·
          refine ⟨8473667029570985153380915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11298222706094646871174553 8473667029570985153380915)
          ·
            refine ⟨12710500544356477730071373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8473667029570985153380915 12710500544356477730071373)
            ·
              refine ⟨4766437704133679148776765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12710500544356477730071373 4766437704133679148776765)
              ·
                refine ⟨1787414139050129680791287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4766437704133679148776765 1787414139050129680791287)
                ·
                  refine ⟨2681121208575194521186931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1787414139050129680791287 2681121208575194521186931)
                  ·
                    refine ⟨4021681812862791781780397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2681121208575194521186931 4021681812862791781780397)
                    ·
                      refine ⟨1508130679823546918167649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4021681812862791781780397 1508130679823546918167649)
                      ·
                        rfl

theorem cell23_2937074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_2937074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937074 prefixEnd_2937074 := by exact prefixLift 2937074
  have htrace : WordTrace (prefixWord ++ tailWord_2937074) baseStart_2937074 baseEnd_2937074 := by
    simpa [prefixWord, tailWord_2937074, baseEnd_2937074] using wordTrace_append hprefix tailTrace_2937074
  have hstable : (prefixWord ++ tailWord_2937074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937074).length < 2 ^ (prefixWord ++ tailWord_2937074).sum := by decide
  have hdescent : baseEnd_2937074 < baseStart_2937074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937080 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 5, 2, 2]
def baseStart_2937080 : Nat := 118140960795 + 2937080 * 2 ^ 59
def prefixEnd_2937080 : Nat := 4983230072969 + 3 ^ 40 * 2937080 * 2
def baseEnd_2937080 : Nat := 1508133760707473894692621

theorem tailTrace_2937080 : CollatzResearch.WordTrace tailWord_2937080 prefixEnd_2937080 1508133760707473894692621 := by
  unfold tailWord_2937080
  simp only [CollatzResearch.WordTrace]
  refine ⟨53562054099734124086816347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71416072132978832115755129 53562054099734124086816347)
  ·
    refine ⟨80343081149601186130224521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53562054099734124086816347 80343081149601186130224521)
    ·
      refine ⟨60257310862200889597668391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80343081149601186130224521 60257310862200889597668391)
      ·
        refine ⟨90385966293301334396502587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60257310862200889597668391 90385966293301334396502587)
        ·
          refine ⟨135578949439952001594753881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90385966293301334396502587 135578949439952001594753881)
          ·
            refine ⟨101684212079964001196065411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135578949439952001594753881 101684212079964001196065411)
            ·
              refine ⟨152526318119946001794098117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101684212079964001196065411 152526318119946001794098117)
              ·
                refine ⟨28598684647489875336393397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152526318119946001794098117 28598684647489875336393397)
                ·
                  refine ⟨2681126685702175812786881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28598684647489875336393397 2681126685702175812786881)
                  ·
                    refine ⟨2010845014276631859590161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2681126685702175812786881 2010845014276631859590161)
                    ·
                      refine ⟨1508133760707473894692621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2010845014276631859590161 1508133760707473894692621)
                      ·
                        rfl

theorem cell23_2937080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 5, 2, 2].length) (baseStart_2937080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937080 prefixEnd_2937080 := by exact prefixLift 2937080
  have htrace : WordTrace (prefixWord ++ tailWord_2937080) baseStart_2937080 baseEnd_2937080 := by
    simpa [prefixWord, tailWord_2937080, baseEnd_2937080] using wordTrace_append hprefix tailTrace_2937080
  have hstable : (prefixWord ++ tailWord_2937080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937080).length < 2 ^ (prefixWord ++ tailWord_2937080).sum := by decide
  have hdescent : baseEnd_2937080 < baseStart_2937080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937097 : List Nat := [1, 2, 1, 1, 3, 4, 3, 1, 3, 2, 2]
def baseStart_2937097 : Nat := 118140960795 + 2937097 * 2 ^ 59
def prefixEnd_2937097 : Nat := 4983230072969 + 3 ^ 40 * 2937097 * 2
def baseEnd_2937097 : Nat := 1508142489878600328180043

theorem tailTrace_2937097 : CollatzResearch.WordTrace tailWord_2937097 prefixEnd_2937097 1508142489878600328180043 := by
  unfold tailWord_2937097
  simp only [CollatzResearch.WordTrace]
  refine ⟨107124728240406660077001545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71416485493604440051334363 107124728240406660077001545)
  ·
    refine ⟨80343546180304995057751159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107124728240406660077001545 80343546180304995057751159)
    ·
      refine ⟨120515319270457492586626739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80343546180304995057751159 120515319270457492586626739)
      ·
        refine ⟨180772978905686238879940109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120515319270457492586626739 180772978905686238879940109)
        ·
          refine ⟨67789867089632339579977541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180772978905686238879940109 67789867089632339579977541)
          ·
            refine ⟨12710600079306063671245789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67789867089632339579977541 12710600079306063671245789)
            ·
              refine ⟨4766475029739773876717171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12710600079306063671245789 4766475029739773876717171)
              ·
                refine ⟨7149712544609660815075757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4766475029739773876717171 7149712544609660815075757)
                ·
                  refine ⟨2681142204228622805653409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7149712544609660815075757 2681142204228622805653409)
                  ·
                    refine ⟨2010856653171467104240057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2681142204228622805653409 2010856653171467104240057)
                    ·
                      refine ⟨1508142489878600328180043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2010856653171467104240057 1508142489878600328180043)
                      ·
                        rfl

theorem cell23_2937097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 1, 3, 2, 2].length) (baseStart_2937097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937097 prefixEnd_2937097 := by exact prefixLift 2937097
  have htrace : WordTrace (prefixWord ++ tailWord_2937097) baseStart_2937097 baseEnd_2937097 := by
    simpa [prefixWord, tailWord_2937097, baseEnd_2937097] using wordTrace_append hprefix tailTrace_2937097
  have hstable : (prefixWord ++ tailWord_2937097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937097).length < 2 ^ (prefixWord ++ tailWord_2937097).sum := by decide
  have hdescent : baseEnd_2937097 < baseStart_2937097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937114 : List Nat := [3, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4]
def baseStart_2937114 : Nat := 118140960795 + 2937114 * 2 ^ 59
def prefixEnd_2937114 : Nat := 4983230072969 + 3 ^ 40 * 2937114 * 2
def baseEnd_2937114 : Nat := 1508151219049726761667465

theorem tailTrace_2937114 : CollatzResearch.WordTrace tailWord_2937114 prefixEnd_2937114 1508151219049726761667465 := by
  unfold tailWord_2937114
  simp only [CollatzResearch.WordTrace]
  refine ⟨26781337070336267995092599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71416898854230047986913597 26781337070336267995092599)
  ·
    refine ⟨40172005605504401992638899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26781337070336267995092599 40172005605504401992638899)
    ·
      refine ⟨60258008408256602988958349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40172005605504401992638899 60258008408256602988958349)
      ·
        refine ⟨22596753153096226120859381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60258008408256602988958349 22596753153096226120859381)
        ·
          refine ⟨2118445608102771198830567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22596753153096226120859381 2118445608102771198830567)
          ·
            refine ⟨3177668412154156798245851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118445608102771198830567 3177668412154156798245851)
            ·
              refine ⟨4766502618231235197368777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3177668412154156798245851 4766502618231235197368777)
              ·
                refine ⟨3574876963673426398026583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4766502618231235197368777 3574876963673426398026583)
                ·
                  refine ⟨5362315445510139597039875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3574876963673426398026583 5362315445510139597039875)
                  ·
                    refine ⟨8043473168265209395559813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5362315445510139597039875 8043473168265209395559813)
                    ·
                      refine ⟨1508151219049726761667465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8043473168265209395559813 1508151219049726761667465)
                      ·
                        rfl

theorem cell23_2937114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_2937114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937114 prefixEnd_2937114 := by exact prefixLift 2937114
  have htrace : WordTrace (prefixWord ++ tailWord_2937114) baseStart_2937114 baseEnd_2937114 := by
    simpa [prefixWord, tailWord_2937114, baseEnd_2937114] using wordTrace_append hprefix tailTrace_2937114
  have hstable : (prefixWord ++ tailWord_2937114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937114).length < 2 ^ (prefixWord ++ tailWord_2937114).sum := by decide
  have hdescent : baseEnd_2937114 < baseStart_2937114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937117 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_2937117 : Nat := 118140960795 + 2937117 * 2 ^ 59
def prefixEnd_2937117 : Nat := 4983230072969 + 3 ^ 40 * 2937117 * 2
def baseEnd_2937117 : Nat := 1508152759491690249929951

theorem tailTrace_2937117 : CollatzResearch.WordTrace tailWord_2937117 prefixEnd_2937117 1508152759491690249929951 := by
  unfold tailWord_2937117
  simp only [CollatzResearch.WordTrace]
  refine ⟨107125457700334203492729605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71416971800222802328486403 107125457700334203492729605)
  ·
    refine ⟨20086023318812663154886801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107125457700334203492729605 20086023318812663154886801)
    ·
      refine ⟨15064517489109497366165101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20086023318812663154886801 15064517489109497366165101)
      ·
        refine ⟨5649194058416061512311913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15064517489109497366165101 5649194058416061512311913)
        ·
          refine ⟨4236895543812046134233935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5649194058416061512311913 4236895543812046134233935)
          ·
            refine ⟨6355343315718069201350903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4236895543812046134233935 6355343315718069201350903)
            ·
              refine ⟨9533014973577103802026355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6355343315718069201350903 9533014973577103802026355)
              ·
                refine ⟨14299522460365655703039533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9533014973577103802026355 14299522460365655703039533)
                ·
                  refine ⟨5362320922637120888639825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14299522460365655703039533 5362320922637120888639825)
                  ·
                    refine ⟨4021740691977840666479869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5362320922637120888639825 4021740691977840666479869)
                    ·
                      refine ⟨1508152759491690249929951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4021740691977840666479869 1508152759491690249929951)
                      ·
                        rfl

theorem cell23_2937117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_2937117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937117 prefixEnd_2937117 := by exact prefixLift 2937117
  have htrace : WordTrace (prefixWord ++ tailWord_2937117) baseStart_2937117 baseEnd_2937117 := by
    simpa [prefixWord, tailWord_2937117, baseEnd_2937117] using wordTrace_append hprefix tailTrace_2937117
  have hstable : (prefixWord ++ tailWord_2937117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937117).length < 2 ^ (prefixWord ++ tailWord_2937117).sum := by decide
  have hdescent : baseEnd_2937117 < baseStart_2937117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937134 : List Nat := [4, 1, 3, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_2937134 : Nat := 118140960795 + 2937134 * 2 ^ 59
def prefixEnd_2937134 : Nat := 4983230072969 + 3 ^ 40 * 2937134 * 2
def baseEnd_2937134 : Nat := 1508161488662816683417373

theorem tailTrace_2937134 : CollatzResearch.WordTrace tailWord_2937134 prefixEnd_2937134 1508161488662816683417373 := by
  unfold tailWord_2937134
  simp only [CollatzResearch.WordTrace]
  refine ⟨13390759717659076924512307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71417385160848410264065637 13390759717659076924512307)
  ·
    refine ⟨20086139576488615386768461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13390759717659076924512307 20086139576488615386768461)
    ·
      refine ⟨7532302341183230770038173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20086139576488615386768461 7532302341183230770038173)
      ·
        refine ⟨2824613377943711538764315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7532302341183230770038173 2824613377943711538764315)
        ·
          refine ⟨4236920066915567308146473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2824613377943711538764315 4236920066915567308146473)
          ·
            refine ⟨3177690050186675481109855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4236920066915567308146473 3177690050186675481109855)
            ·
              refine ⟨4766535075280013221664783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3177690050186675481109855 4766535075280013221664783)
              ·
                refine ⟨7149802612920019832497175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4766535075280013221664783 7149802612920019832497175)
                ·
                  refine ⟨10724703919380029748745763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7149802612920019832497175 10724703919380029748745763)
                  ·
                    refine ⟨16087055879070044623118645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10724703919380029748745763 16087055879070044623118645)
                    ·
                      refine ⟨1508161488662816683417373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16087055879070044623118645 1508161488662816683417373)
                      ·
                        rfl

theorem cell23_2937134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_2937134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937134 prefixEnd_2937134 := by exact prefixLift 2937134
  have htrace : WordTrace (prefixWord ++ tailWord_2937134) baseStart_2937134 baseEnd_2937134 := by
    simpa [prefixWord, tailWord_2937134, baseEnd_2937134] using wordTrace_append hprefix tailTrace_2937134
  have hstable : (prefixWord ++ tailWord_2937134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937134).length < 2 ^ (prefixWord ++ tailWord_2937134).sum := by decide
  have hdescent : baseEnd_2937134 < baseStart_2937134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937182 : List Nat := [4, 4, 2, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_2937182 : Nat := 118140960795 + 2937182 * 2 ^ 59
def prefixEnd_2937182 : Nat := 4983230072969 + 3 ^ 40 * 2937182 * 2
def baseEnd_2937182 : Nat := 1508186135734232495617153

theorem tailTrace_2937182 : CollatzResearch.WordTrace tailWord_2937182 prefixEnd_2937182 1508186135734232495617153 := by
  unfold tailWord_2937182
  simp only [CollatzResearch.WordTrace]
  refine ⟨13390978555637339949230725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71418552296732479729230533 13390978555637339949230725)
  ·
    refine ⟨2510808479182001240480761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13390978555637339949230725 2510808479182001240480761)
    ·
      refine ⟨1883106359386500930360571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2510808479182001240480761 1883106359386500930360571)
      ·
        refine ⟨2824659539079751395540857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1883106359386500930360571 2824659539079751395540857)
        ·
          refine ⟨2118494654309813546655643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2824659539079751395540857 2118494654309813546655643)
          ·
            refine ⟨3177741981464720319983465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118494654309813546655643 3177741981464720319983465)
            ·
              refine ⟨2383306486098540239987599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3177741981464720319983465 2383306486098540239987599)
              ·
                refine ⟨3574959729147810359981399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2383306486098540239987599 3574959729147810359981399)
                ·
                  refine ⟨5362439593721715539972099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3574959729147810359981399 5362439593721715539972099)
                  ·
                    refine ⟨8043659390582573309958149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5362439593721715539972099 8043659390582573309958149)
                    ·
                      refine ⟨1508186135734232495617153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8043659390582573309958149 1508186135734232495617153)
                      ·
                        rfl

theorem cell23_2937182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_2937182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937182 prefixEnd_2937182 := by exact prefixLift 2937182
  have htrace : WordTrace (prefixWord ++ tailWord_2937182) baseStart_2937182 baseEnd_2937182 := by
    simpa [prefixWord, tailWord_2937182, baseEnd_2937182] using wordTrace_append hprefix tailTrace_2937182
  have hstable : (prefixWord ++ tailWord_2937182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937182).length < 2 ^ (prefixWord ++ tailWord_2937182).sum := by decide
  have hdescent : baseEnd_2937182 < baseStart_2937182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937187 : List Nat := [1, 1, 1, 5, 2, 1, 2, 2, 4, 2, 2]
def baseStart_2937187 : Nat := 118140960795 + 2937187 * 2 ^ 59
def prefixEnd_2937187 : Nat := 4983230072969 + 3 ^ 40 * 2937187 * 2
def baseEnd_2937187 : Nat := 1508188703137504976054629

theorem tailTrace_2937187 : CollatzResearch.WordTrace tailWord_2937187 prefixEnd_2937187 1508188703137504976054629 := by
  unfold tailWord_2937187
  simp only [CollatzResearch.WordTrace]
  refine ⟨107128010810080605447777815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71418673873387070298518543 107128010810080605447777815)
  ·
    refine ⟨160692016215120908171666723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107128010810080605447777815 160692016215120908171666723)
    ·
      refine ⟨241038024322681362257500085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160692016215120908171666723 241038024322681362257500085)
      ·
        refine ⟨22597314780251377711640633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 241038024322681362257500085 22597314780251377711640633)
        ·
          refine ⟨16947986085188533283730475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22597314780251377711640633 16947986085188533283730475)
          ·
            refine ⟨25421979127782799925595713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16947986085188533283730475 25421979127782799925595713)
            ·
              refine ⟨19066484345837099944196785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25421979127782799925595713 19066484345837099944196785)
              ·
                refine ⟨14299863259377824958147589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19066484345837099944196785 14299863259377824958147589)
                ·
                  refine ⟨2681224361133342179652673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14299863259377824958147589 2681224361133342179652673)
                  ·
                    refine ⟨2010918270850006634739505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2681224361133342179652673 2010918270850006634739505)
                    ·
                      refine ⟨1508188703137504976054629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2010918270850006634739505 1508188703137504976054629)
                      ·
                        rfl

theorem cell23_2937187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_2937187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937187 prefixEnd_2937187 := by exact prefixLift 2937187
  have htrace : WordTrace (prefixWord ++ tailWord_2937187) baseStart_2937187 baseEnd_2937187 := by
    simpa [prefixWord, tailWord_2937187, baseEnd_2937187] using wordTrace_append hprefix tailTrace_2937187
  have hstable : (prefixWord ++ tailWord_2937187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937187).length < 2 ^ (prefixWord ++ tailWord_2937187).sum := by decide
  have hdescent : baseEnd_2937187 < baseStart_2937187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937191 : List Nat := [1, 1, 5, 1, 3, 3, 2, 1, 1, 3, 2]
def baseStart_2937191 : Nat := 118140960795 + 2937191 * 2 ^ 59
def prefixEnd_2937191 : Nat := 4983230072969 + 3 ^ 40 * 2937191 * 2
def baseEnd_2937191 : Nat := 1508190757060122960404611

theorem tailTrace_2937191 : CollatzResearch.WordTrace tailWord_2937191 prefixEnd_2937191 1508190757060122960404611 := by
  unfold tailWord_2937191
  simp only [CollatzResearch.WordTrace]
  refine ⟨107128156702066114130923427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71418771134710742753948951 107128156702066114130923427)
  ·
    refine ⟨160692235053099171196385141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107128156702066114130923427 160692235053099171196385141)
    ·
      refine ⟨15064897036228047299661107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160692235053099171196385141 15064897036228047299661107)
      ·
        refine ⟨22597345554342070949491661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15064897036228047299661107 22597345554342070949491661)
        ·
          refine ⟨8474004582878276606059373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22597345554342070949491661 8474004582878276606059373)
          ·
            refine ⟨3177751718579353727272265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8474004582878276606059373 3177751718579353727272265)
            ·
              refine ⟨2383313788934515295454199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3177751718579353727272265 2383313788934515295454199)
              ·
                refine ⟨3574970683401772943181299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2383313788934515295454199 3574970683401772943181299)
                ·
                  refine ⟨5362456025102659414771949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3574970683401772943181299 5362456025102659414771949)
                  ·
                    refine ⟨2010921009413497280539481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5362456025102659414771949 2010921009413497280539481)
                    ·
                      refine ⟨1508190757060122960404611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2010921009413497280539481 1508190757060122960404611)
                      ·
                        rfl

theorem cell23_2937191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 1, 3, 2].length) (baseStart_2937191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937191 prefixEnd_2937191 := by exact prefixLift 2937191
  have htrace : WordTrace (prefixWord ++ tailWord_2937191) baseStart_2937191 baseEnd_2937191 := by
    simpa [prefixWord, tailWord_2937191, baseEnd_2937191] using wordTrace_append hprefix tailTrace_2937191
  have hstable : (prefixWord ++ tailWord_2937191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937191).length < 2 ^ (prefixWord ++ tailWord_2937191).sum := by decide
  have hdescent : baseEnd_2937191 < baseStart_2937191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937203 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 3]
def baseStart_2937203 : Nat := 118140960795 + 2937203 * 2 ^ 59
def prefixEnd_2937203 : Nat := 4983230072969 + 3 ^ 40 * 2937203 * 2
def baseEnd_2937203 : Nat := 1508196918827976913454555

theorem tailTrace_2937203 : CollatzResearch.WordTrace tailWord_2937203 prefixEnd_2937203 1508196918827976913454555 := by
  unfold tailWord_2937203
  simp only [CollatzResearch.WordTrace]
  refine ⟨107128594378022640180360263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71419062918681760120240175 107128594378022640180360263)
  ·
    refine ⟨160692891567033960270540395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107128594378022640180360263 160692891567033960270540395)
    ·
      refine ⟨241039337350550940405810593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160692891567033960270540395 241039337350550940405810593)
      ·
        refine ⟨180779503012913205304357945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241039337350550940405810593 180779503012913205304357945)
        ·
          refine ⟨135584627259684903978268459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180779503012913205304357945 135584627259684903978268459)
          ·
            refine ⟨203376940889527355967402689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135584627259684903978268459 203376940889527355967402689)
            ·
              refine ⟨152532705667145516975552017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203376940889527355967402689 152532705667145516975552017)
              ·
                refine ⟨114399529250359137731664013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152532705667145516975552017 114399529250359137731664013)
                ·
                  refine ⟨42899823468884676649374005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114399529250359137731664013 42899823468884676649374005)
                  ·
                    refine ⟨4021858450207938435878813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42899823468884676649374005 4021858450207938435878813)
                    ·
                      refine ⟨1508196918827976913454555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4021858450207938435878813 1508196918827976913454555)
                      ·
                        rfl

theorem cell23_2937203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 3].length) (baseStart_2937203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937203 prefixEnd_2937203 := by exact prefixLift 2937203
  have htrace : WordTrace (prefixWord ++ tailWord_2937203) baseStart_2937203 baseEnd_2937203 := by
    simpa [prefixWord, tailWord_2937203, baseEnd_2937203] using wordTrace_append hprefix tailTrace_2937203
  have hstable : (prefixWord ++ tailWord_2937203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937203).length < 2 ^ (prefixWord ++ tailWord_2937203).sum := by decide
  have hdescent : baseEnd_2937203 < baseStart_2937203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937220 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 2, 3, 3]
def baseStart_2937220 : Nat := 118140960795 + 2937220 * 2 ^ 59
def prefixEnd_2937220 : Nat := 4983230072969 + 3 ^ 40 * 2937220 * 2
def baseEnd_2937220 : Nat := 1508205647999103346941977

theorem tailTrace_2937220 : CollatzResearch.WordTrace tailWord_2937220 prefixEnd_2937220 1508205647999103346941977 := by
  unfold tailWord_2937220
  simp only [CollatzResearch.WordTrace]
  refine ⟨53564607209480526041864557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71419476279307368055819409 53564607209480526041864557)
  ·
    refine ⟨20086727703555197265699209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53564607209480526041864557 20086727703555197265699209)
    ·
      refine ⟨15065045777666397949274407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20086727703555197265699209 15065045777666397949274407)
      ·
        refine ⟨22597568666499596923911611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15065045777666397949274407 22597568666499596923911611)
        ·
          refine ⟨33896352999749395385867417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22597568666499596923911611 33896352999749395385867417)
          ·
            refine ⟨25422264749812046539400563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33896352999749395385867417 25422264749812046539400563)
            ·
              refine ⟨38133397124718069809100845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25422264749812046539400563 38133397124718069809100845)
              ·
                refine ⟨14300023921769276178412817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38133397124718069809100845 14300023921769276178412817)
                ·
                  refine ⟨10725017941326957133809613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14300023921769276178412817 10725017941326957133809613)
                  ·
                    refine ⟨4021881727997608925178605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10725017941326957133809613 4021881727997608925178605)
                    ·
                      refine ⟨1508205647999103346941977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4021881727997608925178605 1508205647999103346941977)
                      ·
                        rfl

theorem cell23_2937220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_2937220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937220 prefixEnd_2937220 := by exact prefixLift 2937220
  have htrace : WordTrace (prefixWord ++ tailWord_2937220) baseStart_2937220 baseEnd_2937220 := by
    simpa [prefixWord, tailWord_2937220, baseEnd_2937220] using wordTrace_append hprefix tailTrace_2937220
  have hstable : (prefixWord ++ tailWord_2937220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937220).length < 2 ^ (prefixWord ++ tailWord_2937220).sum := by decide
  have hdescent : baseEnd_2937220 < baseStart_2937220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937223 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 3, 7]
def baseStart_2937223 : Nat := 118140960795 + 2937223 * 2 ^ 59
def prefixEnd_2937223 : Nat := 4983230072969 + 3 ^ 40 * 2937223 * 2
def baseEnd_2937223 : Nat := 502735729480355611734821

theorem tailTrace_2937223 : CollatzResearch.WordTrace tailWord_2937223 prefixEnd_2937223 502735729480355611734821 := by
  unfold tailWord_2937223
  simp only [CollatzResearch.WordTrace]
  refine ⟨107129323837950183596088323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71419549225300122397392215 107129323837950183596088323)
  ·
    refine ⟨160693985756925275394132485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107129323837950183596088323 160693985756925275394132485)
    ·
      refine ⟨30130122329423489136399841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160693985756925275394132485 30130122329423489136399841)
      ·
        refine ⟨22597591747067616852299881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30130122329423489136399841 22597591747067616852299881)
        ·
          refine ⟨16948193810300712639224911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22597591747067616852299881 16948193810300712639224911)
          ·
            refine ⟨25422290715451068958837367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16948193810300712639224911 25422290715451068958837367)
            ·
              refine ⟨38133436073176603438256051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25422290715451068958837367 38133436073176603438256051)
              ·
                refine ⟨57200154109764905157384077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38133436073176603438256051 57200154109764905157384077)
                ·
                  refine ⟨21450057791161839434019029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57200154109764905157384077 21450057791161839434019029)
                  ·
                    refine ⟨502735729480355611734821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21450057791161839434019029 502735729480355611734821)
                    ·
                      rfl

theorem cell23_2937223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_2937223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937223 prefixEnd_2937223 := by exact prefixLift 2937223
  have htrace : WordTrace (prefixWord ++ tailWord_2937223) baseStart_2937223 baseEnd_2937223 := by
    simpa [prefixWord, tailWord_2937223, baseEnd_2937223] using wordTrace_append hprefix tailTrace_2937223
  have hstable : (prefixWord ++ tailWord_2937223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937223).length < 2 ^ (prefixWord ++ tailWord_2937223).sum := by decide
  have hdescent : baseEnd_2937223 < baseStart_2937223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937240 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 1, 7]
def baseStart_2937240 : Nat := 118140960795 + 2937240 * 2 ^ 59
def prefixEnd_2937240 : Nat := 4983230072969 + 3 ^ 40 * 2937240 * 2
def baseEnd_2937240 : Nat := 502738639204064422897295

theorem tailTrace_2937240 : CollatzResearch.WordTrace tailWord_2937240 prefixEnd_2937240 502738639204064422897295 := by
  unfold tailWord_2937240
  simp only [CollatzResearch.WordTrace]
  refine ⟨53564971939444297749728587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71419962585925730332971449 53564971939444297749728587)
  ·
    refine ⟨80347457909166446624592881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53564971939444297749728587 80347457909166446624592881)
    ·
      refine ⟨60260593431874834968444661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80347457909166446624592881 60260593431874834968444661)
      ·
        refine ⟨5649430634238265778291687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 60260593431874834968444661 5649430634238265778291687)
        ·
          refine ⟨8474145951357398667437531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5649430634238265778291687 8474145951357398667437531)
          ·
            refine ⟨12711218927036098001156297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8474145951357398667437531 12711218927036098001156297)
            ·
              refine ⟨9533414195277073500867223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12711218927036098001156297 9533414195277073500867223)
              ·
                refine ⟨14300121292915610251300835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9533414195277073500867223 14300121292915610251300835)
                ·
                  refine ⟨21450181939373415376951253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14300121292915610251300835 21450181939373415376951253)
                  ·
                    refine ⟨502738639204064422897295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21450181939373415376951253 502738639204064422897295)
                    ·
                      rfl

theorem cell23_2937240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 1, 7].length) (baseStart_2937240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937240 prefixEnd_2937240 := by exact prefixLift 2937240
  have htrace : WordTrace (prefixWord ++ tailWord_2937240) baseStart_2937240 baseEnd_2937240 := by
    simpa [prefixWord, tailWord_2937240, baseEnd_2937240] using wordTrace_append hprefix tailTrace_2937240
  have hstable : (prefixWord ++ tailWord_2937240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937240).length < 2 ^ (prefixWord ++ tailWord_2937240).sum := by decide
  have hdescent : baseEnd_2937240 < baseStart_2937240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937250 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_2937250 : Nat := 118140960795 + 2937250 * 2 ^ 59
def prefixEnd_2937250 : Nat := 4983230072969 + 3 ^ 40 * 2937250 * 2
def baseEnd_2937250 : Nat := 1508221052418738229566839

theorem tailTrace_2937250 : CollatzResearch.WordTrace tailWord_2937250 prefixEnd_2937250 1508221052418738229566839 := by
  unfold tailWord_2937250
  simp only [CollatzResearch.WordTrace]
  refine ⟨26782577152213091801830301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71420205739234911471547469 26782577152213091801830301)
  ·
    refine ⟨10043466432079909425686363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26782577152213091801830301 10043466432079909425686363)
    ·
      refine ⟨15065199648119864138529545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10043466432079909425686363 15065199648119864138529545)
      ·
        refine ⟨11298899736089898103897159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15065199648119864138529545 11298899736089898103897159)
        ·
          refine ⟨16948349604134847155845739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11298899736089898103897159 16948349604134847155845739)
          ·
            refine ⟨25422524406202270733768609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16948349604134847155845739 25422524406202270733768609)
            ·
              refine ⟨19066893304651703050326457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25422524406202270733768609 19066893304651703050326457)
              ·
                refine ⟨14300169978488777287744843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19066893304651703050326457 14300169978488777287744843)
                ·
                  refine ⟨21450254967733165931617265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14300169978488777287744843 21450254967733165931617265)
                  ·
                    refine ⟨16087691225799874448712949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21450254967733165931617265 16087691225799874448712949)
                    ·
                      refine ⟨1508221052418738229566839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16087691225799874448712949 1508221052418738229566839)
                      ·
                        rfl

theorem cell23_2937250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_2937250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937250 prefixEnd_2937250 := by exact prefixLift 2937250
  have htrace : WordTrace (prefixWord ++ tailWord_2937250) baseStart_2937250 baseEnd_2937250 := by
    simpa [prefixWord, tailWord_2937250, baseEnd_2937250] using wordTrace_append hprefix tailTrace_2937250
  have hstable : (prefixWord ++ tailWord_2937250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937250).length < 2 ^ (prefixWord ++ tailWord_2937250).sum := by decide
  have hdescent : baseEnd_2937250 < baseStart_2937250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937261 : List Nat := [1, 5, 2, 2, 2, 1, 3, 2, 5]
def baseStart_2937261 : Nat := 118140960795 + 2937261 * 2 ^ 59
def prefixEnd_2937261 : Nat := 4983230072969 + 3 ^ 40 * 2937261 * 2
def baseEnd_2937261 : Nat := 167580744522881965169921

theorem tailTrace_2937261 : CollatzResearch.WordTrace tailWord_2937261 prefixEnd_2937261 167580744522881965169921 := by
  unfold tailWord_2937261
  simp only [CollatzResearch.WordTrace]
  refine ⟨107130709811812516085971637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71420473207875010723981091 107130709811812516085971637)
  ·
    refine ⟨10043504044857423383059841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 107130709811812516085971637 10043504044857423383059841)
    ·
      refine ⟨7532628033643067537294881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10043504044857423383059841 7532628033643067537294881)
      ·
        refine ⟨5649471025232300652971161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7532628033643067537294881 5649471025232300652971161)
        ·
          refine ⟨4237103268924225489728371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5649471025232300652971161 4237103268924225489728371)
          ·
            refine ⟨6355654903386338234592557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4237103268924225489728371 6355654903386338234592557)
            ·
              refine ⟨2383370588769876837972209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6355654903386338234592557 2383370588769876837972209)
              ·
                refine ⟨1787527941577407628479157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2383370588769876837972209 1787527941577407628479157)
                ·
                  refine ⟨167580744522881965169921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1787527941577407628479157 167580744522881965169921)
                  ·
                    rfl

theorem cell23_2937261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_2937261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937261 prefixEnd_2937261 := by exact prefixLift 2937261
  have htrace : WordTrace (prefixWord ++ tailWord_2937261) baseStart_2937261 baseEnd_2937261 := by
    simpa [prefixWord, tailWord_2937261, baseEnd_2937261] using wordTrace_append hprefix tailTrace_2937261
  have hstable : (prefixWord ++ tailWord_2937261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937261).length < 2 ^ (prefixWord ++ tailWord_2937261).sum := by decide
  have hdescent : baseEnd_2937261 < baseStart_2937261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937280 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 3]
def baseStart_2937280 : Nat := 118140960795 + 2937280 * 2 ^ 59
def prefixEnd_2937280 : Nat := 4983230072969 + 3 ^ 40 * 2937280 * 2
def baseEnd_2937280 : Nat := 1508236456838373112191701

theorem tailTrace_2937280 : CollatzResearch.WordTrace tailWord_2937280 prefixEnd_2937280 1508236456838373112191701 := by
  unfold tailWord_2937280
  simp only [CollatzResearch.WordTrace]
  refine ⟨53565701399371841165456647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71420935199162454887275529 53565701399371841165456647)
  ·
    refine ⟨80348552099057761748184971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53565701399371841165456647 80348552099057761748184971)
    ·
      refine ⟨120522828148586642622277457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80348552099057761748184971 120522828148586642622277457)
      ·
        refine ⟨90392121111439981966708093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120522828148586642622277457 90392121111439981966708093)
        ·
          refine ⟨33897045416789993237515535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90392121111439981966708093 33897045416789993237515535)
          ·
            refine ⟨50845568125184989856273303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33897045416789993237515535 50845568125184989856273303)
            ·
              refine ⟨76268352187777484784409955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50845568125184989856273303 76268352187777484784409955)
              ·
                refine ⟨114402528281666227176614933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76268352187777484784409955 114402528281666227176614933)
                ·
                  refine ⟨5362618513203104398903825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 114402528281666227176614933 5362618513203104398903825)
                  ·
                    refine ⟨4021963884902328299177869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5362618513203104398903825 4021963884902328299177869)
                    ·
                      refine ⟨1508236456838373112191701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4021963884902328299177869 1508236456838373112191701)
                      ·
                        rfl

theorem cell23_2937280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_2937280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937280 prefixEnd_2937280 := by exact prefixLift 2937280
  have htrace : WordTrace (prefixWord ++ tailWord_2937280) baseStart_2937280 baseEnd_2937280 := by
    simpa [prefixWord, tailWord_2937280, baseEnd_2937280] using wordTrace_append hprefix tailTrace_2937280
  have hstable : (prefixWord ++ tailWord_2937280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937280).length < 2 ^ (prefixWord ++ tailWord_2937280).sum := by decide
  have hdescent : baseEnd_2937280 < baseStart_2937280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937303 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 8]
def baseStart_2937303 : Nat := 118140960795 + 2937303 * 2 ^ 59
def prefixEnd_2937303 : Nat := 4983230072969 + 3 ^ 40 * 2937303 * 2
def baseEnd_2937303 : Nat := 1508248266893426522204095

theorem tailTrace_2937303 : CollatzResearch.WordTrace tailWord_2937303 prefixEnd_2937303 1508248266893426522204095 := by
  unfold tailWord_2937303
  simp only [CollatzResearch.WordTrace]
  refine ⟨107132241677660357259000563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71421494451773571506000375 107132241677660357259000563)
  ·
    refine ⟨160698362516490535888500845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107132241677660357259000563 160698362516490535888500845)
    ·
      refine ⟨60261885943683950958187817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160698362516490535888500845 60261885943683950958187817)
      ·
        refine ⟨45196414457762963218640863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60261885943683950958187817 45196414457762963218640863)
        ·
          refine ⟨67794621686644444827961295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45196414457762963218640863 67794621686644444827961295)
          ·
            refine ⟨101691932529966667241941943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67794621686644444827961295 101691932529966667241941943)
            ·
              refine ⟨152537898794950000862912915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101691932529966667241941943 152537898794950000862912915)
              ·
                refine ⟨228806848192425001294369373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152537898794950000862912915 228806848192425001294369373)
                ·
                  refine ⟨85802568072159375485388515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228806848192425001294369373 85802568072159375485388515)
                  ·
                    refine ⟨128703852108239063228082773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85802568072159375485388515 128703852108239063228082773)
                    ·
                      refine ⟨1508248266893426522204095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 128703852108239063228082773 1508248266893426522204095)
                      ·
                        rfl

theorem cell23_2937303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_2937303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937303 prefixEnd_2937303 := by exact prefixLift 2937303
  have htrace : WordTrace (prefixWord ++ tailWord_2937303) baseStart_2937303 baseEnd_2937303 := by
    simpa [prefixWord, tailWord_2937303, baseEnd_2937303] using wordTrace_append hprefix tailTrace_2937303
  have hstable : (prefixWord ++ tailWord_2937303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937303).length < 2 ^ (prefixWord ++ tailWord_2937303).sum := by decide
  have hdescent : baseEnd_2937303 < baseStart_2937303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937327 : List Nat := [1, 1, 2, 1, 4, 1, 1, 5, 3, 1, 3]
def baseStart_2937327 : Nat := 118140960795 + 2937327 * 2 ^ 59
def prefixEnd_2937327 : Nat := 4983230072969 + 3 ^ 40 * 2937327 * 2
def baseEnd_2937327 : Nat := 1508260590429134428303985

theorem tailTrace_2937327 : CollatzResearch.WordTrace tailWord_2937327 prefixEnd_2937327 1508260590429134428303985 := by
  unfold tailWord_2937327
  simp only [CollatzResearch.WordTrace]
  refine ⟨107133117029573409357874235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71422078019715606238582823 107133117029573409357874235)
  ·
    refine ⟨160699675544360114036811353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107133117029573409357874235 160699675544360114036811353)
    ·
      refine ⟨120524756658270085527608515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160699675544360114036811353 120524756658270085527608515)
      ·
        refine ⟨180787134987405128291412773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120524756658270085527608515 180787134987405128291412773)
        ·
          refine ⟨33897587810138461554639895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180787134987405128291412773 33897587810138461554639895)
          ·
            refine ⟨50846381715207692331959843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33897587810138461554639895 50846381715207692331959843)
            ·
              refine ⟨76269572572811538497939765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50846381715207692331959843 76269572572811538497939765)
              ·
                refine ⟨7150272428701081734181853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76269572572811538497939765 7150272428701081734181853)
                ·
                  refine ⟨2681352160762905650318195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7150272428701081734181853 2681352160762905650318195)
                  ·
                    refine ⟨4022028241144358475477293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2681352160762905650318195 4022028241144358475477293)
                    ·
                      refine ⟨1508260590429134428303985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4022028241144358475477293 1508260590429134428303985)
                      ·
                        rfl

theorem cell23_2937327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 1, 3].length) (baseStart_2937327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937327 prefixEnd_2937327 := by exact prefixLift 2937327
  have htrace : WordTrace (prefixWord ++ tailWord_2937327) baseStart_2937327 baseEnd_2937327 := by
    simpa [prefixWord, tailWord_2937327, baseEnd_2937327] using wordTrace_append hprefix tailTrace_2937327
  have hstable : (prefixWord ++ tailWord_2937327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937327).length < 2 ^ (prefixWord ++ tailWord_2937327).sum := by decide
  have hdescent : baseEnd_2937327 < baseStart_2937327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937337 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 4, 3, 2]
def baseStart_2937337 : Nat := 118140960795 + 2937337 * 2 ^ 59
def prefixEnd_2937337 : Nat := 4983230072969 + 3 ^ 40 * 2937337 * 2
def baseEnd_2937337 : Nat := 1508265725235679389178939

theorem tailTrace_2937337 : CollatzResearch.WordTrace tailWord_2937337 prefixEnd_2937337 1508265725235679389178939 := by
  unfold tailWord_2937337
  simp only [CollatzResearch.WordTrace]
  refine ⟨107133481759537181065738265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71422321173024787377158843 107133481759537181065738265)
  ·
    refine ⟨80350111319652885799303699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107133481759537181065738265 80350111319652885799303699)
    ·
      refine ⟨120525166979479328698955549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80350111319652885799303699 120525166979479328698955549)
      ·
        refine ⟨45196937617304748262108331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120525166979479328698955549 45196937617304748262108331)
        ·
          refine ⟨67795406425957122393162497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45196937617304748262108331 67795406425957122393162497)
          ·
            refine ⟨50846554819467841794871873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67795406425957122393162497 50846554819467841794871873)
            ·
              refine ⟨38134916114600881346153905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50846554819467841794871873 38134916114600881346153905)
              ·
                refine ⟨28601187085950661009615429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38134916114600881346153905 28601187085950661009615429)
                ·
                  refine ⟨5362722578615748939302893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28601187085950661009615429 5362722578615748939302893)
                  ·
                    refine ⟨2011020966980905852238585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5362722578615748939302893 2011020966980905852238585)
                    ·
                      refine ⟨1508265725235679389178939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2011020966980905852238585 1508265725235679389178939)
                      ·
                        rfl

theorem cell23_2937337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_2937337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937337 prefixEnd_2937337 := by exact prefixLift 2937337
  have htrace : WordTrace (prefixWord ++ tailWord_2937337) baseStart_2937337 baseEnd_2937337 := by
    simpa [prefixWord, tailWord_2937337, baseEnd_2937337] using wordTrace_append hprefix tailTrace_2937337
  have hstable : (prefixWord ++ tailWord_2937337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937337).length < 2 ^ (prefixWord ++ tailWord_2937337).sum := by decide
  have hdescent : baseEnd_2937337 < baseStart_2937337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937377 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 4, 4]
def baseStart_2937377 : Nat := 118140960795 + 2937377 * 2 ^ 59
def prefixEnd_2937377 : Nat := 4983230072969 + 3 ^ 40 * 2937377 * 2
def baseEnd_2937377 : Nat := 502762088153953077559585

theorem tailTrace_2937377 : CollatzResearch.WordTrace tailWord_2937377 prefixEnd_2937377 502762088153953077559585 := by
  unfold tailWord_2937377
  simp only [CollatzResearch.WordTrace]
  refine ⟨107134940679392267897194385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71423293786261511931462923 107134940679392267897194385)
  ·
    refine ⟨80351205509544200922895789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107134940679392267897194385 80351205509544200922895789)
    ·
      refine ⟨30131702066079075346085921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80351205509544200922895789 30131702066079075346085921)
      ·
        refine ⟨22598776549559306509564441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30131702066079075346085921 22598776549559306509564441)
        ·
          refine ⟨16949082412169479882173331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22598776549559306509564441 16949082412169479882173331)
          ·
            refine ⟨25423623618254219823259997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16949082412169479882173331 25423623618254219823259997)
            ·
              refine ⟨9533858856845332433722499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25423623618254219823259997 9533858856845332433722499)
              ·
                refine ⟨14300788285267998650583749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9533858856845332433722499 14300788285267998650583749)
                ·
                  refine ⟨2681397803487749746984453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14300788285267998650583749 2681397803487749746984453)
                  ·
                    refine ⟨502762088153953077559585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2681397803487749746984453 502762088153953077559585)
                    ·
                      rfl

theorem cell23_2937377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_2937377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937377 prefixEnd_2937377 := by exact prefixLift 2937377
  have htrace : WordTrace (prefixWord ++ tailWord_2937377) baseStart_2937377 baseEnd_2937377 := by
    simpa [prefixWord, tailWord_2937377, baseEnd_2937377] using wordTrace_append hprefix tailTrace_2937377
  have hstable : (prefixWord ++ tailWord_2937377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937377).length < 2 ^ (prefixWord ++ tailWord_2937377).sum := by decide
  have hdescent : baseEnd_2937377 < baseStart_2937377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937404 : List Nat := [2, 2, 2, 2, 3, 1, 1, 4, 1, 2, 3]
def baseStart_2937404 : Nat := 118140960795 + 2937404 * 2 ^ 59
def prefixEnd_2937404 : Nat := 4983230072969 + 3 ^ 40 * 2937404 * 2
def baseEnd_2937404 : Nat := 1508300128439530627041131

theorem tailTrace_2937404 : CollatzResearch.WordTrace tailWord_2937404 prefixEnd_2937404 1508300128439530627041131 := by
  unfold tailWord_2937404
  simp only [CollatzResearch.WordTrace]
  refine ⟨53567962725147225754213633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71423950300196301005618177 53567962725147225754213633)
  ·
    refine ⟨40175972043860419315660225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53567962725147225754213633 40175972043860419315660225)
    ·
      refine ⟨30131979032895314486745169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40175972043860419315660225 30131979032895314486745169)
      ·
        refine ⟨22598984274671485865058877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30131979032895314486745169 22598984274671485865058877)
        ·
          refine ⟨8474619103001807199397079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22598984274671485865058877 8474619103001807199397079)
          ·
            refine ⟨12711928654502710799095619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8474619103001807199397079 12711928654502710799095619)
            ·
              refine ⟨19067892981754066198643429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12711928654502710799095619 19067892981754066198643429)
              ·
                refine ⟨3575229934078887412245643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19067892981754066198643429 3575229934078887412245643)
                ·
                  refine ⟨5362844901118331118368465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3575229934078887412245643 5362844901118331118368465)
                  ·
                    refine ⟨4022133675838748338776349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5362844901118331118368465 4022133675838748338776349)
                    ·
                      refine ⟨1508300128439530627041131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4022133675838748338776349 1508300128439530627041131)
                      ·
                        rfl

theorem cell23_2937404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_2937404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937404 prefixEnd_2937404 := by exact prefixLift 2937404
  have htrace : WordTrace (prefixWord ++ tailWord_2937404) baseStart_2937404 baseEnd_2937404 := by
    simpa [prefixWord, tailWord_2937404, baseEnd_2937404] using wordTrace_append hprefix tailTrace_2937404
  have hstable : (prefixWord ++ tailWord_2937404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937404).length < 2 ^ (prefixWord ++ tailWord_2937404).sum := by decide
  have hdescent : baseEnd_2937404 < baseStart_2937404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937418 : List Nat := [3, 1, 2, 1, 1, 4, 3, 3, 1, 2, 2]
def baseStart_2937418 : Nat := 118140960795 + 2937418 * 2 ^ 59
def prefixEnd_2937418 : Nat := 4983230072969 + 3 ^ 40 * 2937418 * 2
def baseEnd_2937418 : Nat := 1508307317168693572266067

theorem tailTrace_2937418 : CollatzResearch.WordTrace tailWord_2937418 prefixEnd_2937418 1508307317168693572266067 := by
  unfold tailWord_2937418
  simp only [CollatzResearch.WordTrace]
  refine ⟨26784109018060932974859227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71424290714829154599624605 26784109018060932974859227)
  ·
    refine ⟨40176163527091399462288841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26784109018060932974859227 40176163527091399462288841)
    ·
      refine ⟨30132122645318549596716631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40176163527091399462288841 30132122645318549596716631)
      ·
        refine ⟨45198183967977824395074947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30132122645318549596716631 45198183967977824395074947)
        ·
          refine ⟨67797275951966736592612421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45198183967977824395074947 67797275951966736592612421)
          ·
            refine ⟨12711989240993763111114829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67797275951966736592612421 12711989240993763111114829)
            ·
              refine ⟨4766995965372661166668061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12711989240993763111114829 4766995965372661166668061)
              ·
                refine ⟨1787623487014747937500523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4766995965372661166668061 1787623487014747937500523)
                ·
                  refine ⟨2681435230522121906250785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1787623487014747937500523 2681435230522121906250785)
                  ·
                    refine ⟨2011076422891591429688089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2681435230522121906250785 2011076422891591429688089)
                    ·
                      refine ⟨1508307317168693572266067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2011076422891591429688089 1508307317168693572266067)
                      ·
                        rfl

theorem cell23_2937418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 3, 1, 2, 2].length) (baseStart_2937418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937418 prefixEnd_2937418 := by exact prefixLift 2937418
  have htrace : WordTrace (prefixWord ++ tailWord_2937418) baseStart_2937418 baseEnd_2937418 := by
    simpa [prefixWord, tailWord_2937418, baseEnd_2937418] using wordTrace_append hprefix tailTrace_2937418
  have hstable : (prefixWord ++ tailWord_2937418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937418).length < 2 ^ (prefixWord ++ tailWord_2937418).sum := by decide
  have hdescent : baseEnd_2937418 < baseStart_2937418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937421 : List Nat := [1, 6, 1, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_2937421 : Nat := 118140960795 + 2937421 * 2 ^ 59
def prefixEnd_2937421 : Nat := 4983230072969 + 3 ^ 40 * 2937421 * 2
def baseEnd_2937421 : Nat := 1508308857610657060528553

theorem tailTrace_2937421 : CollatzResearch.WordTrace tailWord_2937421 prefixEnd_2937421 1508308857610657060528553 := by
  unfold tailWord_2937421
  simp only [CollatzResearch.WordTrace]
  refine ⟨107136545491232863411796117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71424363660821908941197411 107136545491232863411796117)
  ·
    refine ⟨5022025569901540472427943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 107136545491232863411796117 5022025569901540472427943)
    ·
      refine ⟨7533038354852310708641915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5022025569901540472427943 7533038354852310708641915)
      ·
        refine ⟨11299557532278466062962873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7533038354852310708641915 11299557532278466062962873)
        ·
          refine ⟨8474668149208849547222155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11299557532278466062962873 8474668149208849547222155)
          ·
            refine ⟨12712002223813274320833233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8474668149208849547222155 12712002223813274320833233)
            ·
              refine ⟨9534001667859955740624925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12712002223813274320833233 9534001667859955740624925)
              ·
                refine ⟨3575250625447483402734347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9534001667859955740624925 3575250625447483402734347)
                ·
                  refine ⟨5362875938171225104101521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3575250625447483402734347 5362875938171225104101521)
                  ·
                    refine ⟨4022156953628418828076141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5362875938171225104101521 4022156953628418828076141)
                    ·
                      refine ⟨1508308857610657060528553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4022156953628418828076141 1508308857610657060528553)
                      ·
                        rfl

theorem cell23_2937421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_2937421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937421 prefixEnd_2937421 := by exact prefixLift 2937421
  have htrace : WordTrace (prefixWord ++ tailWord_2937421) baseStart_2937421 baseEnd_2937421 := by
    simpa [prefixWord, tailWord_2937421, baseEnd_2937421] using wordTrace_append hprefix tailTrace_2937421
  have hstable : (prefixWord ++ tailWord_2937421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937421).length < 2 ^ (prefixWord ++ tailWord_2937421).sum := by decide
  have hdescent : baseEnd_2937421 < baseStart_2937421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937444 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 3, 3, 2]
def baseStart_2937444 : Nat := 118140960795 + 2937444 * 2 ^ 59
def prefixEnd_2937444 : Nat := 4983230072969 + 3 ^ 40 * 2937444 * 2
def baseEnd_2937444 : Nat := 1508320667665710470540947

theorem tailTrace_2937444 : CollatzResearch.WordTrace tailWord_2937444 prefixEnd_2937444 1508320667665710470540947 := by
  unfold tailWord_2937444
  simp only [CollatzResearch.WordTrace]
  refine ⟨53568692185074769169941693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71424922913433025559922257 53568692185074769169941693)
  ·
    refine ⟨20088259569403038438728135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53568692185074769169941693 20088259569403038438728135)
    ·
      refine ⟨30132389354104557658092203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20088259569403038438728135 30132389354104557658092203)
      ·
        refine ⟨45198584031156836487138305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30132389354104557658092203 45198584031156836487138305)
        ·
          refine ⟨33898938023367627365353729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45198584031156836487138305 33898938023367627365353729)
          ·
            refine ⟨25424203517525720524015297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33898938023367627365353729 25424203517525720524015297)
            ·
              refine ⟨19068152638144290393011473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25424203517525720524015297 19068152638144290393011473)
              ·
                refine ⟨14301114478608217794758605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19068152638144290393011473 14301114478608217794758605)
                ·
                  refine ⟨5362917929478081673034477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14301114478608217794758605 5362917929478081673034477)
                  ·
                    refine ⟨2011094223554280627387929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5362917929478081673034477 2011094223554280627387929)
                    ·
                      refine ⟨1508320667665710470540947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2011094223554280627387929 1508320667665710470540947)
                      ·
                        rfl

theorem cell23_2937444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 3, 3, 2].length) (baseStart_2937444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937444 prefixEnd_2937444 := by exact prefixLift 2937444
  have htrace : WordTrace (prefixWord ++ tailWord_2937444) baseStart_2937444 baseEnd_2937444 := by
    simpa [prefixWord, tailWord_2937444, baseEnd_2937444] using wordTrace_append hprefix tailTrace_2937444
  have hstable : (prefixWord ++ tailWord_2937444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937444).length < 2 ^ (prefixWord ++ tailWord_2937444).sum := by decide
  have hdescent : baseEnd_2937444 < baseStart_2937444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937477 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 2, 1, 5]
def baseStart_2937477 : Nat := 118140960795 + 2937477 * 2 ^ 59
def prefixEnd_2937477 : Nat := 4983230072969 + 3 ^ 40 * 2937477 * 2
def baseEnd_2937477 : Nat := 1508337612527308841428295

theorem tailTrace_2937477 : CollatzResearch.WordTrace tailWord_2937477 prefixEnd_2937477 1508337612527308841428295 := by
  unfold tailWord_2937477
  simp only [CollatzResearch.WordTrace]
  refine ⟨107138587979029984975834685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71425725319353323317223123 107138587979029984975834685)
  ·
    refine ⟨40176970492136244365938007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107138587979029984975834685 40176970492136244365938007)
    ·
      refine ⟨60265455738204366548907011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40176970492136244365938007 60265455738204366548907011)
      ·
        refine ⟨90398183607306549823360517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60265455738204366548907011 90398183607306549823360517)
        ·
          refine ⟨16949659426369978091880097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90398183607306549823360517 16949659426369978091880097)
          ·
            refine ⟨12712244569777483568910073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16949659426369978091880097 12712244569777483568910073)
            ·
              refine ⟨9534183427333112676682555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12712244569777483568910073 9534183427333112676682555)
              ·
                refine ⟨14301275140999669015023833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9534183427333112676682555 14301275140999669015023833)
                ·
                  refine ⟨10725956355749751761267875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14301275140999669015023833 10725956355749751761267875)
                  ·
                    refine ⟨16088934533624627641901813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10725956355749751761267875 16088934533624627641901813)
                    ·
                      refine ⟨1508337612527308841428295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16088934533624627641901813 1508337612527308841428295)
                      ·
                        rfl

theorem cell23_2937477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_2937477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937477 prefixEnd_2937477 := by exact prefixLift 2937477
  have htrace : WordTrace (prefixWord ++ tailWord_2937477) baseStart_2937477 baseEnd_2937477 := by
    simpa [prefixWord, tailWord_2937477, baseEnd_2937477] using wordTrace_append hprefix tailTrace_2937477
  have hstable : (prefixWord ++ tailWord_2937477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937477).length < 2 ^ (prefixWord ++ tailWord_2937477).sum := by decide
  have hdescent : baseEnd_2937477 < baseStart_2937477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937504 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 4]
def baseStart_2937504 : Nat := 118140960795 + 2937504 * 2 ^ 59
def prefixEnd_2937504 : Nat := 4983230072969 + 3 ^ 40 * 2937504 * 2
def baseEnd_2937504 : Nat := 1508351476504980235790671

theorem tailTrace_2937504 : CollatzResearch.WordTrace tailWord_2937504 prefixEnd_2937504 1508351476504980235790671 := by
  unfold tailWord_2937504
  simp only [CollatzResearch.WordTrace]
  refine ⟨53569786374966084293533783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71426381833288112391378377 53569786374966084293533783)
  ·
    refine ⟨80354679562449126440300675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53569786374966084293533783 80354679562449126440300675)
    ·
      refine ⟨120532019343673689660451013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80354679562449126440300675 120532019343673689660451013)
      ·
        refine ⟨22599753626938816811334565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120532019343673689660451013 22599753626938816811334565)
        ·
          refine ⟨4237453805051028152125231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22599753626938816811334565 4237453805051028152125231)
          ·
            refine ⟨6356180707576542228187847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4237453805051028152125231 6356180707576542228187847)
            ·
              refine ⟨9534271061364813342281771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6356180707576542228187847 9534271061364813342281771)
              ·
                refine ⟨14301406592047220013422657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9534271061364813342281771 14301406592047220013422657)
                ·
                  refine ⟨10726054944035415010066993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14301406592047220013422657 10726054944035415010066993)
                  ·
                    refine ⟨8044541208026561257550245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10726054944035415010066993 8044541208026561257550245)
                    ·
                      refine ⟨1508351476504980235790671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8044541208026561257550245 1508351476504980235790671)
                      ·
                        rfl

theorem cell23_2937504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_2937504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937504 prefixEnd_2937504 := by exact prefixLift 2937504
  have htrace : WordTrace (prefixWord ++ tailWord_2937504) baseStart_2937504 baseEnd_2937504 := by
    simpa [prefixWord, tailWord_2937504, baseEnd_2937504] using wordTrace_append hprefix tailTrace_2937504
  have hstable : (prefixWord ++ tailWord_2937504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937504).length < 2 ^ (prefixWord ++ tailWord_2937504).sum := by decide
  have hdescent : baseEnd_2937504 < baseStart_2937504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937542 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_2937542 : Nat := 118140960795 + 2937542 * 2 ^ 59
def prefixEnd_2937542 : Nat := 4983230072969 + 3 ^ 40 * 2937542 * 2
def baseEnd_2937542 : Nat := 1508370988769851087115497

theorem tailTrace_2937542 : CollatzResearch.WordTrace tailWord_2937542 prefixEnd_2937542 1508370988769851087115497 := by
  unfold tailWord_2937542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3348154960118578158654715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71427305815863000717967253 3348154960118578158654715)
  ·
    refine ⟨5022232440177867237982073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3348154960118578158654715 5022232440177867237982073)
    ·
      refine ⟨3766674330133400428486555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5022232440177867237982073 3766674330133400428486555)
      ·
        refine ⟨5650011495200100642729833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3766674330133400428486555 5650011495200100642729833)
        ·
          refine ⟨4237508621400075482047375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5650011495200100642729833 4237508621400075482047375)
          ·
            refine ⟨6356262932100113223071063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4237508621400075482047375 6356262932100113223071063)
            ·
              refine ⟨9534394398150169834606595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6356262932100113223071063 9534394398150169834606595)
              ·
                refine ⟨14301591597225254751909893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9534394398150169834606595 14301591597225254751909893)
                ·
                  refine ⟨2681548424479735265983105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14301591597225254751909893 2681548424479735265983105)
                  ·
                    refine ⟨2011161318359801449487329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2681548424479735265983105 2011161318359801449487329)
                    ·
                      refine ⟨1508370988769851087115497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2011161318359801449487329 1508370988769851087115497)
                      ·
                        rfl

theorem cell23_2937542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_2937542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937542 prefixEnd_2937542 := by exact prefixLift 2937542
  have htrace : WordTrace (prefixWord ++ tailWord_2937542) baseStart_2937542 baseEnd_2937542 := by
    simpa [prefixWord, tailWord_2937542, baseEnd_2937542] using wordTrace_append hprefix tailTrace_2937542
  have hstable : (prefixWord ++ tailWord_2937542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937542).length < 2 ^ (prefixWord ++ tailWord_2937542).sum := by decide
  have hdescent : baseEnd_2937542 < baseStart_2937542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937584 : List Nat := [2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 3]
def baseStart_2937584 : Nat := 118140960795 + 2937584 * 2 ^ 59
def prefixEnd_2937584 : Nat := 4983230072969 + 3 ^ 40 * 2937584 * 2
def baseEnd_2937584 : Nat := 1508392554957339922790303

theorem tailTrace_2937584 : CollatzResearch.WordTrace tailWord_2937584 prefixEnd_2937584 1508392554957339922790303 := by
  unfold tailWord_2937584
  simp only [CollatzResearch.WordTrace]
  refine ⟨53571245294821171124989903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71428327059761561499986537 53571245294821171124989903)
  ·
    refine ⟨80356867942231756687484855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53571245294821171124989903 80356867942231756687484855)
    ·
      refine ⟨120535301913347635031227283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80356867942231756687484855 120535301913347635031227283)
      ·
        refine ⟨180802952870021452546840925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120535301913347635031227283 180802952870021452546840925)
        ·
          refine ⟨67801107326258044705065347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180802952870021452546840925 67801107326258044705065347)
          ·
            refine ⟨101701660989387067057598021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67801107326258044705065347 101701660989387067057598021)
            ·
              refine ⟨19069061435510075073299629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101701660989387067057598021 19069061435510075073299629)
              ·
                refine ⟨7150898038316278152487361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19069061435510075073299629 7150898038316278152487361)
                ·
                  refine ⟨5363173528737208614365521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7150898038316278152487361 5363173528737208614365521)
                  ·
                    refine ⟨4022380146552906460774141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5363173528737208614365521 4022380146552906460774141)
                    ·
                      refine ⟨1508392554957339922790303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4022380146552906460774141 1508392554957339922790303)
                      ·
                        rfl

theorem cell23_2937584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 3].length) (baseStart_2937584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937584 prefixEnd_2937584 := by exact prefixLift 2937584
  have htrace : WordTrace (prefixWord ++ tailWord_2937584) baseStart_2937584 baseEnd_2937584 := by
    simpa [prefixWord, tailWord_2937584, baseEnd_2937584] using wordTrace_append hprefix tailTrace_2937584
  have hstable : (prefixWord ++ tailWord_2937584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937584).length < 2 ^ (prefixWord ++ tailWord_2937584).sum := by decide
  have hdescent : baseEnd_2937584 < baseStart_2937584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937604 : List Nat := [2, 3, 2, 2, 1, 1, 2, 4, 6]
def baseStart_2937604 : Nat := 118140960795 + 2937604 * 2 ^ 59
def prefixEnd_2937604 : Nat := 4983230072969 + 3 ^ 40 * 2937604 * 2
def baseEnd_2937604 : Nat := 167600313841158871615579

theorem tailTrace_2937604 : CollatzResearch.WordTrace tailWord_2937604 prefixEnd_2937604 167600313841158871615579 := by
  unfold tailWord_2937604
  simp only [CollatzResearch.WordTrace]
  refine ⟨53571610024784942832853933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71428813366379923777138577 53571610024784942832853933)
  ·
    refine ⟨20089353759294353562320225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53571610024784942832853933 20089353759294353562320225)
    ·
      refine ⟨15067015319470765171740169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20089353759294353562320225 15067015319470765171740169)
      ·
        refine ⟨11300261489603073878805127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15067015319470765171740169 11300261489603073878805127)
        ·
          refine ⟨16950392234404610818207691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11300261489603073878805127 16950392234404610818207691)
          ·
            refine ⟨25425588351606916227311537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16950392234404610818207691 25425588351606916227311537)
            ·
              refine ⟨19069191263705187170483653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25425588351606916227311537 19069191263705187170483653)
              ·
                refine ⟨3575473361944722594465685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19069191263705187170483653 3575473361944722594465685)
                ·
                  refine ⟨167600313841158871615579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3575473361944722594465685 167600313841158871615579)
                  ·
                    rfl

theorem cell23_2937604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 6].length) (baseStart_2937604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937604 prefixEnd_2937604 := by exact prefixLift 2937604
  have htrace : WordTrace (prefixWord ++ tailWord_2937604) baseStart_2937604 baseEnd_2937604 := by
    simpa [prefixWord, tailWord_2937604, baseEnd_2937604] using wordTrace_append hprefix tailTrace_2937604
  have hstable : (prefixWord ++ tailWord_2937604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937604).length < 2 ^ (prefixWord ++ tailWord_2937604).sum := by decide
  have hdescent : baseEnd_2937604 < baseStart_2937604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937664 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 4, 4]
def baseStart_2937664 : Nat := 118140960795 + 2937664 * 2 ^ 59
def prefixEnd_2937664 : Nat := 4983230072969 + 3 ^ 40 * 2937664 * 2
def baseEnd_2937664 : Nat := 502811211136566536596645

theorem tailTrace_2937664 : CollatzResearch.WordTrace tailWord_2937664 prefixEnd_2937664 502811211136566536596645 := by
  unfold tailWord_2937664
  simp only [CollatzResearch.WordTrace]
  refine ⟨53572704214676257956446023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71430272286235010608594697 53572704214676257956446023)
  ·
    refine ⟨80359056322014386934669035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53572704214676257956446023 80359056322014386934669035)
    ·
      refine ⟨120538584483021580402003553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80359056322014386934669035 120538584483021580402003553)
      ·
        refine ⟨90403938362266185301502665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120538584483021580402003553 90403938362266185301502665)
        ·
          refine ⟨67802953771699638976126999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90403938362266185301502665 67802953771699638976126999)
          ·
            refine ⟨101704430657549458464190499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67802953771699638976126999 101704430657549458464190499)
            ·
              refine ⟨152556645986324187696285749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101704430657549458464190499 152556645986324187696285749)
              ·
                refine ⟨14302185561217892596526789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152556645986324187696285749 14302185561217892596526789)
                ·
                  refine ⟨2681659792728354861848773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14302185561217892596526789 2681659792728354861848773)
                  ·
                    refine ⟨502811211136566536596645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2681659792728354861848773 502811211136566536596645)
                    ·
                      rfl

theorem cell23_2937664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 4, 4].length) (baseStart_2937664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937664 prefixEnd_2937664 := by exact prefixLift 2937664
  have htrace : WordTrace (prefixWord ++ tailWord_2937664) baseStart_2937664 baseEnd_2937664 := by
    simpa [prefixWord, tailWord_2937664, baseEnd_2937664] using wordTrace_append hprefix tailTrace_2937664
  have hstable : (prefixWord ++ tailWord_2937664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937664).length < 2 ^ (prefixWord ++ tailWord_2937664).sum := by decide
  have hdescent : baseEnd_2937664 < baseStart_2937664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937681 : List Nat := [1, 2, 2, 1, 6, 1, 2, 1, 1, 6]
def baseStart_2937681 : Nat := 118140960795 + 2937681 * 2 ^ 59
def prefixEnd_2937681 : Nat := 4983230072969 + 3 ^ 40 * 2937681 * 2
def baseEnd_2937681 : Nat := 502814120860275347759119

theorem tailTrace_2937681 : CollatzResearch.WordTrace tailWord_2937681 prefixEnd_2937681 502814120860275347759119 := by
  unfold tailWord_2937681
  simp only [CollatzResearch.WordTrace]
  refine ⟨107146028470290927816260897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71430685646860618544173931 107146028470290927816260897)
  ·
    refine ⟨80359521352718195862195673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107146028470290927816260897 80359521352718195862195673)
    ·
      refine ⟨60269641014538646896646755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80359521352718195862195673 60269641014538646896646755)
      ·
        refine ⟨90404461521807970344970133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60269641014538646896646755 90404461521807970344970133)
        ·
          refine ⟨4237709133834748609920475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90404461521807970344970133 4237709133834748609920475)
          ·
            refine ⟨6356563700752122914880713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4237709133834748609920475 6356563700752122914880713)
            ·
              refine ⟨4767422775564092186160535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6356563700752122914880713 4767422775564092186160535)
              ·
                refine ⟨7151134163346138279240803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4767422775564092186160535 7151134163346138279240803)
                ·
                  refine ⟨10726701245019207418861205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7151134163346138279240803 10726701245019207418861205)
                  ·
                    refine ⟨502814120860275347759119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10726701245019207418861205 502814120860275347759119)
                    ·
                      rfl

theorem cell23_2937681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_2937681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937681 prefixEnd_2937681 := by exact prefixLift 2937681
  have htrace : WordTrace (prefixWord ++ tailWord_2937681) baseStart_2937681 baseEnd_2937681 := by
    simpa [prefixWord, tailWord_2937681, baseEnd_2937681] using wordTrace_append hprefix tailTrace_2937681
  have hstable : (prefixWord ++ tailWord_2937681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937681).length < 2 ^ (prefixWord ++ tailWord_2937681).sum := by decide
  have hdescent : baseEnd_2937681 < baseStart_2937681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937738 : List Nat := [3, 1, 2, 4, 1, 1, 3, 1, 1, 3, 3]
def baseStart_2937738 : Nat := 118140960795 + 2937738 * 2 ^ 59
def prefixEnd_2937738 : Nat := 4983230072969 + 3 ^ 40 * 2937738 * 2
def baseEnd_2937738 : Nat := 1508471630978132320264595

theorem tailTrace_2937738 : CollatzResearch.WordTrace tailWord_2937738 prefixEnd_2937738 1508471630978132320264595 := by
  unfold tailWord_2937738
  simp only [CollatzResearch.WordTrace]
  refine ⟨26787026857771106637771467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71432071620722951034057245 26787026857771106637771467)
  ·
    refine ⟨40180540286656659956657201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26787026857771106637771467 40180540286656659956657201)
    ·
      refine ⟨30135405214992494967492901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40180540286656659956657201 30135405214992494967492901)
      ·
        refine ⟨5650388477811092806404919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30135405214992494967492901 5650388477811092806404919)
        ·
          refine ⟨8475582716716639209607379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5650388477811092806404919 8475582716716639209607379)
          ·
            refine ⟨12713374075074958814411069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8475582716716639209607379 12713374075074958814411069)
            ·
              refine ⟨4767515278153109555404151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12713374075074958814411069 4767515278153109555404151)
              ·
                refine ⟨7151272917229664333106227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4767515278153109555404151 7151272917229664333106227)
                ·
                  refine ⟨10726909375844496499659341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7151272917229664333106227 10726909375844496499659341)
                  ·
                    refine ⟨4022591015941686187372253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10726909375844496499659341 4022591015941686187372253)
                    ·
                      refine ⟨1508471630978132320264595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4022591015941686187372253 1508471630978132320264595)
                      ·
                        rfl

theorem cell23_2937738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_2937738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937738 prefixEnd_2937738 := by exact prefixLift 2937738
  have htrace : WordTrace (prefixWord ++ tailWord_2937738) baseStart_2937738 baseEnd_2937738 := by
    simpa [prefixWord, tailWord_2937738, baseEnd_2937738] using wordTrace_append hprefix tailTrace_2937738
  have hstable : (prefixWord ++ tailWord_2937738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937738).length < 2 ^ (prefixWord ++ tailWord_2937738).sum := by decide
  have hdescent : baseEnd_2937738 < baseStart_2937738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937756 : List Nat := [2, 2, 3, 3, 3, 1, 1, 3, 1, 2, 2]
def baseStart_2937756 : Nat := 118140960795 + 2937756 * 2 ^ 59
def prefixEnd_2937756 : Nat := 4983230072969 + 3 ^ 40 * 2937756 * 2
def baseEnd_2937756 : Nat := 1508480873629913249839513

theorem tailTrace_2937756 : CollatzResearch.WordTrace tailWord_2937756 prefixEnd_2937756 1508480873629913249839513 := by
  unfold tailWord_2937756
  simp only [CollatzResearch.WordTrace]
  refine ⟨53574381972509607812620561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71432509296679477083494081 53574381972509607812620561)
  ·
    refine ⟨40180786479382205859465421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53574381972509607812620561 40180786479382205859465421)
    ·
      refine ⟨15067794929768327197299533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40180786479382205859465421 15067794929768327197299533)
      ·
        refine ⟨5650423098663122698987325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15067794929768327197299533 5650423098663122698987325)
        ·
          refine ⟨2118908661998671012120247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5650423098663122698987325 2118908661998671012120247)
          ·
            refine ⟨3178362992998006518180371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118908661998671012120247 3178362992998006518180371)
            ·
              refine ⟨4767544489497009777270557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3178362992998006518180371 4767544489497009777270557)
              ·
                refine ⟨1787829183561378666476459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4767544489497009777270557 1787829183561378666476459)
                ·
                  refine ⟨2681743775342067999714689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1787829183561378666476459 2681743775342067999714689)
                  ·
                    refine ⟨2011307831506550999786017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2681743775342067999714689 2011307831506550999786017)
                    ·
                      refine ⟨1508480873629913249839513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2011307831506550999786017 1508480873629913249839513)
                      ·
                        rfl

theorem cell23_2937756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_2937756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937756 prefixEnd_2937756 := by exact prefixLift 2937756
  have htrace : WordTrace (prefixWord ++ tailWord_2937756) baseStart_2937756 baseEnd_2937756 := by
    simpa [prefixWord, tailWord_2937756, baseEnd_2937756] using wordTrace_append hprefix tailTrace_2937756
  have hstable : (prefixWord ++ tailWord_2937756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937756).length < 2 ^ (prefixWord ++ tailWord_2937756).sum := by decide
  have hdescent : baseEnd_2937756 < baseStart_2937756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937781 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_2937781 : Nat := 118140960795 + 2937781 * 2 ^ 59
def prefixEnd_2937781 : Nat := 4983230072969 + 3 ^ 40 * 2937781 * 2
def baseEnd_2937781 : Nat := 1508493710646275652026897

theorem tailTrace_2937781 : CollatzResearch.WordTrace tailWord_2937781 prefixEnd_2937781 1508493710646275652026897 := by
  unfold tailWord_2937781
  simp only [CollatzResearch.WordTrace]
  refine ⟨107149675769928644894901197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71433117179952429929934131 107149675769928644894901197)
  ·
    refine ⟨40181128413723241835587949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107149675769928644894901197 40181128413723241835587949)
    ·
      refine ⟨15067923155146215688345481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40181128413723241835587949 15067923155146215688345481)
      ·
        refine ⟨11300942366359661766259111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15067923155146215688345481 11300942366359661766259111)
        ·
          refine ⟨16951413549539492649388667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11300942366359661766259111 16951413549539492649388667)
          ·
            refine ⟨25427120324309238974083001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16951413549539492649388667 25427120324309238974083001)
            ·
              refine ⟨19070340243231929230562251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25427120324309238974083001 19070340243231929230562251)
              ·
                refine ⟨28605510364847893845843377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19070340243231929230562251 28605510364847893845843377)
                ·
                  refine ⟨21454132773635920384382533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28605510364847893845843377 21454132773635920384382533)
                  ·
                    refine ⟨4022649895056735072071725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21454132773635920384382533 4022649895056735072071725)
                    ·
                      refine ⟨1508493710646275652026897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4022649895056735072071725 1508493710646275652026897)
                      ·
                        rfl

theorem cell23_2937781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_2937781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937781 prefixEnd_2937781 := by exact prefixLift 2937781
  have htrace : WordTrace (prefixWord ++ tailWord_2937781) baseStart_2937781 baseEnd_2937781 := by
    simpa [prefixWord, tailWord_2937781, baseEnd_2937781] using wordTrace_append hprefix tailTrace_2937781
  have hstable : (prefixWord ++ tailWord_2937781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937781).length < 2 ^ (prefixWord ++ tailWord_2937781).sum := by decide
  have hdescent : baseEnd_2937781 < baseStart_2937781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937789 : List Nat := [1, 4, 1, 2, 5, 1, 2, 1, 2, 1, 3]
def baseStart_2937789 : Nat := 118140960795 + 2937789 * 2 ^ 59
def prefixEnd_2937789 : Nat := 4983230072969 + 3 ^ 40 * 2937789 * 2
def baseEnd_2937789 : Nat := 1508497818491511620726861

theorem tailTrace_2937789 : CollatzResearch.WordTrace tailWord_2937789 prefixEnd_2937789 1508497818491511620726861 := by
  unfold tailWord_2937789
  simp only [CollatzResearch.WordTrace]
  refine ⟨107149967553899662261192421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71433311702599774840794947 107149967553899662261192421)
  ·
    refine ⟨20090618916356186673973579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107149967553899662261192421 20090618916356186673973579)
    ·
      refine ⟨30135928374534280010960369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20090618916356186673973579 30135928374534280010960369)
      ·
        refine ⟨22601946280900710008220277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30135928374534280010960369 22601946280900710008220277)
        ·
          refine ⟨2118932463834441563270651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22601946280900710008220277 2118932463834441563270651)
          ·
            refine ⟨3178398695751662344905977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118932463834441563270651 3178398695751662344905977)
            ·
              refine ⟨2383799021813746758679483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3178398695751662344905977 2383799021813746758679483)
              ·
                refine ⟨3575698532720620138019225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2383799021813746758679483 3575698532720620138019225)
                ·
                  refine ⟨2681773899540465103514419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3575698532720620138019225 2681773899540465103514419)
                  ·
                    refine ⟨4022660849310697655271629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2681773899540465103514419 4022660849310697655271629)
                    ·
                      refine ⟨1508497818491511620726861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4022660849310697655271629 1508497818491511620726861)
                      ·
                        rfl

theorem cell23_2937789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_2937789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937789 prefixEnd_2937789 := by exact prefixLift 2937789
  have htrace : WordTrace (prefixWord ++ tailWord_2937789) baseStart_2937789 baseEnd_2937789 := by
    simpa [prefixWord, tailWord_2937789, baseEnd_2937789] using wordTrace_append hprefix tailTrace_2937789
  have hstable : (prefixWord ++ tailWord_2937789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937789).length < 2 ^ (prefixWord ++ tailWord_2937789).sum := by decide
  have hdescent : baseEnd_2937789 < baseStart_2937789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937829 : List Nat := [1, 3, 1, 6, 1, 1, 2, 2, 2, 2, 2]
def baseStart_2937829 : Nat := 118140960795 + 2937829 * 2 ^ 59
def prefixEnd_2937829 : Nat := 4983230072969 + 3 ^ 40 * 2937829 * 2
def baseEnd_2937829 : Nat := 1508518357717691464226677

theorem tailTrace_2937829 : CollatzResearch.WordTrace tailWord_2937829 prefixEnd_2937829 1508518357717691464226677 := by
  unfold tailWord_2937829
  simp only [CollatzResearch.WordTrace]
  refine ⟨107151426473754749092648541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71434284315836499395099027 107151426473754749092648541)
  ·
    refine ⟨40181784927658030909743203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107151426473754749092648541 40181784927658030909743203)
    ·
      refine ⟨60272677391487046364614805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40181784927658030909743203 60272677391487046364614805)
      ·
        refine ⟨2825281752725955298341319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60272677391487046364614805 2825281752725955298341319)
        ·
          refine ⟨4237922629088932947511979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2825281752725955298341319 4237922629088932947511979)
          ·
            refine ⟨6356883943633399421267969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4237922629088932947511979 6356883943633399421267969)
            ·
              refine ⟨4767662957725049565950977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6356883943633399421267969 4767662957725049565950977)
              ·
                refine ⟨3575747218293787174463233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4767662957725049565950977 3575747218293787174463233)
                ·
                  refine ⟨2681810413720340380847425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3575747218293787174463233 2681810413720340380847425)
                  ·
                    refine ⟨2011357810290255285635569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2681810413720340380847425 2011357810290255285635569)
                    ·
                      refine ⟨1508518357717691464226677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2011357810290255285635569 1508518357717691464226677)
                      ·
                        rfl

theorem cell23_2937829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_2937829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937829 prefixEnd_2937829 := by exact prefixLift 2937829
  have htrace : WordTrace (prefixWord ++ tailWord_2937829) baseStart_2937829 baseEnd_2937829 := by
    simpa [prefixWord, tailWord_2937829, baseEnd_2937829] using wordTrace_append hprefix tailTrace_2937829
  have hstable : (prefixWord ++ tailWord_2937829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937829).length < 2 ^ (prefixWord ++ tailWord_2937829).sum := by decide
  have hdescent : baseEnd_2937829 < baseStart_2937829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937841 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 1, 2, 5]
def baseStart_2937841 : Nat := 118140960795 + 2937841 * 2 ^ 59
def prefixEnd_2937841 : Nat := 4983230072969 + 3 ^ 40 * 2937841 * 2
def baseEnd_2937841 : Nat := 1508524519485545417276621

theorem tailTrace_2937841 : CollatzResearch.WordTrace tailWord_2937841 prefixEnd_2937841 1508524519485545417276621 := by
  unfold tailWord_2937841
  simp only [CollatzResearch.WordTrace]
  refine ⟨107151864149711275142085377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71434576099807516761390251 107151864149711275142085377)
  ·
    refine ⟨80363898112283456356564033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107151864149711275142085377 80363898112283456356564033)
    ·
      refine ⟨60272923584212592267423025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80363898112283456356564033 60272923584212592267423025)
      ·
        refine ⟨45204692688159444200567269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60272923584212592267423025 45204692688159444200567269)
        ·
          refine ⟨8475879879029895787606363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45204692688159444200567269 8475879879029895787606363)
          ·
            refine ⟨12713819818544843681409545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8475879879029895787606363 12713819818544843681409545)
            ·
              refine ⟨9535364863908632761057159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12713819818544843681409545 9535364863908632761057159)
              ·
                refine ⟨14303047295862949141585739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9535364863908632761057159 14303047295862949141585739)
                ·
                  refine ⟨21454570943794423712378609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14303047295862949141585739 21454570943794423712378609)
                  ·
                    refine ⟨16090928207845817784283957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21454570943794423712378609 16090928207845817784283957)
                    ·
                      refine ⟨1508524519485545417276621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16090928207845817784283957 1508524519485545417276621)
                      ·
                        rfl

theorem cell23_2937841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_2937841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937841 prefixEnd_2937841 := by exact prefixLift 2937841
  have htrace : WordTrace (prefixWord ++ tailWord_2937841) baseStart_2937841 baseEnd_2937841 := by
    simpa [prefixWord, tailWord_2937841, baseEnd_2937841] using wordTrace_append hprefix tailTrace_2937841
  have hstable : (prefixWord ++ tailWord_2937841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937841).length < 2 ^ (prefixWord ++ tailWord_2937841).sum := by decide
  have hdescent : baseEnd_2937841 < baseStart_2937841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937868 : List Nat := [2, 2, 1, 2, 3, 2, 3, 1, 2, 1, 4]
def baseStart_2937868 : Nat := 118140960795 + 2937868 * 2 ^ 59
def prefixEnd_2937868 : Nat := 4983230072969 + 3 ^ 40 * 2937868 * 2
def baseEnd_2937868 : Nat := 1508538383463216811638997

theorem tailTrace_2937868 : CollatzResearch.WordTrace tailWord_2937868 prefixEnd_2937868 1508538383463216811638997 := by
  unfold tailWord_2937868
  simp only [CollatzResearch.WordTrace]
  refine ⟨53576424460306729376659129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71435232613742305835545505 53576424460306729376659129)
  ·
    refine ⟨40182318345230047032494347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53576424460306729376659129 40182318345230047032494347)
    ·
      refine ⟨60273477517845070548741521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40182318345230047032494347 60273477517845070548741521)
      ·
        refine ⟨45205108138383802911556141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60273477517845070548741521 45205108138383802911556141)
        ·
          refine ⟨16951915551893926091833553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45205108138383802911556141 16951915551893926091833553)
          ·
            refine ⟨12713936663920444568875165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16951915551893926091833553 12713936663920444568875165)
            ·
              refine ⟨4767726248970166713328187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12713936663920444568875165 4767726248970166713328187)
              ·
                refine ⟨7151589373455250069992281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4767726248970166713328187 7151589373455250069992281)
                ·
                  refine ⟨5363692030091437552494211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7151589373455250069992281 5363692030091437552494211)
                  ·
                    refine ⟨8045538045137156328741317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5363692030091437552494211 8045538045137156328741317)
                    ·
                      refine ⟨1508538383463216811638997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8045538045137156328741317 1508538383463216811638997)
                      ·
                        rfl

theorem cell23_2937868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_2937868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937868 prefixEnd_2937868 := by exact prefixLift 2937868
  have htrace : WordTrace (prefixWord ++ tailWord_2937868) baseStart_2937868 baseEnd_2937868 := by
    simpa [prefixWord, tailWord_2937868, baseEnd_2937868] using wordTrace_append hprefix tailTrace_2937868
  have hstable : (prefixWord ++ tailWord_2937868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937868).length < 2 ^ (prefixWord ++ tailWord_2937868).sum := by decide
  have hdescent : baseEnd_2937868 < baseStart_2937868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937871 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 3]
def baseStart_2937871 : Nat := 118140960795 + 2937871 * 2 ^ 59
def prefixEnd_2937871 : Nat := 4983230072969 + 3 ^ 40 * 2937871 * 2
def baseEnd_2937871 : Nat := 1508539923905180299901483

theorem tailTrace_2937871 : CollatzResearch.WordTrace tailWord_2937871 prefixEnd_2937871 1508539923905180299901483 := by
  unfold tailWord_2937871
  simp only [CollatzResearch.WordTrace]
  refine ⟨107152958339602590265677467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71435305559735060177118311 107152958339602590265677467)
  ·
    refine ⟨160729437509403885398516201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107152958339602590265677467 160729437509403885398516201)
    ·
      refine ⟨120547078132052914048887151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160729437509403885398516201 120547078132052914048887151)
      ·
        refine ⟨180820617198079371073330727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120547078132052914048887151 180820617198079371073330727)
        ·
          refine ⟨271230925797119056609996091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180820617198079371073330727 271230925797119056609996091)
          ·
            refine ⟨406846388695678584914994137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 271230925797119056609996091 406846388695678584914994137)
            ·
              refine ⟨305134791521758938686245603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406846388695678584914994137 305134791521758938686245603)
              ·
                refine ⟨457702187282638408029368405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305134791521758938686245603 457702187282638408029368405)
                ·
                  refine ⟨5363697507218418844094161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 457702187282638408029368405 5363697507218418844094161)
                  ·
                    refine ⟨4022773130413814133070621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5363697507218418844094161 4022773130413814133070621)
                    ·
                      refine ⟨1508539923905180299901483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4022773130413814133070621 1508539923905180299901483)
                      ·
                        rfl

theorem cell23_2937871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 3].length) (baseStart_2937871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937871 prefixEnd_2937871 := by exact prefixLift 2937871
  have htrace : WordTrace (prefixWord ++ tailWord_2937871) baseStart_2937871 baseEnd_2937871 := by
    simpa [prefixWord, tailWord_2937871, baseEnd_2937871] using wordTrace_append hprefix tailTrace_2937871
  have hstable : (prefixWord ++ tailWord_2937871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937871).length < 2 ^ (prefixWord ++ tailWord_2937871).sum := by decide
  have hdescent : baseEnd_2937871 < baseStart_2937871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937891 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 8]
def baseStart_2937891 : Nat := 118140960795 + 2937891 * 2 ^ 59
def prefixEnd_2937891 : Nat := 4983230072969 + 3 ^ 40 * 2937891 * 2
def baseEnd_2937891 : Nat := 167616688168696691294599

theorem tailTrace_2937891 : CollatzResearch.WordTrace tailWord_2937891 prefixEnd_2937891 167616688168696691294599 := by
  unfold tailWord_2937891
  simp only [CollatzResearch.WordTrace]
  refine ⟨107153687799530133681405527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71435791866353422454270351 107153687799530133681405527)
  ·
    refine ⟨160730531699295200522108291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107153687799530133681405527 160730531699295200522108291)
    ·
      refine ⟨241095797548942800783162437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160730531699295200522108291 241095797548942800783162437)
      ·
        refine ⟨45205462040426775146842957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241095797548942800783162437 45205462040426775146842957)
        ·
          refine ⟨16952048265160040680066109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45205462040426775146842957 16952048265160040680066109)
          ·
            refine ⟨6357018099435015255024791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16952048265160040680066109 6357018099435015255024791)
            ·
              refine ⟨9535527149152522882537187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6357018099435015255024791 9535527149152522882537187)
              ·
                refine ⟨14303290723728784323805781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9535527149152522882537187 14303290723728784323805781)
                ·
                  refine ⟨167616688168696691294599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14303290723728784323805781 167616688168696691294599)
                  ·
                    rfl

theorem cell23_2937891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 8].length) (baseStart_2937891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937891 prefixEnd_2937891 := by exact prefixLift 2937891
  have htrace : WordTrace (prefixWord ++ tailWord_2937891) baseStart_2937891 baseEnd_2937891 := by
    simpa [prefixWord, tailWord_2937891, baseEnd_2937891] using wordTrace_append hprefix tailTrace_2937891
  have hstable : (prefixWord ++ tailWord_2937891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937891).length < 2 ^ (prefixWord ++ tailWord_2937891).sum := by decide
  have hdescent : baseEnd_2937891 < baseStart_2937891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937895 : List Nat := [1, 1, 7, 1, 1, 1, 1, 3, 3, 4]
def baseStart_2937895 : Nat := 118140960795 + 2937895 * 2 ^ 59
def prefixEnd_2937895 : Nat := 4983230072969 + 3 ^ 40 * 2937895 * 2
def baseEnd_2937895 : Nat := 502850749146962735333791

theorem tailTrace_2937895 : CollatzResearch.WordTrace tailWord_2937895 prefixEnd_2937895 502850749146962735333791 := by
  unfold tailWord_2937895
  simp only [CollatzResearch.WordTrace]
  refine ⟨107153833691515642364551139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71435889127677094909700759 107153833691515642364551139)
  ·
    refine ⟨160730750537273463546826709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107153833691515642364551139 160730750537273463546826709)
    ·
      refine ⟨3767126965717346801878751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 160730750537273463546826709 3767126965717346801878751)
      ·
        refine ⟨5650690448576020202818127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3767126965717346801878751 5650690448576020202818127)
        ·
          refine ⟨8476035672864030304227191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5650690448576020202818127 8476035672864030304227191)
          ·
            refine ⟨12714053509296045456340787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8476035672864030304227191 12714053509296045456340787)
            ·
              refine ⟨19071080263944068184511181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12714053509296045456340787 19071080263944068184511181)
              ·
                refine ⟨7151655098979025569191693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19071080263944068184511181 7151655098979025569191693)
                ·
                  refine ⟨2681870662117134588446885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7151655098979025569191693 2681870662117134588446885)
                  ·
                    refine ⟨502850749146962735333791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2681870662117134588446885 502850749146962735333791)
                    ·
                      rfl

theorem cell23_2937895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_2937895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937895 prefixEnd_2937895 := by exact prefixLift 2937895
  have htrace : WordTrace (prefixWord ++ tailWord_2937895) baseStart_2937895 baseEnd_2937895 := by
    simpa [prefixWord, tailWord_2937895, baseEnd_2937895] using wordTrace_append hprefix tailTrace_2937895
  have hstable : (prefixWord ++ tailWord_2937895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937895).length < 2 ^ (prefixWord ++ tailWord_2937895).sum := by decide
  have hdescent : baseEnd_2937895 < baseStart_2937895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937928 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 1, 5, 2]
def baseStart_2937928 : Nat := 118140960795 + 2937928 * 2 ^ 59
def prefixEnd_2937928 : Nat := 4983230072969 + 3 ^ 40 * 2937928 * 2
def baseEnd_2937928 : Nat := 1508569192302486576888721

theorem tailTrace_2937928 : CollatzResearch.WordTrace tailWord_2937928 prefixEnd_2937928 1508569192302486576888721 := by
  unfold tailWord_2937928
  simp only [CollatzResearch.WordTrace]
  refine ⟨53577518650198044500251219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71436691533597392667001625 53577518650198044500251219)
  ·
    refine ⟨80366277975297066750376829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53577518650198044500251219 80366277975297066750376829)
    ·
      refine ⟨30137354240736400031391311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80366277975297066750376829 30137354240736400031391311)
      ·
        refine ⟨45206031361104600047086967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30137354240736400031391311 45206031361104600047086967)
        ·
          refine ⟨67809047041656900070630451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45206031361104600047086967 67809047041656900070630451)
          ·
            refine ⟨101713570562485350105945677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67809047041656900070630451 101713570562485350105945677)
            ·
              refine ⟨38142588960932006289729629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101713570562485350105945677 38142588960932006289729629)
              ·
                refine ⟨14303470860349502358648611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38142588960932006289729629 14303470860349502358648611)
                ·
                  refine ⟨21455206290524253537972917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14303470860349502358648611 21455206290524253537972917)
                  ·
                    refine ⟨2011425589736648769184961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21455206290524253537972917 2011425589736648769184961)
                    ·
                      refine ⟨1508569192302486576888721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2011425589736648769184961 1508569192302486576888721)
                      ·
                        rfl

theorem cell23_2937928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_2937928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937928 prefixEnd_2937928 := by exact prefixLift 2937928
  have htrace : WordTrace (prefixWord ++ tailWord_2937928) baseStart_2937928 baseEnd_2937928 := by
    simpa [prefixWord, tailWord_2937928, baseEnd_2937928] using wordTrace_append hprefix tailTrace_2937928
  have hstable : (prefixWord ++ tailWord_2937928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937928).length < 2 ^ (prefixWord ++ tailWord_2937928).sum := by decide
  have hdescent : baseEnd_2937928 < baseStart_2937928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937971 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 4]
def baseStart_2937971 : Nat := 118140960795 + 2937971 * 2 ^ 59
def prefixEnd_2937971 : Nat := 4983230072969 + 3 ^ 40 * 2937971 * 2
def baseEnd_2937971 : Nat := 1508591271970629908651023

theorem tailTrace_2937971 : CollatzResearch.WordTrace tailWord_2937971 prefixEnd_2937971 1508591271970629908651023 := by
  unfold tailWord_2937971
  simp only [CollatzResearch.WordTrace]
  refine ⟨107156605639240307344317767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71437737092826871562878511 107156605639240307344317767)
  ·
    refine ⟨160734908458860461016476651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107156605639240307344317767 160734908458860461016476651)
    ·
      refine ⟨241102362688290691524714977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160734908458860461016476651 241102362688290691524714977)
      ·
        refine ⟨180826772016218018643536233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241102362688290691524714977 180826772016218018643536233)
        ·
          refine ⟨135620079012163513982652175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180826772016218018643536233 135620079012163513982652175)
          ·
            refine ⟨203430118518245270973978263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135620079012163513982652175 203430118518245270973978263)
            ·
              refine ⟨305145177777367906460967395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203430118518245270973978263 305145177777367906460967395)
              ·
                refine ⟨457717766666051859691451093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 305145177777367906460967395 457717766666051859691451093)
                ·
                  refine ⟨10727760156235590461518385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 457717766666051859691451093 10727760156235590461518385)
                  ·
                    refine ⟨8045820117176692846138789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10727760156235590461518385 8045820117176692846138789)
                    ·
                      refine ⟨1508591271970629908651023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8045820117176692846138789 1508591271970629908651023)
                      ·
                        rfl

theorem cell23_2937971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 4].length) (baseStart_2937971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937971 prefixEnd_2937971 := by exact prefixLift 2937971
  have htrace : WordTrace (prefixWord ++ tailWord_2937971) baseStart_2937971 baseEnd_2937971 := by
    simpa [prefixWord, tailWord_2937971, baseEnd_2937971] using wordTrace_append hprefix tailTrace_2937971
  have hstable : (prefixWord ++ tailWord_2937971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937971).length < 2 ^ (prefixWord ++ tailWord_2937971).sum := by decide
  have hdescent : baseEnd_2937971 < baseStart_2937971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937975 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 5, 2, 2]
def baseStart_2937975 : Nat := 118140960795 + 2937975 * 2 ^ 59
def prefixEnd_2937975 : Nat := 4983230072969 + 3 ^ 40 * 2937975 * 2
def baseEnd_2937975 : Nat := 1508593325893247893001005

theorem tailTrace_2937975 : CollatzResearch.WordTrace tailWord_2937975 prefixEnd_2937975 1508593325893247893001005 := by
  unfold tailWord_2937975
  simp only [CollatzResearch.WordTrace]
  refine ⟨107156751531225816027463379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71437834354150544018308919 107156751531225816027463379)
  ·
    refine ⟨160735127296838724041195069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107156751531225816027463379 160735127296838724041195069)
    ·
      refine ⟨60275672736314521515448151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160735127296838724041195069 60275672736314521515448151)
      ·
        refine ⟨90413509104471782273172227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60275672736314521515448151 90413509104471782273172227)
        ·
          refine ⟨135620263656707673409758341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90413509104471782273172227 135620263656707673409758341)
          ·
            refine ⟨25428799435632688764329689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135620263656707673409758341 25428799435632688764329689)
            ·
              refine ⟨19071599576724516573247267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25428799435632688764329689 19071599576724516573247267)
              ·
                refine ⟨28607399365086774859870901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19071599576724516573247267 28607399365086774859870901)
                ·
                  refine ⟨2681943690476885143112897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28607399365086774859870901 2681943690476885143112897)
                  ·
                    refine ⟨2011457767857663857334673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2681943690476885143112897 2011457767857663857334673)
                    ·
                      refine ⟨1508593325893247893001005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2011457767857663857334673 1508593325893247893001005)
                      ·
                        rfl

theorem cell23_2937975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 5, 2, 2].length) (baseStart_2937975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937975 prefixEnd_2937975 := by exact prefixLift 2937975
  have htrace : WordTrace (prefixWord ++ tailWord_2937975) baseStart_2937975 baseEnd_2937975 := by
    simpa [prefixWord, tailWord_2937975, baseEnd_2937975] using wordTrace_append hprefix tailTrace_2937975
  have hstable : (prefixWord ++ tailWord_2937975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937975).length < 2 ^ (prefixWord ++ tailWord_2937975).sum := by decide
  have hdescent : baseEnd_2937975 < baseStart_2937975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937981 : List Nat := [1, 4, 1, 1, 3, 1, 1, 11]
def baseStart_2937981 : Nat := 118140960795 + 2937981 * 2 ^ 59
def prefixEnd_2937981 : Nat := 4983230072969 + 3 ^ 40 * 2937981 * 2
def baseEnd_2937981 : Nat := 55873940991747217389851

theorem tailTrace_2937981 : CollatzResearch.WordTrace tailWord_2937981 prefixEnd_2937981 55873940991747217389851 := by
  unfold tailWord_2937981
  simp only [CollatzResearch.WordTrace]
  refine ⟨107156970369204079052181797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71437980246136052701454531 107156970369204079052181797)
  ·
    refine ⟨20091931944225764822284087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107156970369204079052181797 20091931944225764822284087)
    ·
      refine ⟨30137897916338647233426131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20091931944225764822284087 30137897916338647233426131)
      ·
        refine ⟨45206846874507970850139197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30137897916338647233426131 45206846874507970850139197)
        ·
          refine ⟨16952567577940489068802199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45206846874507970850139197 16952567577940489068802199)
          ·
            refine ⟨25428851366910733603203299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16952567577940489068802199 25428851366910733603203299)
            ·
              refine ⟨38143277050366100404804949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25428851366910733603203299 38143277050366100404804949)
              ·
                refine ⟨55873940991747217389851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 38143277050366100404804949 55873940991747217389851)
                ·
                  rfl

theorem cell23_2937981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 11].length) (baseStart_2937981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937981 prefixEnd_2937981 := by exact prefixLift 2937981
  have htrace : WordTrace (prefixWord ++ tailWord_2937981) baseStart_2937981 baseEnd_2937981 := by
    simpa [prefixWord, tailWord_2937981, baseEnd_2937981] using wordTrace_append hprefix tailTrace_2937981
  have hstable : (prefixWord ++ tailWord_2937981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937981).length < 2 ^ (prefixWord ++ tailWord_2937981).sum := by decide
  have hdescent : baseEnd_2937981 < baseStart_2937981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2937988 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 3, 2, 4]
def baseStart_2937988 : Nat := 118140960795 + 2937988 * 2 ^ 59
def prefixEnd_2937988 : Nat := 4983230072969 + 3 ^ 40 * 2937988 * 2
def baseEnd_2937988 : Nat := 1508600001141756342138445

theorem tailTrace_2937988 : CollatzResearch.WordTrace tailWord_2937988 prefixEnd_2937988 1508600001141756342138445 := by
  unfold tailWord_2937988
  simp only [CollatzResearch.WordTrace]
  refine ⟨53578612840089359623843309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71438150453452479498457745 53578612840089359623843309)
  ·
    refine ⟨20091979815033509858941241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53578612840089359623843309 20091979815033509858941241)
    ·
      refine ⟨15068984861275132394205931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20091979815033509858941241 15068984861275132394205931)
      ·
        refine ⟨22603477291912698591308897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15068984861275132394205931 22603477291912698591308897)
        ·
          refine ⟨16952607968934523943481673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22603477291912698591308897 16952607968934523943481673)
          ·
            refine ⟨12714455976700892957611255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16952607968934523943481673 12714455976700892957611255)
            ·
              refine ⟨19071683965051339436416883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12714455976700892957611255 19071683965051339436416883)
              ·
                refine ⟨28607525947577009154625325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19071683965051339436416883 28607525947577009154625325)
                ·
                  refine ⟨10727822230341378432984497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28607525947577009154625325 10727822230341378432984497)
                  ·
                    refine ⟨8045866672756033824738373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10727822230341378432984497 8045866672756033824738373)
                    ·
                      refine ⟨1508600001141756342138445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8045866672756033824738373 1508600001141756342138445)
                      ·
                        rfl

theorem cell23_2937988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_2937988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2937988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2937988 prefixEnd_2937988 := by exact prefixLift 2937988
  have htrace : WordTrace (prefixWord ++ tailWord_2937988) baseStart_2937988 baseEnd_2937988 := by
    simpa [prefixWord, tailWord_2937988, baseEnd_2937988] using wordTrace_append hprefix tailTrace_2937988
  have hstable : (prefixWord ++ tailWord_2937988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2937988).length < 2 ^ (prefixWord ++ tailWord_2937988).sum := by decide
  have hdescent : baseEnd_2937988 < baseStart_2937988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2937988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938002 : List Nat := [3, 2, 3, 1, 1, 3, 2, 2, 2, 4]
def baseStart_2938002 : Nat := 118140960795 + 2938002 * 2 ^ 59
def prefixEnd_2938002 : Nat := 4983230072969 + 3 ^ 40 * 2938002 * 2
def baseEnd_2938002 : Nat := 502869063290306429121127

theorem tailTrace_2938002 : CollatzResearch.WordTrace tailWord_2938002 prefixEnd_2938002 502869063290306429121127 := by
  unfold tailWord_2938002
  simp only [CollatzResearch.WordTrace]
  refine ⟨26789434075531999909674065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71438490868085333092464173 26789434075531999909674065)
  ·
    refine ⟨20092075556648999932255549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26789434075531999909674065 20092075556648999932255549)
    ·
      refine ⟨7534528333743374974595831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20092075556648999932255549 7534528333743374974595831)
      ·
        refine ⟨11301792500615062461893747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7534528333743374974595831 11301792500615062461893747)
        ·
          refine ⟨16952688750922593692840621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11301792500615062461893747 16952688750922593692840621)
          ·
            refine ⟨6357258281595972634815233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16952688750922593692840621 6357258281595972634815233)
            ·
              refine ⟨4767943711196979476111425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6357258281595972634815233 4767943711196979476111425)
              ·
                refine ⟨3575957783397734607083569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4767943711196979476111425 3575957783397734607083569)
                ·
                  refine ⟨2681968337548300955312677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3575957783397734607083569 2681968337548300955312677)
                  ·
                    refine ⟨502869063290306429121127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2681968337548300955312677 502869063290306429121127)
                    ·
                      rfl

theorem cell23_2938002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_2938002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938002 prefixEnd_2938002 := by exact prefixLift 2938002
  have htrace : WordTrace (prefixWord ++ tailWord_2938002) baseStart_2938002 baseEnd_2938002 := by
    simpa [prefixWord, tailWord_2938002, baseEnd_2938002] using wordTrace_append hprefix tailTrace_2938002
  have hstable : (prefixWord ++ tailWord_2938002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938002).length < 2 ^ (prefixWord ++ tailWord_2938002).sum := by decide
  have hdescent : baseEnd_2938002 < baseStart_2938002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938015 : List Nat := [1, 1, 2, 6, 2, 2, 1, 8]
def baseStart_2938015 : Nat := 118140960795 + 2938015 * 2 ^ 59
def prefixEnd_2938015 : Nat := 4983230072969 + 3 ^ 40 * 2938015 * 2
def baseEnd_2938015 : Nat := 55874587597015842092623

theorem tailTrace_2938015 : CollatzResearch.WordTrace tailWord_2938015 prefixEnd_2938015 55874587597015842092623 := by
  unfold tailWord_2938015
  simp only [CollatzResearch.WordTrace]
  refine ⟨107158210451080902858919499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71438806967387268572612999 107158210451080902858919499)
  ·
    refine ⟨160737315676621354288379249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107158210451080902858919499 160737315676621354288379249)
    ·
      refine ⟨120552986757466015716284437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160737315676621354288379249 120552986757466015716284437)
      ·
        refine ⟨5650921254256219486700833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 120552986757466015716284437 5650921254256219486700833)
        ·
          refine ⟨4238190940692164615025625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5650921254256219486700833 4238190940692164615025625)
          ·
            refine ⟨3178643205519123461269219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4238190940692164615025625 3178643205519123461269219)
            ·
              refine ⟨4767964808278685191903829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3178643205519123461269219 4767964808278685191903829)
              ·
                refine ⟨55874587597015842092623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4767964808278685191903829 55874587597015842092623)
                ·
                  rfl

theorem cell23_2938015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 8].length) (baseStart_2938015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938015 prefixEnd_2938015 := by exact prefixLift 2938015
  have htrace : WordTrace (prefixWord ++ tailWord_2938015) baseStart_2938015 baseEnd_2938015 := by
    simpa [prefixWord, tailWord_2938015, baseEnd_2938015] using wordTrace_append hprefix tailTrace_2938015
  have hstable : (prefixWord ++ tailWord_2938015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938015).length < 2 ^ (prefixWord ++ tailWord_2938015).sum := by decide
  have hdescent : baseEnd_2938015 < baseStart_2938015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938035 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 3, 3, 2]
def baseStart_2938035 : Nat := 118140960795 + 2938035 * 2 ^ 59
def prefixEnd_2938035 : Nat := 4983230072969 + 3 ^ 40 * 2938035 * 2
def baseEnd_2938035 : Nat := 1508624134732517658250729

theorem tailTrace_2938035 : CollatzResearch.WordTrace tailWord_2938035 prefixEnd_2938035 1508624134732517658250729 := by
  unfold tailWord_2938035
  simp only [CollatzResearch.WordTrace]
  refine ⟨107158939911008446274647559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71439293274005630849765039 107158939911008446274647559)
  ·
    refine ⟨160738409866512669411971339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107158939911008446274647559 160738409866512669411971339)
    ·
      refine ⟨241107614799769004117957009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160738409866512669411971339 241107614799769004117957009)
      ·
        refine ⟨180830711099826753088467757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241107614799769004117957009 180830711099826753088467757)
        ·
          refine ⟨67811516662435032408175409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180830711099826753088467757 67811516662435032408175409)
          ·
            refine ⟨50858637496826274306131557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67811516662435032408175409 50858637496826274306131557)
            ·
              refine ⟨9535994530654926432399667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50858637496826274306131557 9535994530654926432399667)
              ·
                refine ⟨14303991795982389648599501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9535994530654926432399667 14303991795982389648599501)
                ·
                  refine ⟨5363996923493396118224813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14303991795982389648599501 5363996923493396118224813)
                  ·
                    refine ⟨2011498846310023544334305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5363996923493396118224813 2011498846310023544334305)
                    ·
                      refine ⟨1508624134732517658250729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2011498846310023544334305 1508624134732517658250729)
                      ·
                        rfl

theorem cell23_2938035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 3, 2].length) (baseStart_2938035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938035 prefixEnd_2938035 := by exact prefixLift 2938035
  have htrace : WordTrace (prefixWord ++ tailWord_2938035) baseStart_2938035 baseEnd_2938035 := by
    simpa [prefixWord, tailWord_2938035, baseEnd_2938035] using wordTrace_append hprefix tailTrace_2938035
  have hstable : (prefixWord ++ tailWord_2938035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938035).length < 2 ^ (prefixWord ++ tailWord_2938035).sum := by decide
  have hdescent : baseEnd_2938035 < baseStart_2938035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938058 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 2, 6]
def baseStart_2938058 : Nat := 118140960795 + 2938058 * 2 ^ 59
def prefixEnd_2938058 : Nat := 4983230072969 + 3 ^ 40 * 2938058 * 2
def baseEnd_2938058 : Nat := 502878648262523689421041

theorem tailTrace_2938058 : CollatzResearch.WordTrace tailWord_2938058 prefixEnd_2938058 502878648262523689421041 := by
  unfold tailWord_2938058
  simp only [CollatzResearch.WordTrace]
  refine ⟨26789944697481280300683707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71439852526616747468489885 26789944697481280300683707)
  ·
    refine ⟨40184917046221920451025561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26789944697481280300683707 40184917046221920451025561)
    ·
      refine ⟨30138687784666440338269171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40184917046221920451025561 30138687784666440338269171)
      ·
        refine ⟨45208031676999660507403757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30138687784666440338269171 45208031676999660507403757)
        ·
          refine ⟨16953011878874872690276409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45208031676999660507403757 16953011878874872690276409)
          ·
            refine ⟨12714758909156154517707307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16953011878874872690276409 12714758909156154517707307)
            ·
              refine ⟨19072138363734231776560961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12714758909156154517707307 19072138363734231776560961)
              ·
                refine ⟨14304103772800673832420721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19072138363734231776560961 14304103772800673832420721)
                ·
                  refine ⟨10728077829600505374315541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14304103772800673832420721 10728077829600505374315541)
                  ·
                    refine ⟨502878648262523689421041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10728077829600505374315541 502878648262523689421041)
                    ·
                      rfl

theorem cell23_2938058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 2, 6].length) (baseStart_2938058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938058 prefixEnd_2938058 := by exact prefixLift 2938058
  have htrace : WordTrace (prefixWord ++ tailWord_2938058) baseStart_2938058 baseEnd_2938058 := by
    simpa [prefixWord, tailWord_2938058, baseEnd_2938058] using wordTrace_append hprefix tailTrace_2938058
  have hstable : (prefixWord ++ tailWord_2938058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938058).length < 2 ^ (prefixWord ++ tailWord_2938058).sum := by decide
  have hdescent : baseEnd_2938058 < baseStart_2938058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938088 : List Nat := [2, 1, 4, 1, 2, 1, 1, 4, 7]
def baseStart_2938088 : Nat := 118140960795 + 2938088 * 2 ^ 59
def prefixEnd_2938088 : Nat := 4983230072969 + 3 ^ 40 * 2938088 * 2
def baseEnd_2938088 : Nat := 167627927689689550098665

theorem tailTrace_2938088 : CollatzResearch.WordTrace tailWord_2938088 prefixEnd_2938088 167627927689689550098665 := by
  unfold tailWord_2938088
  simp only [CollatzResearch.WordTrace]
  refine ⟨53580436489908218163163459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71440581986544290884217945 53580436489908218163163459)
  ·
    refine ⟨80370654734862327244745189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53580436489908218163163459 80370654734862327244745189)
    ·
      refine ⟨15069497762786686358389723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80370654734862327244745189 15069497762786686358389723)
      ·
        refine ⟨22604246644180029537584585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15069497762786686358389723 22604246644180029537584585)
        ·
          refine ⟨16953184983135022153188439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22604246644180029537584585 16953184983135022153188439)
          ·
            refine ⟨25429777474702533229782659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16953184983135022153188439 25429777474702533229782659)
            ·
              refine ⟨38144666212053799844673989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25429777474702533229782659 38144666212053799844673989)
              ·
                refine ⟨7152124914760087470876373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38144666212053799844673989 7152124914760087470876373)
                ·
                  refine ⟨167627927689689550098665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7152124914760087470876373 167627927689689550098665)
                  ·
                    rfl

theorem cell23_2938088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 7].length) (baseStart_2938088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938088 prefixEnd_2938088 := by exact prefixLift 2938088
  have htrace : WordTrace (prefixWord ++ tailWord_2938088) baseStart_2938088 baseEnd_2938088 := by
    simpa [prefixWord, tailWord_2938088, baseEnd_2938088] using wordTrace_append hprefix tailTrace_2938088
  have hstable : (prefixWord ++ tailWord_2938088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938088).length < 2 ^ (prefixWord ++ tailWord_2938088).sum := by decide
  have hdescent : baseEnd_2938088 < baseStart_2938088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938152 : List Nat := [2, 1, 5, 1, 2, 2, 2, 1, 2, 5]
def baseStart_2938152 : Nat := 118140960795 + 2938152 * 2 ^ 59
def prefixEnd_2938152 : Nat := 4983230072969 + 3 ^ 40 * 2938152 * 2
def baseEnd_2938152 : Nat := 502894737323031233495897

theorem tailTrace_2938152 : CollatzResearch.WordTrace tailWord_2938152 prefixEnd_2938152 502894737323031233495897 := by
  unfold tailWord_2938152
  simp only [CollatzResearch.WordTrace]
  refine ⟨53581603625792287628328355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71442138167723050171104473 53581603625792287628328355)
  ·
    refine ⟨80372405438688431442492533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53581603625792287628328355 80372405438688431442492533)
    ·
      refine ⟨7534913009877040447733675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80372405438688431442492533 7534913009877040447733675)
      ·
        refine ⟨11302369514815560671600513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7534913009877040447733675 11302369514815560671600513)
        ·
          refine ⟨8476777136111670503700385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11302369514815560671600513 8476777136111670503700385)
          ·
            refine ⟨6357582852083752877775289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8476777136111670503700385 6357582852083752877775289)
            ·
              refine ⟨4768187139062814658331467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6357582852083752877775289 4768187139062814658331467)
              ·
                refine ⟨7152280708594221987497201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4768187139062814658331467 7152280708594221987497201)
                ·
                  refine ⟨5364210531445666490622901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7152280708594221987497201 5364210531445666490622901)
                  ·
                    refine ⟨502894737323031233495897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5364210531445666490622901 502894737323031233495897)
                    ·
                      rfl

theorem cell23_2938152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_2938152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938152 prefixEnd_2938152 := by exact prefixLift 2938152
  have htrace : WordTrace (prefixWord ++ tailWord_2938152) baseStart_2938152 baseEnd_2938152 := by
    simpa [prefixWord, tailWord_2938152, baseEnd_2938152] using wordTrace_append hprefix tailTrace_2938152
  have hstable : (prefixWord ++ tailWord_2938152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938152).length < 2 ^ (prefixWord ++ tailWord_2938152).sum := by decide
  have hdescent : baseEnd_2938152 < baseStart_2938152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938168 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 2, 1, 6]
def baseStart_2938168 : Nat := 118140960795 + 2938168 * 2 ^ 59
def prefixEnd_2938168 : Nat := 4983230072969 + 3 ^ 40 * 2938168 * 2
def baseEnd_2938168 : Nat := 1508692427659565637887617

theorem tailTrace_2938168 : CollatzResearch.WordTrace tailWord_2938168 prefixEnd_2938168 1508692427659565637887617 := by
  unfold tailWord_2938168
  simp only [CollatzResearch.WordTrace]
  refine ⟨53581895409763304994619579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71442527213017739992826105 53581895409763304994619579)
  ·
    refine ⟨80372843114644957491929369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53581895409763304994619579 80372843114644957491929369)
    ·
      refine ⟨60279632335983718118947027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80372843114644957491929369 60279632335983718118947027)
      ·
        refine ⟨90419448503975577178420541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60279632335983718118947027 90419448503975577178420541)
        ·
          refine ⟨33907293188990841441907703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90419448503975577178420541 33907293188990841441907703)
          ·
            refine ⟨50860939783486262162861555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33907293188990841441907703 50860939783486262162861555)
            ·
              refine ⟨76291409675229393244292333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50860939783486262162861555 76291409675229393244292333)
              ·
                refine ⟨28609278628211022466609625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76291409675229393244292333 28609278628211022466609625)
                ·
                  refine ⟨21456958971158266849957219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28609278628211022466609625 21456958971158266849957219)
                  ·
                    refine ⟨32185438456737400274935829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21456958971158266849957219 32185438456737400274935829)
                    ·
                      refine ⟨1508692427659565637887617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32185438456737400274935829 1508692427659565637887617)
                      ·
                        rfl

theorem cell23_2938168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_2938168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938168 prefixEnd_2938168 := by exact prefixLift 2938168
  have htrace : WordTrace (prefixWord ++ tailWord_2938168) baseStart_2938168 baseEnd_2938168 := by
    simpa [prefixWord, tailWord_2938168, baseEnd_2938168] using wordTrace_append hprefix tailTrace_2938168
  have hstable : (prefixWord ++ tailWord_2938168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938168).length < 2 ^ (prefixWord ++ tailWord_2938168).sum := by decide
  have hdescent : baseEnd_2938168 < baseStart_2938168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938173 : List Nat := [1, 4, 1, 5, 2, 1, 2, 2, 5]
def baseStart_2938173 : Nat := 118140960795 + 2938173 * 2 ^ 59
def prefixEnd_2938173 : Nat := 4983230072969 + 3 ^ 40 * 2938173 * 2
def baseEnd_2938173 : Nat := 167632777229204235369455

theorem tailTrace_2938173 : CollatzResearch.WordTrace tailWord_2938173 prefixEnd_2938173 167632777229204235369455 := by
  unfold tailWord_2938173
  simp only [CollatzResearch.WordTrace]
  refine ⟨107163973184508495843171173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71442648789672330562114115 107163973184508495843171173)
  ·
    refine ⟨20093244972095342970594595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 107163973184508495843171173 20093244972095342970594595)
    ·
      refine ⟨30139867458143014455891893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20093244972095342970594595 30139867458143014455891893)
      ·
        refine ⟨2825612574200907605239865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30139867458143014455891893 2825612574200907605239865)
        ·
          refine ⟨2119209430650680703929899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2825612574200907605239865 2119209430650680703929899)
          ·
            refine ⟨3178814145976021055894849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2119209430650680703929899 3178814145976021055894849)
            ·
              refine ⟨2384110609482015791921137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3178814145976021055894849 2384110609482015791921137)
              ·
                refine ⟨1788082957111511843940853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2384110609482015791921137 1788082957111511843940853)
                ·
                  refine ⟨167632777229204235369455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1788082957111511843940853 167632777229204235369455)
                  ·
                    rfl

theorem cell23_2938173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_2938173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938173 prefixEnd_2938173 := by exact prefixLift 2938173
  have htrace : WordTrace (prefixWord ++ tailWord_2938173) baseStart_2938173 baseEnd_2938173 := by
    simpa [prefixWord, tailWord_2938173, baseEnd_2938173] using wordTrace_append hprefix tailTrace_2938173
  have hstable : (prefixWord ++ tailWord_2938173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938173).length < 2 ^ (prefixWord ++ tailWord_2938173).sum := by decide
  have hdescent : baseEnd_2938173 < baseStart_2938173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938216 : List Nat := [2, 1, 4, 2, 3, 1, 2, 3, 1, 4]
def baseStart_2938216 : Nat := 118140960795 + 2938216 * 2 ^ 59
def prefixEnd_2938216 : Nat := 4983230072969 + 3 ^ 40 * 2938216 * 2
def baseEnd_2938216 : Nat := 502905691576993816695799

theorem tailTrace_2938216 : CollatzResearch.WordTrace tailWord_2938216 prefixEnd_2938216 502905691576993816695799 := by
  unfold tailWord_2938216
  simp only [CollatzResearch.WordTrace]
  refine ⟨53582770761676357093493251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71443694348901809457991001 53582770761676357093493251)
  ·
    refine ⟨80374156142514535640239877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53582770761676357093493251 80374156142514535640239877)
    ·
      refine ⟨15070154276721475432544977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80374156142514535640239877 15070154276721475432544977)
      ·
        refine ⟨11302615707541106574408733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15070154276721475432544977 11302615707541106574408733)
        ·
          refine ⟨4238480890327914965403275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11302615707541106574408733 4238480890327914965403275)
          ·
            refine ⟨6357721335491872448104913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4238480890327914965403275 6357721335491872448104913)
            ·
              refine ⟨4768291001618904336078685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6357721335491872448104913 4768291001618904336078685)
              ·
                refine ⟨1788109125607089126029507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4768291001618904336078685 1788109125607089126029507)
                ·
                  refine ⟨2682163688410633689044261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1788109125607089126029507 2682163688410633689044261)
                  ·
                    refine ⟨502905691576993816695799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2682163688410633689044261 502905691576993816695799)
                    ·
                      rfl

theorem cell23_2938216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_2938216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938216 prefixEnd_2938216 := by exact prefixLift 2938216
  have htrace : WordTrace (prefixWord ++ tailWord_2938216) baseStart_2938216 baseEnd_2938216 := by
    simpa [prefixWord, tailWord_2938216, baseEnd_2938216] using wordTrace_append hprefix tailTrace_2938216
  have hstable : (prefixWord ++ tailWord_2938216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938216).length < 2 ^ (prefixWord ++ tailWord_2938216).sum := by decide
  have hdescent : baseEnd_2938216 < baseStart_2938216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938229 : List Nat := [1, 3, 4, 1, 3, 2, 1, 2, 6]
def baseStart_2938229 : Nat := 118140960795 + 2938229 * 2 ^ 59
def prefixEnd_2938229 : Nat := 4983230072969 + 3 ^ 40 * 2938229 * 2
def baseEnd_2938229 : Nat := 167635972219943322136093

theorem tailTrace_2938229 : CollatzResearch.WordTrace tailWord_2938229 prefixEnd_2938229 167635972219943322136093 := by
  unfold tailWord_2938229
  simp only [CollatzResearch.WordTrace]
  refine ⟨107166015672305617407209741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71444010448203744938139827 107166015672305617407209741)
  ·
    refine ⟨40187255877114606527703653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107166015672305617407209741 40187255877114606527703653)
    ·
      refine ⟨7535110476958988723944435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40187255877114606527703653 7535110476958988723944435)
      ·
        refine ⟨11302665715438483085916653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7535110476958988723944435 11302665715438483085916653)
        ·
          refine ⟨4238499643289431157218745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11302665715438483085916653 4238499643289431157218745)
          ·
            refine ⟨3178874732467073367914059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4238499643289431157218745 3178874732467073367914059)
            ·
              refine ⟨4768312098700610051871089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3178874732467073367914059 4768312098700610051871089)
              ·
                refine ⟨3576234074025457538903317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4768312098700610051871089 3576234074025457538903317)
                ·
                  refine ⟨167635972219943322136093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3576234074025457538903317 167635972219943322136093)
                  ·
                    rfl

theorem cell23_2938229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 6].length) (baseStart_2938229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938229 prefixEnd_2938229 := by exact prefixLift 2938229
  have htrace : WordTrace (prefixWord ++ tailWord_2938229) baseStart_2938229 baseEnd_2938229 := by
    simpa [prefixWord, tailWord_2938229, baseEnd_2938229] using wordTrace_append hprefix tailTrace_2938229
  have hstable : (prefixWord ++ tailWord_2938229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938229).length < 2 ^ (prefixWord ++ tailWord_2938229).sum := by decide
  have hdescent : baseEnd_2938229 < baseStart_2938229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938245 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 5, 1, 4]
def baseStart_2938245 : Nat := 118140960795 + 2938245 * 2 ^ 59
def prefixEnd_2938245 : Nat := 4983230072969 + 3 ^ 40 * 2938245 * 2
def baseEnd_2938245 : Nat := 1508731965669961836624763

theorem tailTrace_2938245 : CollatzResearch.WordTrace tailWord_2938245 prefixEnd_2938245 1508731965669961836624763 := by
  unfold tailWord_2938245
  simp only [CollatzResearch.WordTrace]
  refine ⟨107166599240247652139792189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71444399493498434759861459 107166599240247652139792189)
  ·
    refine ⟨40187474715092869552422071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107166599240247652139792189 40187474715092869552422071)
    ·
      refine ⟨60281212072639304328633107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40187474715092869552422071 60281212072639304328633107)
      ·
        refine ⟨90421818108958956492949661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60281212072639304328633107 90421818108958956492949661)
        ·
          refine ⟨33908181790859608684856123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90421818108958956492949661 33908181790859608684856123)
          ·
            refine ⟨50862272686289413027284185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33908181790859608684856123 50862272686289413027284185)
            ·
              refine ⟨38146704514717059770463139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50862272686289413027284185 38146704514717059770463139)
              ·
                refine ⟨57220056772075589655694709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38146704514717059770463139 57220056772075589655694709)
                ·
                  refine ⟨5364380322382086530221379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57220056772075589655694709 5364380322382086530221379)
                  ·
                    refine ⟨8046570483573129795332069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5364380322382086530221379 8046570483573129795332069)
                    ·
                      refine ⟨1508731965669961836624763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8046570483573129795332069 1508731965669961836624763)
                      ·
                        rfl

theorem cell23_2938245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_2938245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938245 prefixEnd_2938245 := by exact prefixLift 2938245
  have htrace : WordTrace (prefixWord ++ tailWord_2938245) baseStart_2938245 baseEnd_2938245 := by
    simpa [prefixWord, tailWord_2938245, baseEnd_2938245] using wordTrace_append hprefix tailTrace_2938245
  have hstable : (prefixWord ++ tailWord_2938245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938245).length < 2 ^ (prefixWord ++ tailWord_2938245).sum := by decide
  have hdescent : baseEnd_2938245 < baseStart_2938245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938275 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 4]
def baseStart_2938275 : Nat := 118140960795 + 2938275 * 2 ^ 59
def prefixEnd_2938275 : Nat := 4983230072969 + 3 ^ 40 * 2938275 * 2
def baseEnd_2938275 : Nat := 1508747370089596719249625

theorem tailTrace_2938275 : CollatzResearch.WordTrace tailWord_2938275 prefixEnd_2938275 1508747370089596719249625 := by
  unfold tailWord_2938275
  simp only [CollatzResearch.WordTrace]
  refine ⟨107167693430138967263384279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71445128953425978175589519 107167693430138967263384279)
  ·
    refine ⟨160751540145208450895076419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107167693430138967263384279 160751540145208450895076419)
    ·
      refine ⟨241127310217812676342614629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160751540145208450895076419 241127310217812676342614629)
      ·
        refine ⟨45211370665839876814240243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241127310217812676342614629 45211370665839876814240243)
        ·
          refine ⟨67817055998759815221360365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45211370665839876814240243 67817055998759815221360365)
          ·
            refine ⟨25431395999534930708010137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67817055998759815221360365 25431395999534930708010137)
            ·
              refine ⟨19073546999651198031007603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25431395999534930708010137 19073546999651198031007603)
              ·
                refine ⟨28610320499476797046511405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19073546999651198031007603 28610320499476797046511405)
                ·
                  refine ⟨10728870187303798892441777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28610320499476797046511405 10728870187303798892441777)
                  ·
                    refine ⟨8046652640477849169331333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10728870187303798892441777 8046652640477849169331333)
                    ·
                      refine ⟨1508747370089596719249625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8046652640477849169331333 1508747370089596719249625)
                      ·
                        rfl

theorem cell23_2938275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_2938275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938275 prefixEnd_2938275 := by exact prefixLift 2938275
  have htrace : WordTrace (prefixWord ++ tailWord_2938275) baseStart_2938275 baseEnd_2938275 := by
    simpa [prefixWord, tailWord_2938275, baseEnd_2938275] using wordTrace_append hprefix tailTrace_2938275
  have hstable : (prefixWord ++ tailWord_2938275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938275).length < 2 ^ (prefixWord ++ tailWord_2938275).sum := by decide
  have hdescent : baseEnd_2938275 < baseStart_2938275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938296 : List Nat := [2, 1, 2, 1, 2, 2, 2, 6, 1, 2, 2]
def baseStart_2938296 : Nat := 118140960795 + 2938296 * 2 ^ 59
def prefixEnd_2938296 : Nat := 4983230072969 + 3 ^ 40 * 2938296 * 2
def baseEnd_2938296 : Nat := 1508758153183341137087029

theorem tailTrace_2938296 : CollatzResearch.WordTrace tailWord_2938296 prefixEnd_2938296 1508758153183341137087029 := by
  unfold tailWord_2938296
  simp only [CollatzResearch.WordTrace]
  refine ⟨53584229681531443924949371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71445639575375258566599161 53584229681531443924949371)
  ·
    refine ⟨80376344522297165887424057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53584229681531443924949371 80376344522297165887424057)
    ·
      refine ⟨60282258391722874415568043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80376344522297165887424057 60282258391722874415568043)
      ·
        refine ⟨90423387587584311623352065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60282258391722874415568043 90423387587584311623352065)
        ·
          refine ⟨67817540690688233717514049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90423387587584311623352065 67817540690688233717514049)
          ·
            refine ⟨50863155518016175288135537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67817540690688233717514049 50863155518016175288135537)
            ·
              refine ⟨38147366638512131466101653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50863155518016175288135537 38147366638512131466101653)
              ·
                refine ⟨1788157811180256162473515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38147366638512131466101653 1788157811180256162473515)
                ·
                  refine ⟨2682236716770384243710273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1788157811180256162473515 2682236716770384243710273)
                  ·
                    refine ⟨2011677537577788182782705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2682236716770384243710273 2011677537577788182782705)
                    ·
                      refine ⟨1508758153183341137087029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2011677537577788182782705 1508758153183341137087029)
                      ·
                        rfl

theorem cell23_2938296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 6, 1, 2, 2].length) (baseStart_2938296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938296 prefixEnd_2938296 := by exact prefixLift 2938296
  have htrace : WordTrace (prefixWord ++ tailWord_2938296) baseStart_2938296 baseEnd_2938296 := by
    simpa [prefixWord, tailWord_2938296, baseEnd_2938296] using wordTrace_append hprefix tailTrace_2938296
  have hstable : (prefixWord ++ tailWord_2938296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938296).length < 2 ^ (prefixWord ++ tailWord_2938296).sum := by decide
  have hdescent : baseEnd_2938296 < baseStart_2938296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938312 : List Nat := [2, 1, 3, 1, 3, 1, 2, 3, 1, 3, 3]
def baseStart_2938312 : Nat := 118140960795 + 2938312 * 2 ^ 59
def prefixEnd_2938312 : Nat := 4983230072969 + 3 ^ 40 * 2938312 * 2
def baseEnd_2938312 : Nat := 1508766368873813074486955

theorem tailTrace_2938312 : CollatzResearch.WordTrace tailWord_2938312 prefixEnd_2938312 1508766368873813074486955 := by
  unfold tailWord_2938312
  simp only [CollatzResearch.WordTrace]
  refine ⟨53584521465502461291240595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71446028620669948388320793 53584521465502461291240595)
  ·
    refine ⟨80376782198253691936860893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53584521465502461291240595 80376782198253691936860893)
    ·
      refine ⟨30141293324345134476322835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80376782198253691936860893 30141293324345134476322835)
      ·
        refine ⟨45211939986517701714484253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30141293324345134476322835 45211939986517701714484253)
        ·
          refine ⟨16954477494944138142931595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45211939986517701714484253 16954477494944138142931595)
          ·
            refine ⟨25431716242416207214397393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16954477494944138142931595 25431716242416207214397393)
            ·
              refine ⟨19073787181812155410798045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25431716242416207214397393 19073787181812155410798045)
              ·
                refine ⟨7152670193179558279049267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19073787181812155410798045 7152670193179558279049267)
                ·
                  refine ⟨10729005289769337418573901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7152670193179558279049267 10729005289769337418573901)
                  ·
                    refine ⟨4023376983663501531965213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10729005289769337418573901 4023376983663501531965213)
                    ·
                      refine ⟨1508766368873813074486955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4023376983663501531965213 1508766368873813074486955)
                      ·
                        rfl

theorem cell23_2938312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_2938312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938312 prefixEnd_2938312 := by exact prefixLift 2938312
  have htrace : WordTrace (prefixWord ++ tailWord_2938312) baseStart_2938312 baseEnd_2938312 := by
    simpa [prefixWord, tailWord_2938312, baseEnd_2938312] using wordTrace_append hprefix tailTrace_2938312
  have hstable : (prefixWord ++ tailWord_2938312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938312).length < 2 ^ (prefixWord ++ tailWord_2938312).sum := by decide
  have hdescent : baseEnd_2938312 < baseStart_2938312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938316 : List Nat := [2, 2, 1, 4, 2, 3, 1, 2, 1, 2, 3]
def baseStart_2938316 : Nat := 118140960795 + 2938316 * 2 ^ 59
def prefixEnd_2938316 : Nat := 4983230072969 + 3 ^ 40 * 2938316 * 2
def baseEnd_2938316 : Nat := 1508768422796431058836937

theorem tailTrace_2938316 : CollatzResearch.WordTrace tailWord_2938316 prefixEnd_2938316 1508768422796431058836937 := by
  unfold tailWord_2938316
  simp only [CollatzResearch.WordTrace]
  refine ⟨53584594411495215632813401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71446125881993620843751201 53584594411495215632813401)
  ·
    refine ⟨40188445808621411724610051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53584594411495215632813401 40188445808621411724610051)
    ·
      refine ⟨60282668712932117586915077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40188445808621411724610051 60282668712932117586915077)
      ·
        refine ⟨11303000383674772047546577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60282668712932117586915077 11303000383674772047546577)
        ·
          refine ⟨8477250287756079035659933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11303000383674772047546577 8477250287756079035659933)
          ·
            refine ⟨3178968857908529638372475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8477250287756079035659933 3178968857908529638372475)
            ·
              refine ⟨4768453286862794457558713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3178968857908529638372475 4768453286862794457558713)
              ·
                refine ⟨3576339965147095843169035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4768453286862794457558713 3576339965147095843169035)
                ·
                  refine ⟨5364509947720643764753553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3576339965147095843169035 5364509947720643764753553)
                  ·
                    refine ⟨4023382460790482823565165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5364509947720643764753553 4023382460790482823565165)
                    ·
                      refine ⟨1508768422796431058836937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4023382460790482823565165 1508768422796431058836937)
                      ·
                        rfl

theorem cell23_2938316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_2938316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938316 prefixEnd_2938316 := by exact prefixLift 2938316
  have htrace : WordTrace (prefixWord ++ tailWord_2938316) baseStart_2938316 baseEnd_2938316 := by
    simpa [prefixWord, tailWord_2938316, baseEnd_2938316] using wordTrace_append hprefix tailTrace_2938316
  have hstable : (prefixWord ++ tailWord_2938316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938316).length < 2 ^ (prefixWord ++ tailWord_2938316).sum := by decide
  have hdescent : baseEnd_2938316 < baseStart_2938316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938355 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 5]
def baseStart_2938355 : Nat := 118140960795 + 2938355 * 2 ^ 59
def prefixEnd_2938355 : Nat := 4983230072969 + 3 ^ 40 * 2938355 * 2
def baseEnd_2938355 : Nat := 1508788448541956406249257

theorem tailTrace_2938355 : CollatzResearch.WordTrace tailWord_2938355 prefixEnd_2938355 1508788448541956406249257 := by
  unfold tailWord_2938355
  simp only [CollatzResearch.WordTrace]
  refine ⟨107170611269849140926296519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71447074179899427284197679 107170611269849140926296519)
  ·
    refine ⟨160755916904773711389444779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107170611269849140926296519 160755916904773711389444779)
    ·
      refine ⟨241133875357160567084167169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160755916904773711389444779 241133875357160567084167169)
      ·
        refine ⟨180850406517870425313125377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241133875357160567084167169 180850406517870425313125377)
        ·
          refine ⟨135637804888402818984844033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180850406517870425313125377 135637804888402818984844033)
          ·
            refine ⟨101728353666302114238633025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135637804888402818984844033 101728353666302114238633025)
            ·
              refine ⟨76296265249726585678974769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101728353666302114238633025 76296265249726585678974769)
              ·
                refine ⟨57222198937294939259231077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76296265249726585678974769 57222198937294939259231077)
                ·
                  refine ⟨10729162300742801111105827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57222198937294939259231077 10729162300742801111105827)
                  ·
                    refine ⟨16093743451114201666658741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10729162300742801111105827 16093743451114201666658741)
                    ·
                      refine ⟨1508788448541956406249257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16093743451114201666658741 1508788448541956406249257)
                      ·
                        rfl

theorem cell23_2938355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 5].length) (baseStart_2938355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938355 prefixEnd_2938355 := by exact prefixLift 2938355
  have htrace : WordTrace (prefixWord ++ tailWord_2938355) baseStart_2938355 baseEnd_2938355 := by
    simpa [prefixWord, tailWord_2938355, baseEnd_2938355] using wordTrace_append hprefix tailTrace_2938355
  have hstable : (prefixWord ++ tailWord_2938355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938355).length < 2 ^ (prefixWord ++ tailWord_2938355).sum := by decide
  have hdescent : baseEnd_2938355 < baseStart_2938355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938442 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_2938442 : Nat := 118140960795 + 2938442 * 2 ^ 59
def prefixEnd_2938442 : Nat := 4983230072969 + 3 ^ 40 * 2938442 * 2
def baseEnd_2938442 : Nat := 1508833121358897565861357

theorem tailTrace_2938442 : CollatzResearch.WordTrace tailWord_2938442 prefixEnd_2938442 1508833121358897565861357 := by
  unfold tailWord_2938442
  simp only [CollatzResearch.WordTrace]
  refine ⟨26793446105133488696178395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71449189613689303189809053 26793446105133488696178395)
  ·
    refine ⟨40190169157700233044267593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26793446105133488696178395 40190169157700233044267593)
    ·
      refine ⟨30142626868275174783200695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40190169157700233044267593 30142626868275174783200695)
      ·
        refine ⟨45213940302412762174801043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30142626868275174783200695 45213940302412762174801043)
        ·
          refine ⟨67820910453619143262201565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45213940302412762174801043 67820910453619143262201565)
          ·
            refine ⟨25432841420107178723325587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67820910453619143262201565 25432841420107178723325587)
            ·
              refine ⟨38149262130160768084988381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25432841420107178723325587 38149262130160768084988381)
              ·
                refine ⟨14305973298810288031870643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38149262130160768084988381 14305973298810288031870643)
                ·
                  refine ⟨21458959948215432047805965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14305973298810288031870643 21458959948215432047805965)
                  ·
                    refine ⟨8047109980580787017927237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21458959948215432047805965 8047109980580787017927237)
                    ·
                      refine ⟨1508833121358897565861357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8047109980580787017927237 1508833121358897565861357)
                      ·
                        rfl

theorem cell23_2938442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_2938442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938442 prefixEnd_2938442 := by exact prefixLift 2938442
  have htrace : WordTrace (prefixWord ++ tailWord_2938442) baseStart_2938442 baseEnd_2938442 := by
    simpa [prefixWord, tailWord_2938442, baseEnd_2938442] using wordTrace_append hprefix tailTrace_2938442
  have hstable : (prefixWord ++ tailWord_2938442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938442).length < 2 ^ (prefixWord ++ tailWord_2938442).sum := by decide
  have hdescent : baseEnd_2938442 < baseStart_2938442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938520 : List Nat := [2, 1, 2, 4, 1, 4, 2, 2, 1, 4]
def baseStart_2938520 : Nat := 118140960795 + 2938520 * 2 ^ 59
def prefixEnd_2938520 : Nat := 4983230072969 + 3 ^ 40 * 2938520 * 2
def baseEnd_2938520 : Nat := 502957724283316086895333

theorem tailTrace_2938520 : CollatzResearch.WordTrace tailWord_2938520 prefixEnd_2938520 502957724283316086895333 := by
  unfold tailWord_2938520
  simp only [CollatzResearch.WordTrace]
  refine ⟨53588314657125687053026507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71451086209500916070702009 53588314657125687053026507)
  ·
    refine ⟨80382471985688530579539761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53588314657125687053026507 80382471985688530579539761)
    ·
      refine ⟨60286853989266397934654821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80382471985688530579539761 60286853989266397934654821)
      ·
        refine ⟨11303785122987449612747779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60286853989266397934654821 11303785122987449612747779)
        ·
          refine ⟨16955677684481174419121669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11303785122987449612747779 16955677684481174419121669)
          ·
            refine ⟨3179189565840220203585313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16955677684481174419121669 3179189565840220203585313)
            ·
              refine ⟨2384392174380165152688985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3179189565840220203585313 2384392174380165152688985)
              ·
                refine ⟨1788294130785123864516739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2384392174380165152688985 1788294130785123864516739)
                ·
                  refine ⟨2682441196177685796775109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1788294130785123864516739 2682441196177685796775109)
                  ·
                    refine ⟨502957724283316086895333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2682441196177685796775109 502957724283316086895333)
                    ·
                      rfl

theorem cell23_2938520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 1, 4].length) (baseStart_2938520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938520 prefixEnd_2938520 := by exact prefixLift 2938520
  have htrace : WordTrace (prefixWord ++ tailWord_2938520) baseStart_2938520 baseEnd_2938520 := by
    simpa [prefixWord, tailWord_2938520, baseEnd_2938520] using wordTrace_append hprefix tailTrace_2938520
  have hstable : (prefixWord ++ tailWord_2938520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938520).length < 2 ^ (prefixWord ++ tailWord_2938520).sum := by decide
  have hdescent : baseEnd_2938520 < baseStart_2938520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938529 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 3, 5]
def baseStart_2938529 : Nat := 118140960795 + 2938529 * 2 ^ 59
def prefixEnd_2938529 : Nat := 4983230072969 + 3 ^ 40 * 2938529 * 2
def baseEnd_2938529 : Nat := 502959264725279575157819

theorem tailTrace_2938529 : CollatzResearch.WordTrace tailWord_2938529 prefixEnd_2938529 502959264725279575157819 := by
  unfold tailWord_2938529
  simp only [CollatzResearch.WordTrace]
  refine ⟨107176957571218768643130641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71451305047479179095420427 107176957571218768643130641)
  ·
    refine ⟨80382718178414076482347981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107176957571218768643130641 80382718178414076482347981)
    ·
      refine ⟨30143519316905278680880493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80382718178414076482347981 30143519316905278680880493)
      ·
        refine ⟨11303819743839479505330185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30143519316905278680880493 11303819743839479505330185)
        ·
          refine ⟨8477864807879609628997639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11303819743839479505330185 8477864807879609628997639)
          ·
            refine ⟨12716797211819414443496459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8477864807879609628997639 12716797211819414443496459)
            ·
              refine ⟨19075195817729121665244689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12716797211819414443496459 19075195817729121665244689)
              ·
                refine ⟨14306396863296841248933517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19075195817729121665244689 14306396863296841248933517)
                ·
                  refine ⟨5364898823736315468350069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14306396863296841248933517 5364898823736315468350069)
                  ·
                    refine ⟨502959264725279575157819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5364898823736315468350069 502959264725279575157819)
                    ·
                      rfl

theorem cell23_2938529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_2938529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938529 prefixEnd_2938529 := by exact prefixLift 2938529
  have htrace : WordTrace (prefixWord ++ tailWord_2938529) baseStart_2938529 baseEnd_2938529 := by
    simpa [prefixWord, tailWord_2938529, baseEnd_2938529] using wordTrace_append hprefix tailTrace_2938529
  have hstable : (prefixWord ++ tailWord_2938529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938529).length < 2 ^ (prefixWord ++ tailWord_2938529).sum := by decide
  have hdescent : baseEnd_2938529 < baseStart_2938529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938559 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 4, 4]
def baseStart_2938559 : Nat := 118140960795 + 2938559 * 2 ^ 59
def prefixEnd_2938559 : Nat := 4983230072969 + 3 ^ 40 * 2938559 * 2
def baseEnd_2938559 : Nat := 502964399531824536032773

theorem tailTrace_2938559 : CollatzResearch.WordTrace tailWord_2938559 prefixEnd_2938559 502964399531824536032773 := by
  unfold tailWord_2938559
  simp only [CollatzResearch.WordTrace]
  refine ⟨107178051761110083766722731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71452034507406722511148487 107178051761110083766722731)
  ·
    refine ⟨160767077641665125650084097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107178051761110083766722731 160767077641665125650084097)
    ·
      refine ⟨120575308231248844237563073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160767077641665125650084097 120575308231248844237563073)
      ·
        refine ⟨90431481173436633178172305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120575308231248844237563073 90431481173436633178172305)
        ·
          refine ⟨67823610880077474883629229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90431481173436633178172305 67823610880077474883629229)
          ·
            refine ⟨25433854080029053081360961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67823610880077474883629229 25433854080029053081360961)
            ·
              refine ⟨19075390560021789811020721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25433854080029053081360961 19075390560021789811020721)
              ·
                refine ⟨14306542920016342358265541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19075390560021789811020721 14306542920016342358265541)
                ·
                  refine ⟨2682476797503064192174789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14306542920016342358265541 2682476797503064192174789)
                  ·
                    refine ⟨502964399531824536032773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2682476797503064192174789 502964399531824536032773)
                    ·
                      rfl

theorem cell23_2938559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 4].length) (baseStart_2938559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938559 prefixEnd_2938559 := by exact prefixLift 2938559
  have htrace : WordTrace (prefixWord ++ tailWord_2938559) baseStart_2938559 baseEnd_2938559 := by
    simpa [prefixWord, tailWord_2938559, baseEnd_2938559] using wordTrace_append hprefix tailTrace_2938559
  have hstable : (prefixWord ++ tailWord_2938559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938559).length < 2 ^ (prefixWord ++ tailWord_2938559).sum := by decide
  have hdescent : baseEnd_2938559 < baseStart_2938559 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938583 : List Nat := [1, 1, 3, 2, 1, 3, 4, 1, 3, 2, 2]
def baseStart_2938583 : Nat := 118140960795 + 2938583 * 2 ^ 59
def prefixEnd_2938583 : Nat := 4983230072969 + 3 ^ 40 * 2938583 * 2
def baseEnd_2938583 : Nat := 1508905522131181514198209

theorem tailTrace_2938583 : CollatzResearch.WordTrace tailWord_2938583 prefixEnd_2938583 1508905522131181514198209 := by
  unfold tailWord_2938583
  simp only [CollatzResearch.WordTrace]
  refine ⟨107178927113023135865596403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71452618075348757243730935 107178927113023135865596403)
  ·
    refine ⟨160768390669534703798394605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107178927113023135865596403 160768390669534703798394605)
    ·
      refine ⟨60288146501075513924397977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160768390669534703798394605 60288146501075513924397977)
      ·
        refine ⟨45216109875806635443298483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60288146501075513924397977 45216109875806635443298483)
        ·
          refine ⟨67824164813709953164947725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45216109875806635443298483 67824164813709953164947725)
          ·
            refine ⟨25434061805141232436855397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67824164813709953164947725 25434061805141232436855397)
            ·
              refine ⟨4768886588463981081910387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25434061805141232436855397 4768886588463981081910387)
              ·
                refine ⟨7153329882695971622865581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4768886588463981081910387 7153329882695971622865581)
                ·
                  refine ⟨2682498706010989358574593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7153329882695971622865581 2682498706010989358574593)
                  ·
                    refine ⟨2011874029508242018930945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2682498706010989358574593 2011874029508242018930945)
                    ·
                      refine ⟨1508905522131181514198209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2011874029508242018930945 1508905522131181514198209)
                      ·
                        rfl

theorem cell23_2938583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_2938583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938583 prefixEnd_2938583 := by exact prefixLift 2938583
  have htrace : WordTrace (prefixWord ++ tailWord_2938583) baseStart_2938583 baseEnd_2938583 := by
    simpa [prefixWord, tailWord_2938583, baseEnd_2938583] using wordTrace_append hprefix tailTrace_2938583
  have hstable : (prefixWord ++ tailWord_2938583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938583).length < 2 ^ (prefixWord ++ tailWord_2938583).sum := by decide
  have hdescent : baseEnd_2938583 < baseStart_2938583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938593 : List Nat := [1, 2, 3, 1, 6, 1, 1, 1, 1, 6]
def baseStart_2938593 : Nat := 118140960795 + 2938593 * 2 ^ 59
def prefixEnd_2938593 : Nat := 4983230072969 + 3 ^ 40 * 2938593 * 2
def baseEnd_2938593 : Nat := 502970218979242158357721

theorem tailTrace_2938593 : CollatzResearch.WordTrace tailWord_2938593 prefixEnd_2938593 502970218979242158357721 := by
  unfold tailWord_2938593
  simp only [CollatzResearch.WordTrace]
  refine ⟨107179291842986907573460433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71452861228657938382306955 107179291842986907573460433)
  ·
    refine ⟨80384468882240180680095325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107179291842986907573460433 80384468882240180680095325)
    ·
      refine ⟨30144175830840067755035747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80384468882240180680095325 30144175830840067755035747)
      ·
        refine ⟨45216263746260101632553621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30144175830840067755035747 45216263746260101632553621)
        ·
          refine ⟨2119512363105942264025951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 45216263746260101632553621 2119512363105942264025951)
          ·
            refine ⟨3179268544658913396038927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2119512363105942264025951 3179268544658913396038927)
            ·
              refine ⟨4768902816988370094058391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3179268544658913396038927 4768902816988370094058391)
              ·
                refine ⟨7153354225482555141087587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4768902816988370094058391 7153354225482555141087587)
                ·
                  refine ⟨10730031338223832711631381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7153354225482555141087587 10730031338223832711631381)
                  ·
                    refine ⟨502970218979242158357721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10730031338223832711631381 502970218979242158357721)
                    ·
                      rfl

theorem cell23_2938593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_2938593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938593 prefixEnd_2938593 := by exact prefixLift 2938593
  have htrace : WordTrace (prefixWord ++ tailWord_2938593) baseStart_2938593 baseEnd_2938593 := by
    simpa [prefixWord, tailWord_2938593, baseEnd_2938593] using wordTrace_append hprefix tailTrace_2938593
  have hstable : (prefixWord ++ tailWord_2938593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938593).length < 2 ^ (prefixWord ++ tailWord_2938593).sum := by decide
  have hdescent : baseEnd_2938593 < baseStart_2938593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938650 : List Nat := [3, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3]
def baseStart_2938650 : Nat := 118140960795 + 2938650 * 2 ^ 59
def prefixEnd_2938650 : Nat := 4983230072969 + 3 ^ 40 * 2938650 * 2
def baseEnd_2938650 : Nat := 1508939925335032752060401

theorem tailTrace_2938650 : CollatzResearch.WordTrace tailWord_2938650 prefixEnd_2938650 1508939925335032752060401 := by
  unfold tailWord_2938650
  simp only [CollatzResearch.WordTrace]
  refine ⟨26795342700945101577071351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71454247202520270872190269 26795342700945101577071351)
  ·
    refine ⟨40193014051417652365607027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26795342700945101577071351 40193014051417652365607027)
    ·
      refine ⟨60289521077126478548410541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40193014051417652365607027 60289521077126478548410541)
      ·
        refine ⟨22608570403922429455653953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60289521077126478548410541 22608570403922429455653953)
        ·
          refine ⟨16956427802941822091740465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22608570403922429455653953 16956427802941822091740465)
          ·
            refine ⟨12717320852206366568805349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16956427802941822091740465 12717320852206366568805349)
            ·
              refine ⟨2384497659788693731651003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12717320852206366568805349 2384497659788693731651003)
              ·
                refine ⟨3576746489683040597476505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2384497659788693731651003 3576746489683040597476505)
                ·
                  refine ⟨2682559867262280448107379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3576746489683040597476505 2682559867262280448107379)
                  ·
                    refine ⟨4023839800893420672161069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2682559867262280448107379 4023839800893420672161069)
                    ·
                      refine ⟨1508939925335032752060401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4023839800893420672161069 1508939925335032752060401)
                      ·
                        rfl

theorem cell23_2938650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_2938650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938650 prefixEnd_2938650 := by exact prefixLift 2938650
  have htrace : WordTrace (prefixWord ++ tailWord_2938650) baseStart_2938650 baseEnd_2938650 := by
    simpa [prefixWord, tailWord_2938650, baseEnd_2938650] using wordTrace_append hprefix tailTrace_2938650
  have hstable : (prefixWord ++ tailWord_2938650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938650).length < 2 ^ (prefixWord ++ tailWord_2938650).sum := by decide
  have hdescent : baseEnd_2938650 < baseStart_2938650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938654 : List Nat := [4, 3, 2, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_2938654 : Nat := 118140960795 + 2938654 * 2 ^ 59
def prefixEnd_2938654 : Nat := 4983230072969 + 3 ^ 40 * 2938654 * 2
def baseEnd_2938654 : Nat := 1508941979257650736410383

theorem tailTrace_2938654 : CollatzResearch.WordTrace tailWord_2938654 prefixEnd_2938654 1508941979257650736410383 := by
  unfold tailWord_2938654
  simp only [CollatzResearch.WordTrace]
  refine ⟨13397689586970739373928877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 71454344463843943327620677 13397689586970739373928877)
  ·
    refine ⟨5024133595114027265223329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13397689586970739373928877 5024133595114027265223329)
    ·
      refine ⟨3768100196335520448917497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5024133595114027265223329 3768100196335520448917497)
      ·
        refine ⟨2826075147251640336688123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3768100196335520448917497 2826075147251640336688123)
        ·
          refine ⟨4239112720877460505032185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2826075147251640336688123 4239112720877460505032185)
          ·
            refine ⟨3179334540658095378774139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4239112720877460505032185 3179334540658095378774139)
            ·
              refine ⟨4769001810987143068161209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3179334540658095378774139 4769001810987143068161209)
              ·
                refine ⟨3576751358240357301120907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4769001810987143068161209 3576751358240357301120907)
                ·
                  refine ⟨5365127037360535951681361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3576751358240357301120907 5365127037360535951681361)
                  ·
                    refine ⟨4023845278020401963761021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5365127037360535951681361 4023845278020401963761021)
                    ·
                      refine ⟨1508941979257650736410383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4023845278020401963761021 1508941979257650736410383)
                      ·
                        rfl

theorem cell23_2938654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_2938654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938654 prefixEnd_2938654 := by exact prefixLift 2938654
  have htrace : WordTrace (prefixWord ++ tailWord_2938654) baseStart_2938654 baseEnd_2938654 := by
    simpa [prefixWord, tailWord_2938654, baseEnd_2938654] using wordTrace_append hprefix tailTrace_2938654
  have hstable : (prefixWord ++ tailWord_2938654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938654).length < 2 ^ (prefixWord ++ tailWord_2938654).sum := by decide
  have hdescent : baseEnd_2938654 < baseStart_2938654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938659 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 5]
def baseStart_2938659 : Nat := 118140960795 + 2938659 * 2 ^ 59
def prefixEnd_2938659 : Nat := 4983230072969 + 3 ^ 40 * 2938659 * 2
def baseEnd_2938659 : Nat := 1508944546660923216847859

theorem tailTrace_2938659 : CollatzResearch.WordTrace tailWord_2938659 prefixEnd_2938659 1508944546660923216847859 := by
  unfold tailWord_2938659
  simp only [CollatzResearch.WordTrace]
  refine ⟨107181699060747800845363031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71454466040498533896908687 107181699060747800845363031)
  ·
    refine ⟨160772548591121701268044547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107181699060747800845363031 160772548591121701268044547)
    ·
      refine ⟨241158822886682551902066821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160772548591121701268044547 241158822886682551902066821)
      ·
        refine ⟨45217279291252978481637529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 241158822886682551902066821 45217279291252978481637529)
        ·
          refine ⟨33912959468439733861228147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45217279291252978481637529 33912959468439733861228147)
          ·
            refine ⟨50869439202659600791842221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33912959468439733861228147 50869439202659600791842221)
            ·
              refine ⟨19076039700997350296940833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50869439202659600791842221 19076039700997350296940833)
              ·
                refine ⟨14307029775748012722705625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19076039700997350296940833 14307029775748012722705625)
                ·
                  refine ⟨10730272331811009542029219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14307029775748012722705625 10730272331811009542029219)
                  ·
                    refine ⟨16095408497716514313043829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10730272331811009542029219 16095408497716514313043829)
                    ·
                      refine ⟨1508944546660923216847859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16095408497716514313043829 1508944546660923216847859)
                      ·
                        rfl

theorem cell23_2938659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_2938659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938659 prefixEnd_2938659 := by exact prefixLift 2938659
  have htrace : WordTrace (prefixWord ++ tailWord_2938659) baseStart_2938659 baseEnd_2938659 := by
    simpa [prefixWord, tailWord_2938659, baseEnd_2938659] using wordTrace_append hprefix tailTrace_2938659
  have hstable : (prefixWord ++ tailWord_2938659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938659).length < 2 ^ (prefixWord ++ tailWord_2938659).sum := by decide
  have hdescent : baseEnd_2938659 < baseStart_2938659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938660 : List Nat := [2, 3, 1, 3, 2, 1, 3, 2, 1, 3, 2]
def baseStart_2938660 : Nat := 118140960795 + 2938660 * 2 ^ 59
def prefixEnd_2938660 : Nat := 4983230072969 + 3 ^ 40 * 2938660 * 2
def baseEnd_2938660 : Nat := 1508945060141577712935355

theorem tailTrace_2938660 : CollatzResearch.WordTrace tailWord_2938660 prefixEnd_2938660 1508945060141577712935355 := by
  unfold tailWord_2938660
  simp only [CollatzResearch.WordTrace]
  refine ⟨53590867766872089008074717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71454490355829452010766289 53590867766872089008074717)
  ·
    refine ⟨20096575412577033378028019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53590867766872089008074717 20096575412577033378028019)
    ·
      refine ⟨30144863118865550067042029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20096575412577033378028019 30144863118865550067042029)
      ·
        refine ⟨11304323669574581275140761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30144863118865550067042029 11304323669574581275140761)
        ·
          refine ⟨8478242752180935956355571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11304323669574581275140761 8478242752180935956355571)
          ·
            refine ⟨12717364128271403934533357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8478242752180935956355571 12717364128271403934533357)
            ·
              refine ⟨4769011548101776475450009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12717364128271403934533357 4769011548101776475450009)
              ·
                refine ⟨3576758661076332356587507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4769011548101776475450009 3576758661076332356587507)
                ·
                  refine ⟨5365137991614498534881261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3576758661076332356587507 5365137991614498534881261)
                  ·
                    refine ⟨2011926746855436950580473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5365137991614498534881261 2011926746855436950580473)
                    ·
                      refine ⟨1508945060141577712935355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2011926746855436950580473 1508945060141577712935355)
                      ·
                        rfl

theorem cell23_2938660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 1, 3, 2].length) (baseStart_2938660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938660 prefixEnd_2938660 := by exact prefixLift 2938660
  have htrace : WordTrace (prefixWord ++ tailWord_2938660) baseStart_2938660 baseEnd_2938660 := by
    simpa [prefixWord, tailWord_2938660, baseEnd_2938660] using wordTrace_append hprefix tailTrace_2938660
  have hstable : (prefixWord ++ tailWord_2938660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938660).length < 2 ^ (prefixWord ++ tailWord_2938660).sum := by decide
  have hdescent : baseEnd_2938660 < baseStart_2938660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938673 : List Nat := [1, 2, 2, 3, 2, 3, 1, 2, 1, 4, 2]
def baseStart_2938673 : Nat := 118140960795 + 2938673 * 2 ^ 59
def prefixEnd_2938673 : Nat := 4983230072969 + 3 ^ 40 * 2938673 * 2
def baseEnd_2938673 : Nat := 1508951735390086162072795

theorem tailTrace_2938673 : CollatzResearch.WordTrace tailWord_2938673 prefixEnd_2938673 1508951735390086162072795 := by
  unfold tailWord_2938673
  simp only [CollatzResearch.WordTrace]
  refine ⟨107182209682697081236372673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71454806455131387490915115 107182209682697081236372673)
  ·
    refine ⟨80386657262022810927279505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107182209682697081236372673 80386657262022810927279505)
    ·
      refine ⟨60289992946517108195459629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80386657262022810927279505 60289992946517108195459629)
      ·
        refine ⟨22608747354943915573297361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60289992946517108195459629 22608747354943915573297361)
        ·
          refine ⟨16956560516207936679973021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22608747354943915573297361 16956560516207936679973021)
          ·
            refine ⟨6358710193577976254989883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16956560516207936679973021 6358710193577976254989883)
            ·
              refine ⟨9538065290366964382484825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6358710193577976254989883 9538065290366964382484825)
              ·
                refine ⟨7153548967775223286863619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9538065290366964382484825 7153548967775223286863619)
                ·
                  refine ⟨10730323451662834930295429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7153548967775223286863619 10730323451662834930295429)
                  ·
                    refine ⟨2011935647186781549430393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10730323451662834930295429 2011935647186781549430393)
                    ·
                      refine ⟨1508951735390086162072795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2011935647186781549430393 1508951735390086162072795)
                      ·
                        rfl

theorem cell23_2938673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_2938673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938673 prefixEnd_2938673 := by exact prefixLift 2938673
  have htrace : WordTrace (prefixWord ++ tailWord_2938673) baseStart_2938673 baseEnd_2938673 := by
    simpa [prefixWord, tailWord_2938673, baseEnd_2938673] using wordTrace_append hprefix tailTrace_2938673
  have hstable : (prefixWord ++ tailWord_2938673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938673).length < 2 ^ (prefixWord ++ tailWord_2938673).sum := by decide
  have hdescent : baseEnd_2938673 < baseStart_2938673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938677 : List Nat := [1, 3, 3, 1, 4, 1, 3, 1, 1, 3, 2]
def baseStart_2938677 : Nat := 118140960795 + 2938677 * 2 ^ 59
def prefixEnd_2938677 : Nat := 4983230072969 + 3 ^ 40 * 2938677 * 2
def baseEnd_2938677 : Nat := 1508953789312704146422777

theorem tailTrace_2938677 : CollatzResearch.WordTrace tailWord_2938677 prefixEnd_2938677 1508953789312704146422777 := by
  unfold tailWord_2938677
  simp only [CollatzResearch.WordTrace]
  refine ⟨107182355574682589919518285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71454903716455059946345523 107182355574682589919518285)
  ·
    refine ⟨40193383340505971219819357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107182355574682589919518285 40193383340505971219819357)
    ·
      refine ⟨15072518752689739207432259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40193383340505971219819357 15072518752689739207432259)
      ·
        refine ⟨22608778129034608811148389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15072518752689739207432259 22608778129034608811148389)
        ·
          refine ⟨4239145899193989152090323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22608778129034608811148389 4239145899193989152090323)
          ·
            refine ⟨6358718848790983728135485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4239145899193989152090323 6358718848790983728135485)
            ·
              refine ⟨2384519568296618898050807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6358718848790983728135485 2384519568296618898050807)
              ·
                refine ⟨3576779352444928347076211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2384519568296618898050807 3576779352444928347076211)
                ·
                  refine ⟨5365169028667392520614317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3576779352444928347076211 5365169028667392520614317)
                  ·
                    refine ⟨2011938385750272195230369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5365169028667392520614317 2011938385750272195230369)
                    ·
                      refine ⟨1508953789312704146422777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2011938385750272195230369 1508953789312704146422777)
                      ·
                        rfl

theorem cell23_2938677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_2938677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938677 prefixEnd_2938677 := by exact prefixLift 2938677
  have htrace : WordTrace (prefixWord ++ tailWord_2938677) baseStart_2938677 baseEnd_2938677 := by
    simpa [prefixWord, tailWord_2938677, baseEnd_2938677] using wordTrace_append hprefix tailTrace_2938677
  have hstable : (prefixWord ++ tailWord_2938677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938677).length < 2 ^ (prefixWord ++ tailWord_2938677).sum := by decide
  have hdescent : baseEnd_2938677 < baseStart_2938677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938706 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_2938706 : Nat := 118140960795 + 2938706 * 2 ^ 59
def prefixEnd_2938706 : Nat := 4983230072969 + 3 ^ 40 * 2938706 * 2
def baseEnd_2938706 : Nat := 1508968680251684532960143

theorem tailTrace_2938706 : CollatzResearch.WordTrace tailWord_2938706 prefixEnd_2938706 1508968680251684532960143 := by
  unfold tailWord_2938706
  simp only [CollatzResearch.WordTrace]
  refine ⟨26795853322894381968080993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71455608861051685248215981 26795853322894381968080993)
  ·
    refine ⟨20096889992170786476060745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26795853322894381968080993 20096889992170786476060745)
    ·
      refine ⟨15072667494128089857045559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20096889992170786476060745 15072667494128089857045559)
      ·
        refine ⟨22609001241192134785568339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15072667494128089857045559 22609001241192134785568339)
        ·
          refine ⟨33913501861788202178352509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22609001241192134785568339 33913501861788202178352509)
          ·
            refine ⟨12717563198170575816882191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33913501861788202178352509 12717563198170575816882191)
            ·
              refine ⟨19076344797255863725323287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12717563198170575816882191 19076344797255863725323287)
              ·
                refine ⟨28614517195883795587984931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19076344797255863725323287 28614517195883795587984931)
                ·
                  refine ⟨42921775793825693381977397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28614517195883795587984931 42921775793825693381977397)
                  ·
                    refine ⟨4023916480671158754560381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42921775793825693381977397 4023916480671158754560381)
                    ·
                      refine ⟨1508968680251684532960143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4023916480671158754560381 1508968680251684532960143)
                      ·
                        rfl

theorem cell23_2938706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_2938706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938706 prefixEnd_2938706 := by exact prefixLift 2938706
  have htrace : WordTrace (prefixWord ++ tailWord_2938706) baseStart_2938706 baseEnd_2938706 := by
    simpa [prefixWord, tailWord_2938706, baseEnd_2938706] using wordTrace_append hprefix tailTrace_2938706
  have hstable : (prefixWord ++ tailWord_2938706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938706).length < 2 ^ (prefixWord ++ tailWord_2938706).sum := by decide
  have hdescent : baseEnd_2938706 < baseStart_2938706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938746 : List Nat := [3, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4]
def baseStart_2938746 : Nat := 118140960795 + 2938746 * 2 ^ 59
def prefixEnd_2938746 : Nat := 4983230072969 + 3 ^ 40 * 2938746 * 2
def baseEnd_2938746 : Nat := 1508989219477864376459959

theorem tailTrace_2938746 : CollatzResearch.WordTrace tailWord_2938746 prefixEnd_2938746 1508989219477864376459959 := by
  unfold tailWord_2938746
  simp only [CollatzResearch.WordTrace]
  refine ⟨26796218052858153675945023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71456581474288409802520061 26796218052858153675945023)
  ·
    refine ⟨40194327079287230513917535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26796218052858153675945023 40194327079287230513917535)
    ·
      refine ⟨60291490618930845770876303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40194327079287230513917535 60291490618930845770876303)
      ·
        refine ⟨90437235928396268656314455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60291490618930845770876303 90437235928396268656314455)
        ·
          refine ⟨135655853892594402984471683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90437235928396268656314455 135655853892594402984471683)
          ·
            refine ⟨203483780838891604476707525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135655853892594402984471683 203483780838891604476707525)
            ·
              refine ⟨38153208907292175839382661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 203483780838891604476707525 38153208907292175839382661)
              ·
                refine ⟨7153726670117282969884249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38153208907292175839382661 7153726670117282969884249)
                ·
                  refine ⟨5365295002587962227413187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7153726670117282969884249 5365295002587962227413187)
                  ·
                    refine ⟨8047942503881943341119781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5365295002587962227413187 8047942503881943341119781)
                    ·
                      refine ⟨1508989219477864376459959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8047942503881943341119781 1508989219477864376459959)
                      ·
                        rfl

theorem cell23_2938746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_2938746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938746 prefixEnd_2938746 := by exact prefixLift 2938746
  have htrace : WordTrace (prefixWord ++ tailWord_2938746) baseStart_2938746 baseEnd_2938746 := by
    simpa [prefixWord, tailWord_2938746, baseEnd_2938746] using wordTrace_append hprefix tailTrace_2938746
  have hstable : (prefixWord ++ tailWord_2938746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938746).length < 2 ^ (prefixWord ++ tailWord_2938746).sum := by decide
  have hdescent : baseEnd_2938746 < baseStart_2938746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938816 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 3, 5]
def baseStart_2938816 : Nat := 118140960795 + 2938816 * 2 ^ 59
def prefixEnd_2938816 : Nat := 4983230072969 + 3 ^ 40 * 2938816 * 2
def baseEnd_2938816 : Nat := 503008387707893034194879

theorem tailTrace_2938816 : CollatzResearch.WordTrace tailWord_2938816 prefixEnd_2938816 503008387707893034194879 := by
  unfold tailWord_2938816
  simp only [CollatzResearch.WordTrace]
  refine ⟨53593712660589508329414151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71458283547452677772552201 53593712660589508329414151)
  ·
    refine ⟨80390568990884262494121227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53593712660589508329414151 80390568990884262494121227)
    ·
      refine ⟨120585853486326393741181841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80390568990884262494121227 120585853486326393741181841)
      ·
        refine ⟨90439390114744795305886381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120585853486326393741181841 90439390114744795305886381)
        ·
          refine ⟨33914771293029298239707393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90439390114744795305886381 33914771293029298239707393)
          ·
            refine ⟨25436078469771973679780545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33914771293029298239707393 25436078469771973679780545)
            ·
              refine ⟨19077058852328980259835409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25436078469771973679780545 19077058852328980259835409)
              ·
                refine ⟨14307794139246735194876557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19077058852328980259835409 14307794139246735194876557)
                ·
                  refine ⟨5365422802217525698078709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14307794139246735194876557 5365422802217525698078709)
                  ·
                    refine ⟨503008387707893034194879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5365422802217525698078709 503008387707893034194879)
                    ·
                      rfl

theorem cell23_2938816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 3, 5].length) (baseStart_2938816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938816 prefixEnd_2938816 := by exact prefixLift 2938816
  have htrace : WordTrace (prefixWord ++ tailWord_2938816) baseStart_2938816 baseEnd_2938816 := by
    simpa [prefixWord, tailWord_2938816, baseEnd_2938816] using wordTrace_append hprefix tailTrace_2938816
  have hstable : (prefixWord ++ tailWord_2938816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938816).length < 2 ^ (prefixWord ++ tailWord_2938816).sum := by decide
  have hdescent : baseEnd_2938816 < baseStart_2938816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938823 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 6, 3, 2]
def baseStart_2938823 : Nat := 118140960795 + 2938823 * 2 ^ 59
def prefixEnd_2938823 : Nat := 4983230072969 + 3 ^ 40 * 2938823 * 2
def baseEnd_2938823 : Nat := 1509028757488260575197105

theorem tailTrace_2938823 : CollatzResearch.WordTrace tailWord_2938823 prefixEnd_2938823 1509028757488260575197105 := by
  unfold tailWord_2938823
  simp only [CollatzResearch.WordTrace]
  refine ⟨107187680632153656854333123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71458453754769104569555415 107187680632153656854333123)
  ·
    refine ⟨160781520948230485281499685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107187680632153656854333123 160781520948230485281499685)
    ·
      refine ⟨30146535177793215990281191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160781520948230485281499685 30146535177793215990281191)
      ·
        refine ⟨45219802766689823985421787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30146535177793215990281191 45219802766689823985421787)
        ·
          refine ⟨67829704150034735978132681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45219802766689823985421787 67829704150034735978132681)
          ·
            refine ⟨50872278112526051983599511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67829704150034735978132681 50872278112526051983599511)
            ·
              refine ⟨76308417168789077975399267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50872278112526051983599511 76308417168789077975399267)
              ·
                refine ⟨114462625753183616963098901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76308417168789077975399267 114462625753183616963098901)
                ·
                  refine ⟨5365435582180482045145261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 114462625753183616963098901 5365435582180482045145261)
                  ·
                    refine ⟨2012038343317680766929473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5365435582180482045145261 2012038343317680766929473)
                    ·
                      refine ⟨1509028757488260575197105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2012038343317680766929473 1509028757488260575197105)
                      ·
                        rfl

theorem cell23_2938823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 3, 2].length) (baseStart_2938823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938823 prefixEnd_2938823 := by exact prefixLift 2938823
  have htrace : WordTrace (prefixWord ++ tailWord_2938823) baseStart_2938823 baseEnd_2938823 := by
    simpa [prefixWord, tailWord_2938823, baseEnd_2938823] using wordTrace_append hprefix tailTrace_2938823
  have hstable : (prefixWord ++ tailWord_2938823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938823).length < 2 ^ (prefixWord ++ tailWord_2938823).sum := by decide
  have hdescent : baseEnd_2938823 < baseStart_2938823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938840 : List Nat := [2, 1, 2, 2, 2, 2, 4, 1, 2, 3, 2]
def baseStart_2938840 : Nat := 118140960795 + 2938840 * 2 ^ 59
def prefixEnd_2938840 : Nat := 4983230072969 + 3 ^ 40 * 2938840 * 2
def baseEnd_2938840 : Nat := 1509037486659387008684527

theorem tailTrace_2938840 : CollatzResearch.WordTrace tailWord_2938840 prefixEnd_2938840 1509037486659387008684527 := by
  unfold tailWord_2938840
  simp only [CollatzResearch.WordTrace]
  refine ⟨53594150336546034378850987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71458867115394712505134649 53594150336546034378850987)
  ·
    refine ⟨80391225504819051568276481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53594150336546034378850987 80391225504819051568276481)
    ·
      refine ⟨60293419128614288676207361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80391225504819051568276481 60293419128614288676207361)
      ·
        refine ⟨45220064346460716507155521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60293419128614288676207361 45220064346460716507155521)
        ·
          refine ⟨33915048259845537380366641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45220064346460716507155521 33915048259845537380366641)
          ·
            refine ⟨25436286194884153035274981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33915048259845537380366641 25436286194884153035274981)
            ·
              refine ⟨4769303661540778694114059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25436286194884153035274981 4769303661540778694114059)
              ·
                refine ⟨7153955492311168041171089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4769303661540778694114059 7153955492311168041171089)
                ·
                  refine ⟨5365466619233376030878317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7153955492311168041171089 5365466619233376030878317)
                  ·
                    refine ⟨2012049982212516011579369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5365466619233376030878317 2012049982212516011579369)
                    ·
                      refine ⟨1509037486659387008684527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2012049982212516011579369 1509037486659387008684527)
                      ·
                        rfl

theorem cell23_2938840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_2938840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938840 prefixEnd_2938840 := by exact prefixLift 2938840
  have htrace : WordTrace (prefixWord ++ tailWord_2938840) baseStart_2938840 baseEnd_2938840 := by
    simpa [prefixWord, tailWord_2938840, baseEnd_2938840] using wordTrace_append hprefix tailTrace_2938840
  have hstable : (prefixWord ++ tailWord_2938840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938840).length < 2 ^ (prefixWord ++ tailWord_2938840).sum := by decide
  have hdescent : baseEnd_2938840 < baseStart_2938840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938873 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 3, 2, 3]
def baseStart_2938873 : Nat := 118140960795 + 2938873 * 2 ^ 59
def prefixEnd_2938873 : Nat := 4983230072969 + 3 ^ 40 * 2938873 * 2
def baseEnd_2938873 : Nat := 1509054431520985379571875

theorem tailTrace_2938873 : CollatzResearch.WordTrace tailWord_2938873 prefixEnd_2938873 1509054431520985379571875 := by
  unfold tailWord_2938873
  simp only [CollatzResearch.WordTrace]
  refine ⟨107189504281972515393653273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71459669521315010262435515 107189504281972515393653273)
  ·
    refine ⟨80392128211479386545239955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107189504281972515393653273 80392128211479386545239955)
    ·
      refine ⟨120588192317219079817859933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80392128211479386545239955 120588192317219079817859933)
      ·
        refine ⟨45220572118957154931697475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120588192317219079817859933 45220572118957154931697475)
        ·
          refine ⟨67830858178435732397546213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45220572118957154931697475 67830858178435732397546213)
          ·
            refine ⟨12718285908456699824539915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67830858178435732397546213 12718285908456699824539915)
            ·
              refine ⟨19077428862685049736809873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12718285908456699824539915 19077428862685049736809873)
              ·
                refine ⟨14308071647013787302607405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19077428862685049736809873 14308071647013787302607405)
                ·
                  refine ⟨5365526867630170238477777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14308071647013787302607405 5365526867630170238477777)
                  ·
                    refine ⟨4024145150722627678858333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5365526867630170238477777 4024145150722627678858333)
                    ·
                      refine ⟨1509054431520985379571875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4024145150722627678858333 1509054431520985379571875)
                      ·
                        rfl

theorem cell23_2938873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_2938873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938873 prefixEnd_2938873 := by exact prefixLift 2938873
  have htrace : WordTrace (prefixWord ++ tailWord_2938873) baseStart_2938873 baseEnd_2938873 := by
    simpa [prefixWord, tailWord_2938873, baseEnd_2938873] using wordTrace_append hprefix tailTrace_2938873
  have hstable : (prefixWord ++ tailWord_2938873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938873).length < 2 ^ (prefixWord ++ tailWord_2938873).sum := by decide
  have hdescent : baseEnd_2938873 < baseStart_2938873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938887 : List Nat := [1, 1, 4, 3, 1, 3, 1, 2, 3, 2, 2]
def baseStart_2938887 : Nat := 118140960795 + 2938887 * 2 ^ 59
def prefixEnd_2938887 : Nat := 4983230072969 + 3 ^ 40 * 2938887 * 2
def baseEnd_2938887 : Nat := 1509061620250148324796811

theorem tailTrace_2938887 : CollatzResearch.WordTrace tailWord_2938887 prefixEnd_2938887 1509061620250148324796811 := by
  unfold tailWord_2938887
  simp only [CollatzResearch.WordTrace]
  refine ⟨107190014903921795784662915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71460009935947863856441943 107190014903921795784662915)
  ·
    refine ⟨160785022355882693676994373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107190014903921795784662915 160785022355882693676994373)
    ·
      refine ⟨30147191691728005064436445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160785022355882693676994373 30147191691728005064436445)
      ·
        refine ⟨11305196884398001899163667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30147191691728005064436445 11305196884398001899163667)
        ·
          refine ⟨16957795326597002848745501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11305196884398001899163667 16957795326597002848745501)
          ·
            refine ⟨6359173247473876068279563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16957795326597002848745501 6359173247473876068279563)
            ·
              refine ⟨9538759871210814102419345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6359173247473876068279563 9538759871210814102419345)
              ·
                refine ⟨7154069903408110576814509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9538759871210814102419345 7154069903408110576814509)
                ·
                  refine ⟨2682776213778041466305441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7154069903408110576814509 2682776213778041466305441)
                  ·
                    refine ⟨2012082160333531099729081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2682776213778041466305441 2012082160333531099729081)
                    ·
                      refine ⟨1509061620250148324796811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2012082160333531099729081 1509061620250148324796811)
                      ·
                        rfl

theorem cell23_2938887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_2938887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938887 prefixEnd_2938887 := by exact prefixLift 2938887
  have htrace : WordTrace (prefixWord ++ tailWord_2938887) baseStart_2938887 baseEnd_2938887 := by
    simpa [prefixWord, tailWord_2938887, baseEnd_2938887] using wordTrace_append hprefix tailTrace_2938887
  have hstable : (prefixWord ++ tailWord_2938887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938887).length < 2 ^ (prefixWord ++ tailWord_2938887).sum := by decide
  have hdescent : baseEnd_2938887 < baseStart_2938887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938904 : List Nat := [2, 1, 2, 3, 2, 1, 4, 3, 1, 2, 2]
def baseStart_2938904 : Nat := 118140960795 + 2938904 * 2 ^ 59
def prefixEnd_2938904 : Nat := 4983230072969 + 3 ^ 40 * 2938904 * 2
def baseEnd_2938904 : Nat := 1509070349421274758284233

theorem tailTrace_2938904 : CollatzResearch.WordTrace tailWord_2938904 prefixEnd_2938904 1509070349421274758284233 := by
  unfold tailWord_2938904
  simp only [CollatzResearch.WordTrace]
  refine ⟨53595317472430103844015883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71460423296573471792021177 53595317472430103844015883)
  ·
    refine ⟨80392976208645155766023825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53595317472430103844015883 80392976208645155766023825)
    ·
      refine ⟨60294732156483866824517869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80392976208645155766023825 60294732156483866824517869)
      ·
        refine ⟨22610524558681450059194201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60294732156483866824517869 22610524558681450059194201)
        ·
          refine ⟨16957893419011087544395651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22610524558681450059194201 16957893419011087544395651)
          ·
            refine ⟨25436840128516631316593477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16957893419011087544395651 25436840128516631316593477)
            ·
              refine ⟨4769407524096868371861277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25436840128516631316593477 4769407524096868371861277)
              ·
                refine ⟨1788527821536325639447979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4769407524096868371861277 1788527821536325639447979)
                ·
                  refine ⟨2682791732304488459171969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1788527821536325639447979 2682791732304488459171969)
                  ·
                    refine ⟨2012093799228366344378977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2682791732304488459171969 2012093799228366344378977)
                    ·
                      refine ⟨1509070349421274758284233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2012093799228366344378977 1509070349421274758284233)
                      ·
                        rfl

theorem cell23_2938904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_2938904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938904 prefixEnd_2938904 := by exact prefixLift 2938904
  have htrace : WordTrace (prefixWord ++ tailWord_2938904) baseStart_2938904 baseEnd_2938904 := by
    simpa [prefixWord, tailWord_2938904, baseEnd_2938904] using wordTrace_append hprefix tailTrace_2938904
  have hstable : (prefixWord ++ tailWord_2938904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938904).length < 2 ^ (prefixWord ++ tailWord_2938904).sum := by decide
  have hdescent : baseEnd_2938904 < baseStart_2938904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938937 : List Nat := [1, 2, 1, 5, 3, 2, 1, 1, 1, 3, 3]
def baseStart_2938937 : Nat := 118140960795 + 2938937 * 2 ^ 59
def prefixEnd_2938937 : Nat := 4983230072969 + 3 ^ 40 * 2938937 * 2
def baseEnd_2938937 : Nat := 1509087294282873129171581

theorem tailTrace_2938937 : CollatzResearch.WordTrace tailWord_2938937 prefixEnd_2938937 1509087294282873129171581 := by
  unfold tailWord_2938937
  simp only [CollatzResearch.WordTrace]
  refine ⟨107191838553740654323983065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71461225702493769549322043 107191838553740654323983065)
  ·
    refine ⟨80393878915305490742987299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107191838553740654323983065 80393878915305490742987299)
    ·
      refine ⟨120590818372958236114480949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80393878915305490742987299 120590818372958236114480949)
      ·
        refine ⟨11305389222464834635732589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120590818372958236114480949 11305389222464834635732589)
        ·
          refine ⟨4239520958424312988399721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11305389222464834635732589 4239520958424312988399721)
          ·
            refine ⟨3179640718818234741299791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4239520958424312988399721 3179640718818234741299791)
            ·
              refine ⟨4769461078227352111949687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3179640718818234741299791 4769461078227352111949687)
              ·
                refine ⟨7154191617341028167924531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4769461078227352111949687 7154191617341028167924531)
                ·
                  refine ⟨10731287426011542251886797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7154191617341028167924531 10731287426011542251886797)
                  ·
                    refine ⟨4024232784754328344457549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10731287426011542251886797 4024232784754328344457549)
                    ·
                      refine ⟨1509087294282873129171581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4024232784754328344457549 1509087294282873129171581)
                      ·
                        rfl

theorem cell23_2938937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_2938937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938937 prefixEnd_2938937 := by exact prefixLift 2938937
  have htrace : WordTrace (prefixWord ++ tailWord_2938937) baseStart_2938937 baseEnd_2938937 := by
    simpa [prefixWord, tailWord_2938937, baseEnd_2938937] using wordTrace_append hprefix tailTrace_2938937
  have hstable : (prefixWord ++ tailWord_2938937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938937).length < 2 ^ (prefixWord ++ tailWord_2938937).sum := by decide
  have hdescent : baseEnd_2938937 < baseStart_2938937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938950 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_2938950 : Nat := 118140960795 + 2938950 * 2 ^ 59
def prefixEnd_2938950 : Nat := 4983230072969 + 3 ^ 40 * 2938950 * 2
def baseEnd_2938950 : Nat := 1509093969531381578309021

theorem tailTrace_2938950 : CollatzResearch.WordTrace tailWord_2938950 prefixEnd_2938950 1509093969531381578309021 := by
  unfold tailWord_2938950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3349759771959173673256447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 71461541801795705029470869 3349759771959173673256447)
  ·
    refine ⟨5024639657938760509884671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3349759771959173673256447 5024639657938760509884671)
    ·
      refine ⟨7536959486908140764827007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5024639657938760509884671 7536959486908140764827007)
      ·
        refine ⟨11305439230362211147240511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7536959486908140764827007 11305439230362211147240511)
        ·
          refine ⟨16958158845543316720860767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11305439230362211147240511 16958158845543316720860767)
          ·
            refine ⟨25437238268314975081291151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16958158845543316720860767 25437238268314975081291151)
            ·
              refine ⟨38155857402472462621936727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25437238268314975081291151 38155857402472462621936727)
              ·
                refine ⟨57233786103708693932905091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38155857402472462621936727 57233786103708693932905091)
                ·
                  refine ⟨85850679155563040899357637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57233786103708693932905091 85850679155563040899357637)
                  ·
                    refine ⟨16097002341668070168629557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85850679155563040899357637 16097002341668070168629557)
                    ·
                      refine ⟨1509093969531381578309021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16097002341668070168629557 1509093969531381578309021)
                      ·
                        rfl

theorem cell23_2938950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_2938950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938950 prefixEnd_2938950 := by exact prefixLift 2938950
  have htrace : WordTrace (prefixWord ++ tailWord_2938950) baseStart_2938950 baseEnd_2938950 := by
    simpa [prefixWord, tailWord_2938950, baseEnd_2938950] using wordTrace_append hprefix tailTrace_2938950
  have hstable : (prefixWord ++ tailWord_2938950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938950).length < 2 ^ (prefixWord ++ tailWord_2938950).sum := by decide
  have hdescent : baseEnd_2938950 < baseStart_2938950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938977 : List Nat := [1, 2, 3, 1, 1, 2, 1, 6, 2, 2, 2]
def baseStart_2938977 : Nat := 118140960795 + 2938977 * 2 ^ 59
def prefixEnd_2938977 : Nat := 4983230072969 + 3 ^ 40 * 2938977 * 2
def baseEnd_2938977 : Nat := 1509107833509052972671397

theorem tailTrace_2938977 : CollatzResearch.WordTrace tailWord_2938977 prefixEnd_2938977 1509107833509052972671397 := by
  unfold tailWord_2938977
  simp only [CollatzResearch.WordTrace]
  refine ⟨107193297473595741155439185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71462198315730494103626123 107193297473595741155439185)
  ·
    refine ⟨80394973105196805866579389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107193297473595741155439185 80394973105196805866579389)
    ·
      refine ⟨30148114914448802199967271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80394973105196805866579389 30148114914448802199967271)
      ·
        refine ⟨45222172371673203299950907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30148114914448802199967271 45222172371673203299950907)
        ·
          refine ⟨67833258557509804949926361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45222172371673203299950907 67833258557509804949926361)
          ·
            refine ⟨50874943918132353712444771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67833258557509804949926361 50874943918132353712444771)
            ·
              refine ⟨76312415877198530568667157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50874943918132353712444771 76312415877198530568667157)
              ·
                refine ⟨3577144494243681120406273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76312415877198530568667157 3577144494243681120406273)
                ·
                  refine ⟨2682858370682760840304705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3577144494243681120406273 2682858370682760840304705)
                  ·
                    refine ⟨2012143778012070630228529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2682858370682760840304705 2012143778012070630228529)
                    ·
                      refine ⟨1509107833509052972671397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2012143778012070630228529 1509107833509052972671397)
                      ·
                        rfl

theorem cell23_2938977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_2938977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938977 prefixEnd_2938977 := by exact prefixLift 2938977
  have htrace : WordTrace (prefixWord ++ tailWord_2938977) baseStart_2938977 baseEnd_2938977 := by
    simpa [prefixWord, tailWord_2938977, baseEnd_2938977] using wordTrace_append hprefix tailTrace_2938977
  have hstable : (prefixWord ++ tailWord_2938977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938977).length < 2 ^ (prefixWord ++ tailWord_2938977).sum := by decide
  have hdescent : baseEnd_2938977 < baseStart_2938977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938993 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 1, 5, 3]
def baseStart_2938993 : Nat := 118140960795 + 2938993 * 2 ^ 59
def prefixEnd_2938993 : Nat := 4983230072969 + 3 ^ 40 * 2938993 * 2
def baseEnd_2938993 : Nat := 1509116049199524910071323

theorem tailTrace_2938993 : CollatzResearch.WordTrace tailWord_2938993 prefixEnd_2938993 1509116049199524910071323 := by
  unfold tailWord_2938993
  simp only [CollatzResearch.WordTrace]
  refine ⟨107193881041537775888021633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71462587361025183925347755 107193881041537775888021633)
  ·
    refine ⟨80395410781153331916016225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107193881041537775888021633 80395410781153331916016225)
    ·
      refine ⟨60296558085864998937012169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80395410781153331916016225 60296558085864998937012169)
      ·
        refine ⟨45222418564398749202759127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60296558085864998937012169 45222418564398749202759127)
        ·
          refine ⟨67833627846598123804138691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45222418564398749202759127 67833627846598123804138691)
          ·
            refine ⟨101750441769897185706208037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67833627846598123804138691 101750441769897185706208037)
            ·
              refine ⟨19078207831855722319914007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101750441769897185706208037 19078207831855722319914007)
              ·
                refine ⟨28617311747783583479871011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19078207831855722319914007 28617311747783583479871011)
                ·
                  refine ⟨42925967621675375219806517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28617311747783583479871011 42925967621675375219806517)
                  ·
                    refine ⟨4024309464532066426856861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42925967621675375219806517 4024309464532066426856861)
                    ·
                      refine ⟨1509116049199524910071323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4024309464532066426856861 1509116049199524910071323)
                      ·
                        rfl

theorem cell23_2938993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_2938993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938993 prefixEnd_2938993 := by exact prefixLift 2938993
  have htrace : WordTrace (prefixWord ++ tailWord_2938993) baseStart_2938993 baseEnd_2938993 := by
    simpa [prefixWord, tailWord_2938993, baseEnd_2938993] using wordTrace_append hprefix tailTrace_2938993
  have hstable : (prefixWord ++ tailWord_2938993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938993).length < 2 ^ (prefixWord ++ tailWord_2938993).sum := by decide
  have hdescent : baseEnd_2938993 < baseStart_2938993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2938994 : List Nat := [3, 2, 1, 2, 2, 3, 1, 3, 2, 2, 2]
def baseStart_2938994 : Nat := 118140960795 + 2938994 * 2 ^ 59
def prefixEnd_2938994 : Nat := 4983230072969 + 3 ^ 40 * 2938994 * 2
def baseEnd_2938994 : Nat := 1509116562680179406158819

theorem tailTrace_2938994 : CollatzResearch.WordTrace tailWord_2938994 prefixEnd_2938994 1509116562680179406158819 := by
  unfold tailWord_2938994
  simp only [CollatzResearch.WordTrace]
  refine ⟨26798479378633538264702009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71462611676356102039205357 26798479378633538264702009)
  ·
    refine ⟨20098859533975153698526507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26798479378633538264702009 20098859533975153698526507)
    ·
      refine ⟨30148289300962730547789761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20098859533975153698526507 30148289300962730547789761)
      ·
        refine ⟨22611216975722047910842321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30148289300962730547789761 22611216975722047910842321)
        ·
          refine ⟨16958412731791535933131741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22611216975722047910842321 16958412731791535933131741)
          ·
            refine ⟨6359404774421825974924403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16958412731791535933131741 6359404774421825974924403)
            ·
              refine ⟨9539107161632738962386605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6359404774421825974924403 9539107161632738962386605)
              ·
                refine ⟨3577165185612277110894977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9539107161632738962386605 3577165185612277110894977)
                ·
                  refine ⟨2682873889209207833171233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3577165185612277110894977 2682873889209207833171233)
                  ·
                    refine ⟨2012155416906905874878425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2682873889209207833171233 2012155416906905874878425)
                    ·
                      refine ⟨1509116562680179406158819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2012155416906905874878425 1509116562680179406158819)
                      ·
                        rfl

theorem cell23_2938994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_2938994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2938994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2938994 prefixEnd_2938994 := by exact prefixLift 2938994
  have htrace : WordTrace (prefixWord ++ tailWord_2938994) baseStart_2938994 baseEnd_2938994 := by
    simpa [prefixWord, tailWord_2938994, baseEnd_2938994] using wordTrace_append hprefix tailTrace_2938994
  have hstable : (prefixWord ++ tailWord_2938994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2938994).length < 2 ^ (prefixWord ++ tailWord_2938994).sum := by decide
  have hdescent : baseEnd_2938994 < baseStart_2938994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2938994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939028 : List Nat := [2, 4, 2, 3, 1, 1, 2, 2, 2, 2, 2]
def baseStart_2939028 : Nat := 118140960795 + 2939028 * 2 ^ 59
def prefixEnd_2939028 : Nat := 4983230072969 + 3 ^ 40 * 2939028 * 2
def baseEnd_2939028 : Nat := 1509134021022432273133663

theorem tailTrace_2939028 : CollatzResearch.WordTrace tailWord_2939028 prefixEnd_2939028 1509134021022432273133663 := by
  unfold tailWord_2939028
  simp only [CollatzResearch.WordTrace]
  refine ⟨53597578798205488432772869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71463438397607317910363825 53597578798205488432772869)
  ·
    refine ⟨10049546024663529081144913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53597578798205488432772869 10049546024663529081144913)
    ·
      refine ⟨7537159518497646810858685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10049546024663529081144913 7537159518497646810858685)
      ·
        refine ⟨2826434819436617554072007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7537159518497646810858685 2826434819436617554072007)
        ·
          refine ⟨4239652229154926331108011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2826434819436617554072007 4239652229154926331108011)
          ·
            refine ⟨6359478343732389496662017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4239652229154926331108011 6359478343732389496662017)
            ·
              refine ⟨4769608757799292122496513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6359478343732389496662017 4769608757799292122496513)
              ·
                refine ⟨3577206568349469091872385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4769608757799292122496513 3577206568349469091872385)
                ·
                  refine ⟨2682904926262101818904289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3577206568349469091872385 2682904926262101818904289)
                  ·
                    refine ⟨2012178694696576364178217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2682904926262101818904289 2012178694696576364178217)
                    ·
                      refine ⟨1509134021022432273133663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2012178694696576364178217 1509134021022432273133663)
                      ·
                        rfl

theorem cell23_2939028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_2939028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939028 prefixEnd_2939028 := by exact prefixLift 2939028
  have htrace : WordTrace (prefixWord ++ tailWord_2939028) baseStart_2939028 baseEnd_2939028 := by
    simpa [prefixWord, tailWord_2939028, baseEnd_2939028] using wordTrace_append hprefix tailTrace_2939028
  have hstable : (prefixWord ++ tailWord_2939028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939028).length < 2 ^ (prefixWord ++ tailWord_2939028).sum := by decide
  have hdescent : baseEnd_2939028 < baseStart_2939028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939077 : List Nat := [1, 3, 1, 1, 1, 1, 5, 5, 1, 4]
def baseStart_2939077 : Nat := 118140960795 + 2939077 * 2 ^ 59
def prefixEnd_2939077 : Nat := 4983230072969 + 3 ^ 40 * 2939077 * 2
def baseEnd_2939077 : Nat := 503053060524834193806979

theorem tailTrace_2939077 : CollatzResearch.WordTrace tailWord_2939077 prefixEnd_2939077 503053060524834193806979 := by
  unfold tailWord_2939077
  simp only [CollatzResearch.WordTrace]
  refine ⟨107196944773233458234079485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71464629848822305489386323 107196944773233458234079485)
  ·
    refine ⟨40198854289962546837779807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107196944773233458234079485 40198854289962546837779807)
    ·
      refine ⟨60298281434943820256669711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40198854289962546837779807 60298281434943820256669711)
      ·
        refine ⟨90447422152415730385004567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60298281434943820256669711 90447422152415730385004567)
        ·
          refine ⟨135671133228623595577506851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90447422152415730385004567 135671133228623595577506851)
          ·
            refine ⟨203506699842935393366260277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135671133228623595577506851 203506699842935393366260277)
            ·
              refine ⟨19078753110275193128086901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 203506699842935393366260277 19078753110275193128086901)
              ·
                refine ⟨1788633104088299355758147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19078753110275193128086901 1788633104088299355758147)
                ·
                  refine ⟨2682949656132449033637221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1788633104088299355758147 2682949656132449033637221)
                  ·
                    refine ⟨503053060524834193806979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2682949656132449033637221 503053060524834193806979)
                    ·
                      rfl

theorem cell23_2939077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 1, 4].length) (baseStart_2939077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939077 prefixEnd_2939077 := by exact prefixLift 2939077
  have htrace : WordTrace (prefixWord ++ tailWord_2939077) baseStart_2939077 baseEnd_2939077 := by
    simpa [prefixWord, tailWord_2939077, baseEnd_2939077] using wordTrace_append hprefix tailTrace_2939077
  have hstable : (prefixWord ++ tailWord_2939077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939077).length < 2 ^ (prefixWord ++ tailWord_2939077).sum := by decide
  have hdescent : baseEnd_2939077 < baseStart_2939077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939090 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 8]
def baseStart_2939090 : Nat := 118140960795 + 2939090 * 2 ^ 59
def prefixEnd_2939090 : Nat := 4983230072969 + 3 ^ 40 * 2939090 * 2
def baseEnd_2939090 : Nat := 167685095202556781173153

theorem tailTrace_2939090 : CollatzResearch.WordTrace tailWord_2939090 prefixEnd_2939090 167685095202556781173153 := by
  unfold tailWord_2939090
  simp only [CollatzResearch.WordTrace]
  refine ⟨26799354730546590363575681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71464945948124240969535149 26799354730546590363575681)
  ·
    refine ⟨20099516047909942772681761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26799354730546590363575681 20099516047909942772681761)
    ·
      refine ⟨15074637035932457079511321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20099516047909942772681761 15074637035932457079511321)
      ·
        refine ⟨11305977776949342809633491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15074637035932457079511321 11305977776949342809633491)
        ·
          refine ⟨16958966665424014214450237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11305977776949342809633491 16958966665424014214450237)
          ·
            refine ⟨6359612499534005330418839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16958966665424014214450237 6359612499534005330418839)
            ·
              refine ⟨9539418749301007995628259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6359612499534005330418839 9539418749301007995628259)
              ·
                refine ⟨14309128123951511993442389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9539418749301007995628259 14309128123951511993442389)
                ·
                  refine ⟨167685095202556781173153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14309128123951511993442389 167685095202556781173153)
                  ·
                    rfl

theorem cell23_2939090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_2939090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939090 prefixEnd_2939090 := by exact prefixLift 2939090
  have htrace : WordTrace (prefixWord ++ tailWord_2939090) baseStart_2939090 baseEnd_2939090 := by
    simpa [prefixWord, tailWord_2939090, baseEnd_2939090] using wordTrace_append hprefix tailTrace_2939090
  have hstable : (prefixWord ++ tailWord_2939090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939090).length < 2 ^ (prefixWord ++ tailWord_2939090).sum := by decide
  have hdescent : baseEnd_2939090 < baseStart_2939090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939094 : List Nat := [5, 2, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_2939094 : Nat := 118140960795 + 2939094 * 2 ^ 59
def prefixEnd_2939094 : Nat := 4983230072969 + 3 ^ 40 * 2939094 * 2
def baseEnd_2939094 : Nat := 503055970248543004969453

theorem tailTrace_2939094 : CollatzResearch.WordTrace tailWord_2939094 prefixEnd_2939094 503055970248543004969453 := by
  unfold tailWord_2939094
  simp only [CollatzResearch.WordTrace]
  refine ⟨6699847800885741883590521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 71465043209447913424965557 6699847800885741883590521)
  ·
    refine ⟨5024885850664306412692891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6699847800885741883590521 5024885850664306412692891)
    ·
      refine ⟨7537328775996459619039337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5024885850664306412692891 7537328775996459619039337)
      ·
        refine ⟨5652996581997344714279503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7537328775996459619039337 5652996581997344714279503)
        ·
          refine ⟨8479494872996017071419255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5652996581997344714279503 8479494872996017071419255)
          ·
            refine ⟨12719242309494025607128883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8479494872996017071419255 12719242309494025607128883)
            ·
              refine ⟨19078863464241038410693325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12719242309494025607128883 19078863464241038410693325)
              ·
                refine ⟨7154573799090389404009997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19078863464241038410693325 7154573799090389404009997)
                ·
                  refine ⟨2682965174658896026503749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7154573799090389404009997 2682965174658896026503749)
                  ·
                    refine ⟨503055970248543004969453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2682965174658896026503749 503055970248543004969453)
                    ·
                      rfl

theorem cell23_2939094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_2939094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939094 prefixEnd_2939094 := by exact prefixLift 2939094
  have htrace : WordTrace (prefixWord ++ tailWord_2939094) baseStart_2939094 baseEnd_2939094 := by
    simpa [prefixWord, tailWord_2939094, baseEnd_2939094] using wordTrace_append hprefix tailTrace_2939094
  have hstable : (prefixWord ++ tailWord_2939094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939094).length < 2 ^ (prefixWord ++ tailWord_2939094).sum := by decide
  have hdescent : baseEnd_2939094 < baseStart_2939094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939144 : List Nat := [2, 1, 3, 2, 3, 2, 1, 2, 2, 3, 2]
def baseStart_2939144 : Nat := 118140960795 + 2939144 * 2 ^ 59
def prefixEnd_2939144 : Nat := 4983230072969 + 3 ^ 40 * 2939144 * 2
def baseEnd_2939144 : Nat := 1509193584778353819283129

theorem tailTrace_2939144 : CollatzResearch.WordTrace tailWord_2939144 prefixEnd_2939144 1509193584778353819283129 := by
  unfold tailWord_2939144
  simp only [CollatzResearch.WordTrace]
  refine ⟨53599694231995364338384243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71466258975993819117845657 53599694231995364338384243)
  ·
    refine ⟨80399541347993046507576365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53599694231995364338384243 80399541347993046507576365)
    ·
      refine ⟨30149828005497392440341137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80399541347993046507576365 30149828005497392440341137)
      ·
        refine ⟨22612371004123044330255853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30149828005497392440341137 22612371004123044330255853)
        ·
          refine ⟨8479639126546141623845945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22612371004123044330255853 8479639126546141623845945)
          ·
            refine ⟨6359729344909606217884459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8479639126546141623845945 6359729344909606217884459)
            ·
              refine ⟨9539594017364409326826689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6359729344909606217884459 9539594017364409326826689)
              ·
                refine ⟨7154695513023306995120017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9539594017364409326826689 7154695513023306995120017)
                ·
                  refine ⟨5366021634767480246340013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7154695513023306995120017 5366021634767480246340013)
                  ·
                    refine ⟨2012258113037805092377505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5366021634767480246340013 2012258113037805092377505)
                    ·
                      refine ⟨1509193584778353819283129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2012258113037805092377505 1509193584778353819283129)
                      ·
                        rfl

theorem cell23_2939144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_2939144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939144 prefixEnd_2939144 := by exact prefixLift 2939144
  have htrace : WordTrace (prefixWord ++ tailWord_2939144) baseStart_2939144 baseEnd_2939144 := by
    simpa [prefixWord, tailWord_2939144, baseEnd_2939144] using wordTrace_append hprefix tailTrace_2939144
  have hstable : (prefixWord ++ tailWord_2939144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939144).length < 2 ^ (prefixWord ++ tailWord_2939144).sum := by decide
  have hdescent : baseEnd_2939144 < baseStart_2939144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939160 : List Nat := [2, 1, 2, 3, 1, 2, 1, 4, 1, 1, 5]
def baseStart_2939160 : Nat := 118140960795 + 2939160 * 2 ^ 59
def prefixEnd_2939160 : Nat := 4983230072969 + 3 ^ 40 * 2939160 * 2
def baseEnd_2939160 : Nat := 1509201800468825756683055

theorem tailTrace_2939160 : CollatzResearch.WordTrace tailWord_2939160 prefixEnd_2939160 1509201800468825756683055 := by
  unfold tailWord_2939160
  simp only [CollatzResearch.WordTrace]
  refine ⟨53599986015966381704675467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71466648021288508939567289 53599986015966381704675467)
  ·
    refine ⟨80399979023949572557013201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53599986015966381704675467 80399979023949572557013201)
    ·
      refine ⟨60299984267962179417759901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80399979023949572557013201 60299984267962179417759901)
      ·
        refine ⟨22612494100485817281659963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60299984267962179417759901 22612494100485817281659963)
        ·
          refine ⟨33918741150728725922489945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22612494100485817281659963 33918741150728725922489945)
          ·
            refine ⟨25439055863046544441867459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33918741150728725922489945 25439055863046544441867459)
            ·
              refine ⟨38158583794569816662801189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25439055863046544441867459 38158583794569816662801189)
              ·
                refine ⟨7154734461481840624275223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38158583794569816662801189 7154734461481840624275223)
                ·
                  refine ⟨10732101692222760936412835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7154734461481840624275223 10732101692222760936412835)
                  ·
                    refine ⟨16098152538334141404619253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10732101692222760936412835 16098152538334141404619253)
                    ·
                      refine ⟨1509201800468825756683055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16098152538334141404619253 1509201800468825756683055)
                      ·
                        rfl

theorem cell23_2939160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_2939160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939160 prefixEnd_2939160 := by exact prefixLift 2939160
  have htrace : WordTrace (prefixWord ++ tailWord_2939160) baseStart_2939160 baseEnd_2939160 := by
    simpa [prefixWord, tailWord_2939160, baseEnd_2939160] using wordTrace_append hprefix tailTrace_2939160
  have hstable : (prefixWord ++ tailWord_2939160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939160).length < 2 ^ (prefixWord ++ tailWord_2939160).sum := by decide
  have hdescent : baseEnd_2939160 < baseStart_2939160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939163 : List Nat := [1, 1, 1, 1, 1, 1, 7, 10]
def baseStart_2939163 : Nat := 118140960795 + 2939163 * 2 ^ 59
def prefixEnd_2939163 : Nat := 4983230072969 + 3 ^ 40 * 2939163 * 2
def baseEnd_2939163 : Nat := 55896420033732934997983

theorem tailTrace_2939163 : CollatzResearch.WordTrace tailWord_2939163 prefixEnd_2939163 55896420033732934997983 := by
  unfold tailWord_2939163
  simp only [CollatzResearch.WordTrace]
  refine ⟨107200081450921894921710143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71466720967281263281140095 107200081450921894921710143)
  ·
    refine ⟨160800122176382842382565215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107200081450921894921710143 160800122176382842382565215)
    ·
      refine ⟨241200183264574263573847823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160800122176382842382565215 241200183264574263573847823)
      ·
        refine ⟨361800274896861395360771735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 241200183264574263573847823 361800274896861395360771735)
        ·
          refine ⟨542700412345292093041157603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361800274896861395360771735 542700412345292093041157603)
          ·
            refine ⟨814050618517938139561736405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542700412345292093041157603 814050618517938139561736405)
            ·
              refine ⟨19079311371514175145978197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 814050618517938139561736405 19079311371514175145978197)
              ·
                refine ⟨55896420033732934997983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19079311371514175145978197 55896420033732934997983)
                ·
                  rfl

theorem cell23_2939163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 10].length) (baseStart_2939163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939163 prefixEnd_2939163 := by exact prefixLift 2939163
  have htrace : WordTrace (prefixWord ++ tailWord_2939163) baseStart_2939163 baseEnd_2939163 := by
    simpa [prefixWord, tailWord_2939163, baseEnd_2939163] using wordTrace_append hprefix tailTrace_2939163
  have hstable : (prefixWord ++ tailWord_2939163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939163).length < 2 ^ (prefixWord ++ tailWord_2939163).sum := by decide
  have hdescent : baseEnd_2939163 < baseStart_2939163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939201 : List Nat := [1, 2, 5, 2, 2, 1, 2, 2, 2, 4]
def baseStart_2939201 : Nat := 118140960795 + 2939201 * 2 ^ 59
def prefixEnd_2939201 : Nat := 4983230072969 + 3 ^ 40 * 2939201 * 2
def baseEnd_2939201 : Nat := 503074284391886698756789

theorem tailTrace_2939201 : CollatzResearch.WordTrace tailWord_2939201 prefixEnd_2939201 503074284391886698756789 := by
  unfold tailWord_2939201
  simp only [CollatzResearch.WordTrace]
  refine ⟨107201467424784227411593457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71467644949856151607728971 107201467424784227411593457)
  ·
    refine ⟨80401100568588170558695093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107201467424784227411593457 80401100568588170558695093)
    ·
      refine ⟨7537603178305140989877665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 80401100568588170558695093 7537603178305140989877665)
      ·
        refine ⟨5653202383728855742408249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7537603178305140989877665 5653202383728855742408249)
        ·
          refine ⟨4239901787796641806806187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5653202383728855742408249 4239901787796641806806187)
          ·
            refine ⟨6359852681694962710209281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4239901787796641806806187 6359852681694962710209281)
            ·
              refine ⟨4769889511271222032656961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6359852681694962710209281 4769889511271222032656961)
              ·
                refine ⟨3577417133453416524492721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4769889511271222032656961 3577417133453416524492721)
                ·
                  refine ⟨2683062850090062393369541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3577417133453416524492721 2683062850090062393369541)
                  ·
                    refine ⟨503074284391886698756789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2683062850090062393369541 503074284391886698756789)
                    ·
                      rfl

theorem cell23_2939201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_2939201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939201 prefixEnd_2939201 := by exact prefixLift 2939201
  have htrace : WordTrace (prefixWord ++ tailWord_2939201) baseStart_2939201 baseEnd_2939201 := by
    simpa [prefixWord, tailWord_2939201, baseEnd_2939201] using wordTrace_append hprefix tailTrace_2939201
  have hstable : (prefixWord ++ tailWord_2939201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939201).length < 2 ^ (prefixWord ++ tailWord_2939201).sum := by decide
  have hdescent : baseEnd_2939201 < baseStart_2939201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939208 : List Nat := [2, 1, 3, 1, 1, 2, 6, 2, 1, 2, 2]
def baseStart_2939208 : Nat := 118140960795 + 2939208 * 2 ^ 59
def prefixEnd_2939208 : Nat := 4983230072969 + 3 ^ 40 * 2939208 * 2
def baseEnd_2939208 : Nat := 1509226447540241568882835

theorem tailTrace_2939208 : CollatzResearch.WordTrace tailWord_2939208 prefixEnd_2939208 1509226447540241568882835 := by
  unfold tailWord_2939208
  simp only [CollatzResearch.WordTrace]
  refine ⟨53600861367879433803549139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71467815157172578404732185 53600861367879433803549139)
  ·
    refine ⟨80401292051819150705323709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53600861367879433803549139 80401292051819150705323709)
    ·
      refine ⟨30150484519432181514496391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80401292051819150705323709 30150484519432181514496391)
      ·
        refine ⟨45225726779148272271744587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30150484519432181514496391 45225726779148272271744587)
        ·
          refine ⟨67838590168722408407616881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45225726779148272271744587 67838590168722408407616881)
          ·
            refine ⟨50878942626541806305712661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67838590168722408407616881 50878942626541806305712661)
            ·
              refine ⟨2384950435619147170580281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50878942626541806305712661 2384950435619147170580281)
              ·
                refine ⟨1788712826714360377935211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2384950435619147170580281 1788712826714360377935211)
                ·
                  refine ⟨2683069240071540566902817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1788712826714360377935211 2683069240071540566902817)
                  ·
                    refine ⟨2012301930053655425177113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2683069240071540566902817 2012301930053655425177113)
                    ·
                      refine ⟨1509226447540241568882835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2012301930053655425177113 1509226447540241568882835)
                      ·
                        rfl

theorem cell23_2939208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 6, 2, 1, 2, 2].length) (baseStart_2939208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939208 prefixEnd_2939208 := by exact prefixLift 2939208
  have htrace : WordTrace (prefixWord ++ tailWord_2939208) baseStart_2939208 baseEnd_2939208 := by
    simpa [prefixWord, tailWord_2939208, baseEnd_2939208] using wordTrace_append hprefix tailTrace_2939208
  have hstable : (prefixWord ++ tailWord_2939208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939208).length < 2 ^ (prefixWord ++ tailWord_2939208).sum := by decide
  have hdescent : baseEnd_2939208 < baseStart_2939208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939247 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 3, 4, 2]
def baseStart_2939247 : Nat := 118140960795 + 2939247 * 2 ^ 59
def prefixEnd_2939247 : Nat := 4983230072969 + 3 ^ 40 * 2939247 * 2
def baseEnd_2939247 : Nat := 1509246473285766916295155

theorem tailTrace_2939247 : CollatzResearch.WordTrace tailWord_2939247 prefixEnd_2939247 1509246473285766916295155 := by
  unfold tailWord_2939247
  simp only [CollatzResearch.WordTrace]
  refine ⟨107203145182617577267767995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71468763455078384845178663 107203145182617577267767995)
  ·
    refine ⟨160804717773926365901651993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107203145182617577267767995 160804717773926365901651993)
    ·
      refine ⟨120603538330444774426238995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160804717773926365901651993 120603538330444774426238995)
      ·
        refine ⟨180905307495667161639358493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120603538330444774426238995 180905307495667161639358493)
        ·
          refine ⟨67839490310875185614759435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180905307495667161639358493 67839490310875185614759435)
          ·
            refine ⟨101759235466312778422139153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67839490310875185614759435 101759235466312778422139153)
            ·
              refine ⟨76319426599734583816604365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101759235466312778422139153 76319426599734583816604365)
              ·
                refine ⟨28619784974900468931226637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76319426599734583816604365 28619784974900468931226637)
                ·
                  refine ⟨10732419365587675849209989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28619784974900468931226637 10732419365587675849209989)
                  ·
                    refine ⟨2012328631047689221726873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10732419365587675849209989 2012328631047689221726873)
                    ·
                      refine ⟨1509246473285766916295155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2012328631047689221726873 1509246473285766916295155)
                      ·
                        rfl

theorem cell23_2939247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 4, 2].length) (baseStart_2939247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939247 prefixEnd_2939247 := by exact prefixLift 2939247
  have htrace : WordTrace (prefixWord ++ tailWord_2939247) baseStart_2939247 baseEnd_2939247 := by
    simpa [prefixWord, tailWord_2939247, baseEnd_2939247] using wordTrace_append hprefix tailTrace_2939247
  have hstable : (prefixWord ++ tailWord_2939247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939247).length < 2 ^ (prefixWord ++ tailWord_2939247).sum := by decide
  have hdescent : baseEnd_2939247 < baseStart_2939247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939321 : List Nat := [1, 2, 1, 4, 3, 2, 3, 2, 5]
def baseStart_2939321 : Nat := 118140960795 + 2939321 * 2 ^ 59
def prefixEnd_2939321 : Nat := 4983230072969 + 3 ^ 40 * 2939321 * 2
def baseEnd_2939321 : Nat := 167698274539355514085535

theorem tailTrace_2939321 : CollatzResearch.WordTrace tailWord_2939321 prefixEnd_2939321 167698274539355514085535 := by
  unfold tailWord_2939321
  simp only [CollatzResearch.WordTrace]
  refine ⟨107205844184349487905961817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71470562789566325270641211 107205844184349487905961817)
  ·
    refine ⟨80404383138262115929471363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107205844184349487905961817 80404383138262115929471363)
    ·
      refine ⟨120606574707393173894207045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80404383138262115929471363 120606574707393173894207045)
      ·
        refine ⟨22613732757636220105163821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120606574707393173894207045 22613732757636220105163821)
        ·
          refine ⟨8480149784113582539436433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22613732757636220105163821 8480149784113582539436433)
          ·
            refine ⟨6360112338085186904577325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8480149784113582539436433 6360112338085186904577325)
            ·
              refine ⟨2385042126781945089216497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6360112338085186904577325 2385042126781945089216497)
              ·
                refine ⟨1788781595086458816912373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2385042126781945089216497 1788781595086458816912373)
                ·
                  refine ⟨167698274539355514085535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1788781595086458816912373 167698274539355514085535)
                  ·
                    rfl

theorem cell23_2939321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 2, 5].length) (baseStart_2939321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939321 prefixEnd_2939321 := by exact prefixLift 2939321
  have htrace : WordTrace (prefixWord ++ tailWord_2939321) baseStart_2939321 baseEnd_2939321 := by
    simpa [prefixWord, tailWord_2939321, baseEnd_2939321] using wordTrace_append hprefix tailTrace_2939321
  have hstable : (prefixWord ++ tailWord_2939321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939321).length < 2 ^ (prefixWord ++ tailWord_2939321).sum := by decide
  have hdescent : baseEnd_2939321 < baseStart_2939321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939332 : List Nat := [2, 3, 3, 2, 2, 2, 2, 1, 2, 2, 2]
def baseStart_2939332 : Nat := 118140960795 + 2939332 * 2 ^ 59
def prefixEnd_2939332 : Nat := 4983230072969 + 3 ^ 40 * 2939332 * 2
def baseEnd_2939332 : Nat := 1509290119141399083732265

theorem tailTrace_2939332 : CollatzResearch.WordTrace tailWord_2939332 prefixEnd_2939332 1509290119141399083732265 := by
  unfold tailWord_2939332
  simp only [CollatzResearch.WordTrace]
  refine ⟨53603122693654818392306125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71470830258206424523074833 53603122693654818392306125)
  ·
    refine ⟨20101171010120556897114797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53603122693654818392306125 20101171010120556897114797)
    ·
      refine ⟨7537939128795208836418049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20101171010120556897114797 7537939128795208836418049)
      ·
        refine ⟨5653454346596406627313537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7537939128795208836418049 5653454346596406627313537)
        ·
          refine ⟨4240090759947304970485153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5653454346596406627313537 4240090759947304970485153)
          ·
            refine ⟨3180068069960478727863865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4240090759947304970485153 3180068069960478727863865)
            ·
              refine ⟨2385051052470359045897899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3180068069960478727863865 2385051052470359045897899)
              ·
                refine ⟨3577576578705538568846849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2385051052470359045897899 3577576578705538568846849)
                ·
                  refine ⟨2683182434029153926635137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3577576578705538568846849 2683182434029153926635137)
                  ·
                    refine ⟨2012386825521865444976353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2683182434029153926635137 2012386825521865444976353)
                    ·
                      refine ⟨1509290119141399083732265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2012386825521865444976353 1509290119141399083732265)
                      ·
                        rfl

theorem cell23_2939332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_2939332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939332 prefixEnd_2939332 := by exact prefixLift 2939332
  have htrace : WordTrace (prefixWord ++ tailWord_2939332) baseStart_2939332 baseEnd_2939332 := by
    simpa [prefixWord, tailWord_2939332, baseEnd_2939332] using wordTrace_append hprefix tailTrace_2939332
  have hstable : (prefixWord ++ tailWord_2939332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939332).length < 2 ^ (prefixWord ++ tailWord_2939332).sum := by decide
  have hdescent : baseEnd_2939332 < baseStart_2939332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939354 : List Nat := [3, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4]
def baseStart_2939354 : Nat := 118140960795 + 2939354 * 2 ^ 59
def prefixEnd_2939354 : Nat := 4983230072969 + 3 ^ 40 * 2939354 * 2
def baseEnd_2939354 : Nat := 1509301415715797997657163

theorem tailTrace_2939354 : CollatzResearch.WordTrace tailWord_2939354 prefixEnd_2939354 1509301415715797997657163 := by
  unfold tailWord_2939354
  simp only [CollatzResearch.WordTrace]
  refine ⟨26801761948307483635478279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71471365195486623027942077 26801761948307483635478279)
  ·
    refine ⟨40202642922461225453217419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26801761948307483635478279 40202642922461225453217419)
    ·
      refine ⟨60303964383691838179826129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40202642922461225453217419 60303964383691838179826129)
      ·
        refine ⟨45227973287768878634869597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60303964383691838179826129 45227973287768878634869597)
        ·
          refine ⟨16960489982913329488076099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45227973287768878634869597 16960489982913329488076099)
          ·
            refine ⟨25440734974369994232114149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16960489982913329488076099 25440734974369994232114149)
            ·
              refine ⟨4770137807694373918521403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25440734974369994232114149 4770137807694373918521403)
              ·
                refine ⟨7155206711541560877782105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4770137807694373918521403 7155206711541560877782105)
                ·
                  refine ⟨5366405033656170658336579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7155206711541560877782105 5366405033656170658336579)
                  ·
                    refine ⟨8049607550484255987504869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5366405033656170658336579 8049607550484255987504869)
                    ·
                      refine ⟨1509301415715797997657163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8049607550484255987504869 1509301415715797997657163)
                      ·
                        rfl

theorem cell23_2939354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_2939354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939354 prefixEnd_2939354 := by exact prefixLift 2939354
  have htrace : WordTrace (prefixWord ++ tailWord_2939354) baseStart_2939354 baseEnd_2939354 := by
    simpa [prefixWord, tailWord_2939354, baseEnd_2939354] using wordTrace_append hprefix tailTrace_2939354
  have hstable : (prefixWord ++ tailWord_2939354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939354).length < 2 ^ (prefixWord ++ tailWord_2939354).sum := by decide
  have hdescent : baseEnd_2939354 < baseStart_2939354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939367 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_2939367 : Nat := 118140960795 + 2939367 * 2 ^ 59
def prefixEnd_2939367 : Nat := 4983230072969 + 3 ^ 40 * 2939367 * 2
def baseEnd_2939367 : Nat := 1509308090964306446794603

theorem tailTrace_2939367 : CollatzResearch.WordTrace tailWord_2939367 prefixEnd_2939367 1509308090964306446794603 := by
  unfold tailWord_2939367
  simp only [CollatzResearch.WordTrace]
  refine ⟨107207521942182837762136355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71471681294788558508090903 107207521942182837762136355)
  ·
    refine ⟨160811282913274256643204533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107207521942182837762136355 160811282913274256643204533)
    ·
      refine ⟨15076057773119461560300425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160811282913274256643204533 15076057773119461560300425)
      ·
        refine ⟨11307043329839596170225319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15076057773119461560300425 11307043329839596170225319)
        ·
          refine ⟨16960564994759394255337979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11307043329839596170225319 16960564994759394255337979)
          ·
            refine ⟨25440847492139091383006969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16960564994759394255337979 25440847492139091383006969)
            ·
              refine ⟨19080635619104318537255227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25440847492139091383006969 19080635619104318537255227)
              ·
                refine ⟨28620953428656477805882841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19080635619104318537255227 28620953428656477805882841)
                ·
                  refine ⟨21465715071492358354412131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28620953428656477805882841 21465715071492358354412131)
                  ·
                    refine ⟨32198572607238537531618197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21465715071492358354412131 32198572607238537531618197)
                    ·
                      refine ⟨1509308090964306446794603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32198572607238537531618197 1509308090964306446794603)
                      ·
                        rfl

theorem cell23_2939367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_2939367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939367 prefixEnd_2939367 := by exact prefixLift 2939367
  have htrace : WordTrace (prefixWord ++ tailWord_2939367) baseStart_2939367 baseEnd_2939367 := by
    simpa [prefixWord, tailWord_2939367, baseEnd_2939367] using wordTrace_append hprefix tailTrace_2939367
  have hstable : (prefixWord ++ tailWord_2939367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939367).length < 2 ^ (prefixWord ++ tailWord_2939367).sum := by decide
  have hdescent : baseEnd_2939367 < baseStart_2939367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939405 : List Nat := [1, 7, 1, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_2939405 : Nat := 118140960795 + 2939405 * 2 ^ 59
def prefixEnd_2939405 : Nat := 4983230072969 + 3 ^ 40 * 2939405 * 2
def baseEnd_2939405 : Nat := 1509327603229177298119429

theorem tailTrace_2939405 : CollatzResearch.WordTrace tailWord_2939405 prefixEnd_2939405 1509327603229177298119429 := by
  unfold tailWord_2939405
  simp only [CollatzResearch.WordTrace]
  refine ⟨107208907916045170252019669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71472605277363446834679779 107208907916045170252019669)
  ·
    refine ⟨2512708779282308677781711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 107208907916045170252019669 2512708779282308677781711)
    ·
      refine ⟨3769063168923463016672567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2512708779282308677781711 3769063168923463016672567)
      ·
        refine ⟨5653594753385194525008851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3769063168923463016672567 5653594753385194525008851)
        ·
          refine ⟨8480392130077791787513277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5653594753385194525008851 8480392130077791787513277)
          ·
            refine ⟨3180147048779171920317479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8480392130077791787513277 3180147048779171920317479)
            ·
              refine ⟨4770220573168757880476219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3180147048779171920317479 4770220573168757880476219)
              ·
                refine ⟨7155330859753136820714329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4770220573168757880476219 7155330859753136820714329)
                ·
                  refine ⟨5366498144814852615535747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7155330859753136820714329 5366498144814852615535747)
                  ·
                    refine ⟨8049747217222278923303621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5366498144814852615535747 8049747217222278923303621)
                    ·
                      refine ⟨1509327603229177298119429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8049747217222278923303621 1509327603229177298119429)
                      ·
                        rfl

theorem cell23_2939405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_2939405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939405 prefixEnd_2939405 := by exact prefixLift 2939405
  have htrace : WordTrace (prefixWord ++ tailWord_2939405) baseStart_2939405 baseEnd_2939405 := by
    simpa [prefixWord, tailWord_2939405, baseEnd_2939405] using wordTrace_append hprefix tailTrace_2939405
  have hstable : (prefixWord ++ tailWord_2939405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939405).length < 2 ^ (prefixWord ++ tailWord_2939405).sum := by decide
  have hdescent : baseEnd_2939405 < baseStart_2939405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939415 : List Nat := [1, 1, 3, 6, 1, 1, 2, 3, 1, 4]
def baseStart_2939415 : Nat := 118140960795 + 2939415 * 2 ^ 59
def prefixEnd_2939415 : Nat := 4983230072969 + 3 ^ 40 * 2939415 * 2
def baseEnd_2939415 : Nat := 503110912678574086331461

theorem tailTrace_2939415 : CollatzResearch.WordTrace tailWord_2939415 prefixEnd_2939415 503110912678574086331461 := by
  unfold tailWord_2939415
  simp only [CollatzResearch.WordTrace]
  refine ⟨107209272646008941959883699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71472848430672627973255799 107209272646008941959883699)
  ·
    refine ⟨160813908969013412939825549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107209272646008941959883699 160813908969013412939825549)
    ·
      refine ⟨60305215863380029852434581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160813908969013412939825549 60305215863380029852434581)
      ·
        refine ⟨2826806993595938899332871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60305215863380029852434581 2826806993595938899332871)
        ·
          refine ⟨4240210490393908348999307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2826806993595938899332871 4240210490393908348999307)
          ·
            refine ⟨6360315735590862523498961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4240210490393908348999307 6360315735590862523498961)
            ·
              refine ⟨4770236801693146892624221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6360315735590862523498961 4770236801693146892624221)
              ·
                refine ⟨1788838800634930084734083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4770236801693146892624221 1788838800634930084734083)
                ·
                  refine ⟨2683258200952395127101125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1788838800634930084734083 2683258200952395127101125)
                  ·
                    refine ⟨503110912678574086331461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2683258200952395127101125 503110912678574086331461)
                    ·
                      rfl

theorem cell23_2939415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 1, 4].length) (baseStart_2939415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939415 prefixEnd_2939415 := by exact prefixLift 2939415
  have htrace : WordTrace (prefixWord ++ tailWord_2939415) baseStart_2939415 baseEnd_2939415 := by
    simpa [prefixWord, tailWord_2939415, baseEnd_2939415] using wordTrace_append hprefix tailTrace_2939415
  have hstable : (prefixWord ++ tailWord_2939415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939415).length < 2 ^ (prefixWord ++ tailWord_2939415).sum := by decide
  have hdescent : baseEnd_2939415 < baseStart_2939415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939428 : List Nat := [2, 3, 1, 5, 1, 2, 1, 2, 6]
def baseStart_2939428 : Nat := 118140960795 + 2939428 * 2 ^ 59
def prefixEnd_2939428 : Nat := 4983230072969 + 3 ^ 40 * 2939428 * 2
def baseEnd_2939428 : Nat := 167704379253803412014647

theorem tailTrace_2939428 : CollatzResearch.WordTrace tailWord_2939428 prefixEnd_2939428 167704379253803412014647 := by
  unfold tailWord_2939428
  simp only [CollatzResearch.WordTrace]
  refine ⟨53604873397480922590053469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71473164529974563453404625 53604873397480922590053469)
  ·
    refine ⟨20101827524055345971270051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53604873397480922590053469 20101827524055345971270051)
    ·
      refine ⟨30152741286083018956905077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20101827524055345971270051 30152741286083018956905077)
      ·
        refine ⟨2826819495570283027209851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30152741286083018956905077 2826819495570283027209851)
        ·
          refine ⟨4240229243355424540814777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2826819495570283027209851 4240229243355424540814777)
          ·
            refine ⟨3180171932516568405611083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4240229243355424540814777 3180171932516568405611083)
            ·
              refine ⟨4770257898774852608416625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3180171932516568405611083 4770257898774852608416625)
              ·
                refine ⟨3577693424081139456312469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4770257898774852608416625 3577693424081139456312469)
                ·
                  refine ⟨167704379253803412014647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3577693424081139456312469 167704379253803412014647)
                  ·
                    rfl

theorem cell23_2939428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_2939428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939428 prefixEnd_2939428 := by exact prefixLift 2939428
  have htrace : WordTrace (prefixWord ++ tailWord_2939428) baseStart_2939428 baseEnd_2939428 := by
    simpa [prefixWord, tailWord_2939428, baseEnd_2939428] using wordTrace_append hprefix tailTrace_2939428
  have hstable : (prefixWord ++ tailWord_2939428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939428).length < 2 ^ (prefixWord ++ tailWord_2939428).sum := by decide
  have hdescent : baseEnd_2939428 < baseStart_2939428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939461 : List Nat := [1, 3, 1, 1, 1, 6, 2, 2, 1, 1, 4]
def baseStart_2939461 : Nat := 118140960795 + 2939461 * 2 ^ 59
def prefixEnd_2939461 : Nat := 4983230072969 + 3 ^ 40 * 2939461 * 2
def baseEnd_2939461 : Nat := 1509356358145829079019171

theorem tailTrace_2939461 : CollatzResearch.WordTrace tailWord_2939461 prefixEnd_2939461 1509356358145829079019171 := by
  unfold tailWord_2939461
  simp only [CollatzResearch.WordTrace]
  refine ⟨107210950403842291816058237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71473966935894861210705491 107210950403842291816058237)
  ·
    refine ⟨40204106401440859431021839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 107210950403842291816058237 40204106401440859431021839)
    ·
      refine ⟨60306159602161289146532759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40204106401440859431021839 60306159602161289146532759)
      ·
        refine ⟨90459239403241933719799139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60306159602161289146532759 90459239403241933719799139)
        ·
          refine ⟨135688859104862900579698709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90459239403241933719799139 135688859104862900579698709)
          ·
            refine ⟨6360415270540448464673377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 135688859104862900579698709 6360415270540448464673377)
            ·
              refine ⟨4770311452905336348505033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6360415270540448464673377 4770311452905336348505033)
              ·
                refine ⟨3577733589679002261378775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4770311452905336348505033 3577733589679002261378775)
                ·
                  refine ⟨5366600384518503392068163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3577733589679002261378775 5366600384518503392068163)
                  ·
                    refine ⟨8049900576777755088102245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5366600384518503392068163 8049900576777755088102245)
                    ·
                      refine ⟨1509356358145829079019171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8049900576777755088102245 1509356358145829079019171)
                      ·
                        rfl

theorem cell23_2939461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 1, 4].length) (baseStart_2939461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939461 prefixEnd_2939461 := by exact prefixLift 2939461
  have htrace : WordTrace (prefixWord ++ tailWord_2939461) baseStart_2939461 baseEnd_2939461 := by
    simpa [prefixWord, tailWord_2939461, baseEnd_2939461] using wordTrace_append hprefix tailTrace_2939461
  have hstable : (prefixWord ++ tailWord_2939461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939461).length < 2 ^ (prefixWord ++ tailWord_2939461).sum := by decide
  have hdescent : baseEnd_2939461 < baseStart_2939461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939464 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 3, 2, 3]
def baseStart_2939464 : Nat := 118140960795 + 2939464 * 2 ^ 59
def prefixEnd_2939464 : Nat := 4983230072969 + 3 ^ 40 * 2939464 * 2
def baseEnd_2939464 : Nat := 1509357898587792567281657

theorem tailTrace_2939464 : CollatzResearch.WordTrace tailWord_2939464 prefixEnd_2939464 1509357898587792567281657 := by
  unfold tailWord_2939464
  simp only [CollatzResearch.WordTrace]
  refine ⟨53605529911415711664208723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71474039881887615552278297 53605529911415711664208723)
  ·
    refine ⟨80408294867123567496313085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53605529911415711664208723 80408294867123567496313085)
    ·
      refine ⟨30153110575171337811117407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80408294867123567496313085 30153110575171337811117407)
      ·
        refine ⟨45229665862757006716676111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30153110575171337811117407 45229665862757006716676111)
        ·
          refine ⟨67844498794135510075014167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45229665862757006716676111 67844498794135510075014167)
          ·
            refine ⟨101766748191203265112521251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67844498794135510075014167 101766748191203265112521251)
            ·
              refine ⟨152650122286804897668781877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101766748191203265112521251 152650122286804897668781877)
              ·
                refine ⟨14310948964387959156448301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152650122286804897668781877 14310948964387959156448301)
                ·
                  refine ⟨5366605861645484683668113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14310948964387959156448301 5366605861645484683668113)
                  ·
                    refine ⟨4024954396234113512751085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5366605861645484683668113 4024954396234113512751085)
                    ·
                      refine ⟨1509357898587792567281657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4024954396234113512751085 1509357898587792567281657)
                      ·
                        rfl

theorem cell23_2939464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_2939464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939464 prefixEnd_2939464 := by exact prefixLift 2939464
  have htrace : WordTrace (prefixWord ++ tailWord_2939464) baseStart_2939464 baseEnd_2939464 := by
    simpa [prefixWord, tailWord_2939464, baseEnd_2939464] using wordTrace_append hprefix tailTrace_2939464
  have hstable : (prefixWord ++ tailWord_2939464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939464).length < 2 ^ (prefixWord ++ tailWord_2939464).sum := by decide
  have hdescent : baseEnd_2939464 < baseStart_2939464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939474 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_2939474 : Nat := 118140960795 + 2939474 * 2 ^ 59
def prefixEnd_2939474 : Nat := 4983230072969 + 3 ^ 40 * 2939474 * 2
def baseEnd_2939474 : Nat := 1509363033394337528156611

theorem tailTrace_2939474 : CollatzResearch.WordTrace tailWord_2939474 prefixEnd_2939474 1509363033394337528156611 := by
  unfold tailWord_2939474
  simp only [CollatzResearch.WordTrace]
  refine ⟨26802856138198798759070369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 71474283035196796690854317 26802856138198798759070369)
  ·
    refine ⟨20102142103649099069302777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26802856138198798759070369 20102142103649099069302777)
    ·
      refine ⟨15076606577736824301977083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20102142103649099069302777 15076606577736824301977083)
      ·
        refine ⟨22614909866605236452965625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15076606577736824301977083 22614909866605236452965625)
        ·
          refine ⟨16961182399953927339724219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22614909866605236452965625 16961182399953927339724219)
          ·
            refine ⟨25441773599930891009586329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16961182399953927339724219 25441773599930891009586329)
            ·
              refine ⟨19081330199948168257189747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25441773599930891009586329 19081330199948168257189747)
              ·
                refine ⟨28621995299922252385784621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19081330199948168257189747 28621995299922252385784621)
                ·
                  refine ⟨10733248237470844644669233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28621995299922252385784621 10733248237470844644669233)
                  ·
                    refine ⟨8049936178103133483501925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10733248237470844644669233 8049936178103133483501925)
                    ·
                      refine ⟨1509363033394337528156611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8049936178103133483501925 1509363033394337528156611)
                      ·
                        rfl

theorem cell23_2939474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_2939474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939474 prefixEnd_2939474 := by exact prefixLift 2939474
  have htrace : WordTrace (prefixWord ++ tailWord_2939474) baseStart_2939474 baseEnd_2939474 := by
    simpa [prefixWord, tailWord_2939474, baseEnd_2939474] using wordTrace_append hprefix tailTrace_2939474
  have hstable : (prefixWord ++ tailWord_2939474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939474).length < 2 ^ (prefixWord ++ tailWord_2939474).sum := by decide
  have hdescent : baseEnd_2939474 < baseStart_2939474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939497 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 2, 7]
def baseStart_2939497 : Nat := 118140960795 + 2939497 * 2 ^ 59
def prefixEnd_2939497 : Nat := 4983230072969 + 3 ^ 40 * 2939497 * 2
def baseEnd_2939497 : Nat := 503124947816463646056335

theorem tailTrace_2939497 : CollatzResearch.WordTrace tailWord_2939497 prefixEnd_2939497 503124947816463646056335 := by
  unfold tailWord_2939497
  simp only [CollatzResearch.WordTrace]
  refine ⟨107212263431711869964368745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71474842287807913309579163 107212263431711869964368745)
  ·
    refine ⟨80409197573783902473276559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107212263431711869964368745 80409197573783902473276559)
    ·
      refine ⟨120613796360675853709914839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80409197573783902473276559 120613796360675853709914839)
      ·
        refine ⟨180920694541013780564872259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120613796360675853709914839 180920694541013780564872259)
        ·
          refine ⟨271381041811520670847308389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180920694541013780564872259 271381041811520670847308389)
          ·
            refine ⟨50883945339660125783870323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 271381041811520670847308389 50883945339660125783870323)
            ·
              refine ⟨76325918009490188675805485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50883945339660125783870323 76325918009490188675805485)
              ·
                refine ⟨28622219253558820753427057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76325918009490188675805485 28622219253558820753427057)
                ·
                  refine ⟨21466664440169115565070293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28622219253558820753427057 21466664440169115565070293)
                  ·
                    refine ⟨503124947816463646056335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21466664440169115565070293 503124947816463646056335)
                    ·
                      rfl

theorem cell23_2939497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 7].length) (baseStart_2939497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939497 prefixEnd_2939497 := by exact prefixLift 2939497
  have htrace : WordTrace (prefixWord ++ tailWord_2939497) baseStart_2939497 baseEnd_2939497 := by
    simpa [prefixWord, tailWord_2939497, baseEnd_2939497] using wordTrace_append hprefix tailTrace_2939497
  have hstable : (prefixWord ++ tailWord_2939497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939497).length < 2 ^ (prefixWord ++ tailWord_2939497).sum := by decide
  have hdescent : baseEnd_2939497 < baseStart_2939497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939507 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 5]
def baseStart_2939507 : Nat := 118140960795 + 2939507 * 2 ^ 59
def prefixEnd_2939507 : Nat := 4983230072969 + 3 ^ 40 * 2939507 * 2
def baseEnd_2939507 : Nat := 1509379978255935899043959

theorem tailTrace_2939507 : CollatzResearch.WordTrace tailWord_2939507 prefixEnd_2939507 1509379978255935899043959 := by
  unfold tailWord_2939507
  simp only [CollatzResearch.WordTrace]
  refine ⟨107212628161675641672232775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 71475085441117094448155183 107212628161675641672232775)
  ·
    refine ⟨160818942242513462508349163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 107212628161675641672232775 160818942242513462508349163)
    ·
      refine ⟨241228413363770193762523745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160818942242513462508349163 241228413363770193762523745)
      ·
        refine ⟨180921310022827645321892809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 241228413363770193762523745 180921310022827645321892809)
        ·
          refine ⟨135690982517120733991419607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180921310022827645321892809 135690982517120733991419607)
          ·
            refine ⟨203536473775681100987129411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135690982517120733991419607 203536473775681100987129411)
            ·
              refine ⟨305304710663521651480694117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203536473775681100987129411 305304710663521651480694117)
              ·
                refine ⟨57244633249410309652630147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 305304710663521651480694117 57244633249410309652630147)
                ·
                  refine ⟨85866949874115464478945221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57244633249410309652630147 85866949874115464478945221)
                  ·
                    refine ⟨16100053101396649589802229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85866949874115464478945221 16100053101396649589802229)
                    ·
                      refine ⟨1509379978255935899043959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16100053101396649589802229 1509379978255935899043959)
                      ·
                        rfl

theorem cell23_2939507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_2939507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939507 prefixEnd_2939507 := by exact prefixLift 2939507
  have htrace : WordTrace (prefixWord ++ tailWord_2939507) baseStart_2939507 baseEnd_2939507 := by
    simpa [prefixWord, tailWord_2939507, baseEnd_2939507] using wordTrace_append hprefix tailTrace_2939507
  have hstable : (prefixWord ++ tailWord_2939507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939507).length < 2 ^ (prefixWord ++ tailWord_2939507).sum := by decide
  have hdescent : baseEnd_2939507 < baseStart_2939507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2939544 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 2, 6]
def baseStart_2939544 : Nat := 118140960795 + 2939544 * 2 ^ 59
def prefixEnd_2939544 : Nat := 4983230072969 + 3 ^ 40 * 2939544 * 2
def baseEnd_2939544 : Nat := 503132992346717418093763

theorem tailTrace_2939544 : CollatzResearch.WordTrace tailWord_2939544 prefixEnd_2939544 503132992346717418093763 := by
  unfold tailWord_2939544
  simp only [CollatzResearch.WordTrace]
  refine ⟨53606988831270798495664843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 71475985108361064660886457 53606988831270798495664843)
  ·
    refine ⟨80410483246906197743497265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53606988831270798495664843 80410483246906197743497265)
    ·
      refine ⟨60307862435179648307622949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80410483246906197743497265 60307862435179648307622949)
      ·
        refine ⟨11307724206596184057679303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60307862435179648307622949 11307724206596184057679303)
        ·
          refine ⟨16961586309894276086518955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11307724206596184057679303 16961586309894276086518955)
          ·
            refine ⟨25442379464841414129778433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16961586309894276086518955 25442379464841414129778433)
            ·
              refine ⟨19081784598631060597333825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25442379464841414129778433 19081784598631060597333825)
              ·
                refine ⟨14311338448973295448000369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19081784598631060597333825 14311338448973295448000369)
                ·
                  refine ⟨10733503836729971586000277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14311338448973295448000369 10733503836729971586000277)
                  ·
                    refine ⟨503132992346717418093763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10733503836729971586000277 503132992346717418093763)
                    ·
                      rfl

theorem cell23_2939544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_2939544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2939544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2939544 prefixEnd_2939544 := by exact prefixLift 2939544
  have htrace : WordTrace (prefixWord ++ tailWord_2939544) baseStart_2939544 baseEnd_2939544 := by
    simpa [prefixWord, tailWord_2939544, baseEnd_2939544] using wordTrace_append hprefix tailTrace_2939544
  have hstable : (prefixWord ++ tailWord_2939544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2939544).length < 2 ^ (prefixWord ++ tailWord_2939544).sum := by decide
  have hdescent : baseEnd_2939544 < baseStart_2939544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2939544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
