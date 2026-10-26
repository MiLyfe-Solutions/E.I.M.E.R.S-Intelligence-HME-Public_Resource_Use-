import V185TrunkScan20Chunk107

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_655601 : List Nat := [1, 2, 2, 2, 2, 1, 4, 2, 4]
def baseStart_655601 : Nat := 118140960795 + 655601 * 2 ^ 59
def prefixEnd_655601 : Nat := 4983230072969 + 3 ^ 40 * 655601 * 2
def baseEnd_655601 : Nat := 299234160505239726019957

theorem tailTrace_655601 : CollatzResearch.WordTrace tailWord_655601 prefixEnd_655601 299234160505239726019957 := by
  unfold tailWord_655601
  simp only [CollatzResearch.WordTrace]
  refine ⟨23911732897877019581702657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15941155265251346387801771 23911732897877019581702657)
  ·
    refine ⟨17933799673407764686276993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23911732897877019581702657 17933799673407764686276993)
    ·
      refine ⟨13450349755055823514707745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17933799673407764686276993 13450349755055823514707745)
      ·
        refine ⟨10087762316291867636030809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13450349755055823514707745 10087762316291867636030809)
        ·
          refine ⟨7565821737218900727023107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10087762316291867636030809 7565821737218900727023107)
          ·
            refine ⟨11348732605828351090534661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7565821737218900727023107 11348732605828351090534661)
            ·
              refine ⟨2127887363592815829475249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11348732605828351090534661 2127887363592815829475249)
              ·
                refine ⟨1595915522694611872106437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2127887363592815829475249 1595915522694611872106437)
                ·
                  refine ⟨299234160505239726019957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1595915522694611872106437 299234160505239726019957)
                  ·
                    rfl

theorem cell20_655601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_655601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655601 prefixEnd_655601 := by exact prefixLift 655601
  have htrace : WordTrace (prefixWord ++ tailWord_655601) baseStart_655601 baseEnd_655601 := by
    simpa [prefixWord, tailWord_655601, baseEnd_655601] using wordTrace_append hprefix tailTrace_655601
  have hstable : (prefixWord ++ tailWord_655601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655601).length < 2 ^ (prefixWord ++ tailWord_655601).sum := by decide
  have hdescent : baseEnd_655601 < baseStart_655601 := by decide
  rcases family_descends (prefixWord ++ tailWord_655601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655615 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 7]
def baseStart_655615 : Nat := 118140960795 + 655615 * 2 ^ 59
def prefixEnd_655615 : Nat := 4983230072969 + 3 ^ 40 * 655615 * 2
def baseEnd_655615 : Nat := 299240550486717899553233

theorem tailTrace_655615 : CollatzResearch.WordTrace tailWord_655615 prefixEnd_655615 299240550486717899553233 := by
  unfold tailWord_655615
  simp only [CollatzResearch.WordTrace]
  refine ⟨23912243519826299972712299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15941495679884199981808199 23912243519826299972712299)
  ·
    refine ⟨35868365279739449959068449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23912243519826299972712299 35868365279739449959068449)
    ·
      refine ⟨26901273959804587469301337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35868365279739449959068449 26901273959804587469301337)
      ·
        refine ⟨20175955469853440601976003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26901273959804587469301337 20175955469853440601976003)
        ·
          refine ⟨30263933204780160902964005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20175955469853440601976003 30263933204780160902964005)
          ·
            refine ⟨5674487475896280169305751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30263933204780160902964005 5674487475896280169305751)
            ·
              refine ⟨8511731213844420253958627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5674487475896280169305751 8511731213844420253958627)
              ·
                refine ⟨12767596820766630380937941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8511731213844420253958627 12767596820766630380937941)
                ·
                  refine ⟨299240550486717899553233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12767596820766630380937941 299240550486717899553233)
                  ·
                    rfl

theorem cell20_655615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_655615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655615 prefixEnd_655615 := by exact prefixLift 655615
  have htrace : WordTrace (prefixWord ++ tailWord_655615) baseStart_655615 baseEnd_655615 := by
    simpa [prefixWord, tailWord_655615, baseEnd_655615] using wordTrace_append hprefix tailTrace_655615
  have hstable : (prefixWord ++ tailWord_655615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655615).length < 2 ^ (prefixWord ++ tailWord_655615).sum := by decide
  have hdescent : baseEnd_655615 < baseStart_655615 := by decide
  rcases family_descends (prefixWord ++ tailWord_655615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655645 : List Nat := [1, 4, 2, 3, 2, 2, 2, 1, 3]
def baseStart_655645 : Nat := 118140960795 + 655645 * 2 ^ 59
def prefixEnd_655645 : Nat := 4983230072969 + 3 ^ 40 * 655645 * 2
def baseEnd_655645 : Nat := 299254243304171128553111

theorem tailTrace_655645 : CollatzResearch.WordTrace tailWord_655645 prefixEnd_655645 299254243304171128553111 := by
  unfold tailWord_655645
  simp only [CollatzResearch.WordTrace]
  refine ⟨23913337709717615096304389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15942225139811743397536259 23913337709717615096304389)
  ·
    refine ⟨4483750820572052830557073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23913337709717615096304389 4483750820572052830557073)
    ·
      refine ⟨3362813115429039622917805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4483750820572052830557073 3362813115429039622917805)
      ·
        refine ⟨1261054918285889858594177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3362813115429039622917805 1261054918285889858594177)
        ·
          refine ⟨945791188714417393945633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1261054918285889858594177 945791188714417393945633)
          ·
            refine ⟨709343391535813045459225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 945791188714417393945633 709343391535813045459225)
            ·
              refine ⟨532007543651859784094419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 709343391535813045459225 532007543651859784094419)
              ·
                refine ⟨798011315477789676141629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532007543651859784094419 798011315477789676141629)
                ·
                  refine ⟨299254243304171128553111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 798011315477789676141629 299254243304171128553111)
                  ·
                    rfl

theorem cell20_655645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_655645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655645 prefixEnd_655645 := by exact prefixLift 655645
  have htrace : WordTrace (prefixWord ++ tailWord_655645) baseStart_655645 baseEnd_655645 := by
    simpa [prefixWord, tailWord_655645, baseEnd_655645] using wordTrace_append hprefix tailTrace_655645
  have hstable : (prefixWord ++ tailWord_655645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655645).length < 2 ^ (prefixWord ++ tailWord_655645).sum := by decide
  have hdescent : baseEnd_655645 < baseStart_655645 := by decide
  rcases family_descends (prefixWord ++ tailWord_655645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655649 : List Nat := [1, 2, 3, 2, 1, 1, 6, 1, 3]
def baseStart_655649 : Nat := 118140960795 + 655649 * 2 ^ 59
def prefixEnd_655649 : Nat := 4983230072969 + 3 ^ 40 * 655649 * 2
def baseEnd_655649 : Nat := 299256069013164892419761

theorem tailTrace_655649 : CollatzResearch.WordTrace tailWord_655649 prefixEnd_655649 299256069013164892419761 := by
  unfold tailWord_655649
  simp only [CollatzResearch.WordTrace]
  refine ⟨23913483601703123779450001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15942322401135415852966667 23913483601703123779450001)
  ·
    refine ⟨17935112701277342834587501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23913483601703123779450001 17935112701277342834587501)
    ·
      refine ⟨6725667262979003562970313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17935112701277342834587501 6725667262979003562970313)
      ·
        refine ⟨5044250447234252672227735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6725667262979003562970313 5044250447234252672227735)
        ·
          refine ⟨7566375670851379008341603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5044250447234252672227735 7566375670851379008341603)
          ·
            refine ⟨11349563506277068512512405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7566375670851379008341603 11349563506277068512512405)
            ·
              refine ⟨532010789356737586524019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11349563506277068512512405 532010789356737586524019)
              ·
                refine ⟨798016184035106379786029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532010789356737586524019 798016184035106379786029)
                ·
                  refine ⟨299256069013164892419761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 798016184035106379786029 299256069013164892419761)
                  ·
                    rfl

theorem cell20_655649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 3].length) (baseStart_655649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655649 prefixEnd_655649 := by exact prefixLift 655649
  have htrace : WordTrace (prefixWord ++ tailWord_655649) baseStart_655649 baseEnd_655649 := by
    simpa [prefixWord, tailWord_655649, baseEnd_655649] using wordTrace_append hprefix tailTrace_655649
  have hstable : (prefixWord ++ tailWord_655649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655649).length < 2 ^ (prefixWord ++ tailWord_655649).sum := by decide
  have hdescent : baseEnd_655649 < baseStart_655649 := by decide
  rcases family_descends (prefixWord ++ tailWord_655649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655715 : List Nat := [1, 1, 1, 5, 2, 1, 3, 2, 4]
def baseStart_655715 : Nat := 118140960795 + 655715 * 2 ^ 59
def prefixEnd_655715 : Nat := 4983230072969 + 3 ^ 40 * 655715 * 2
def baseEnd_655715 : Nat := 299286193211561996219491

theorem tailTrace_655715 : CollatzResearch.WordTrace tailWord_655715 prefixEnd_655715 299286193211561996219491 := by
  unfold tailWord_655715
  simp only [CollatzResearch.WordTrace]
  refine ⟨23915890819464017051352599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15943927212976011367568399 23915890819464017051352599)
  ·
    refine ⟨35873836229196025577028899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23915890819464017051352599 35873836229196025577028899)
    ·
      refine ⟨53810754343794038365543349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35873836229196025577028899 53810754343794038365543349)
      ·
        refine ⟨5044758219730691096769689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53810754343794038365543349 5044758219730691096769689)
        ·
          refine ⟨3783568664798018322577267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5044758219730691096769689 3783568664798018322577267)
          ·
            refine ⟨5675352997197027483865901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3783568664798018322577267 5675352997197027483865901)
            ·
              refine ⟨2128257373948885306449713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5675352997197027483865901 2128257373948885306449713)
              ·
                refine ⟨1596193030461663979837285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2128257373948885306449713 1596193030461663979837285)
                ·
                  refine ⟨299286193211561996219491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1596193030461663979837285 299286193211561996219491)
                  ·
                    rfl

theorem cell20_655715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 4].length) (baseStart_655715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655715 prefixEnd_655715 := by exact prefixLift 655715
  have htrace : WordTrace (prefixWord ++ tailWord_655715) baseStart_655715 baseEnd_655715 := by
    simpa [prefixWord, tailWord_655715, baseEnd_655715] using wordTrace_append hprefix tailTrace_655715
  have hstable : (prefixWord ++ tailWord_655715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655715).length < 2 ^ (prefixWord ++ tailWord_655715).sum := by decide
  have hdescent : baseEnd_655715 < baseStart_655715 := by decide
  rcases family_descends (prefixWord ++ tailWord_655715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655729 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 5]
def baseStart_655729 : Nat := 118140960795 + 655729 * 2 ^ 59
def prefixEnd_655729 : Nat := 4983230072969 + 3 ^ 40 * 655729 * 2
def baseEnd_655729 : Nat := 299292583193040169752767

theorem tailTrace_655729 : CollatzResearch.WordTrace tailWord_655729 prefixEnd_655729 299292583193040169752767 := by
  unfold tailWord_655729
  simp only [CollatzResearch.WordTrace]
  refine ⟨23916401441413297442362241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15944267627608864961574827 23916401441413297442362241)
  ·
    refine ⟨17937301081059973081771681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23916401441413297442362241 17937301081059973081771681)
    ·
      refine ⟨13452975810794979811328761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17937301081059973081771681 13452975810794979811328761)
      ·
        refine ⟨10089731858096234858496571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13452975810794979811328761 10089731858096234858496571)
        ·
          refine ⟨15134597787144352287744857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10089731858096234858496571 15134597787144352287744857)
          ·
            refine ⟨11350948340358264215808643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15134597787144352287744857 11350948340358264215808643)
            ·
              refine ⟨17026422510537396323712965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11350948340358264215808643 17026422510537396323712965)
              ·
                refine ⟨3192454220725761810696181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17026422510537396323712965 3192454220725761810696181)
                ·
                  refine ⟨299292583193040169752767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3192454220725761810696181 299292583193040169752767)
                  ·
                    rfl

theorem cell20_655729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_655729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655729 prefixEnd_655729 := by exact prefixLift 655729
  have htrace : WordTrace (prefixWord ++ tailWord_655729) baseStart_655729 baseEnd_655729 := by
    simpa [prefixWord, tailWord_655729, baseEnd_655729] using wordTrace_append hprefix tailTrace_655729
  have hstable : (prefixWord ++ tailWord_655729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655729).length < 2 ^ (prefixWord ++ tailWord_655729).sum := by decide
  have hdescent : baseEnd_655729 < baseStart_655729 := by decide
  rcases family_descends (prefixWord ++ tailWord_655729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655753 : List Nat := [1, 2, 1, 1, 6, 1, 1, 3, 4]
def baseStart_655753 : Nat := 118140960795 + 655753 * 2 ^ 59
def prefixEnd_655753 : Nat := 4983230072969 + 3 ^ 40 * 655753 * 2
def baseEnd_655753 : Nat := 299303537447002752952669

theorem tailTrace_655753 : CollatzResearch.WordTrace tailWord_655753 prefixEnd_655753 299303537447002752952669 := by
  unfold tailWord_655753
  simp only [CollatzResearch.WordTrace]
  refine ⟨23917276793326349541235913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15944851195550899694157275 23917276793326349541235913)
  ·
    refine ⟨17937957594994762155926935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23917276793326349541235913 17937957594994762155926935)
    ·
      refine ⟨26906936392492143233890403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17937957594994762155926935 26906936392492143233890403)
      ·
        refine ⟨40360404588738214850835605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26906936392492143233890403 40360404588738214850835605)
        ·
          refine ⟨1891893965097103821132919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40360404588738214850835605 1891893965097103821132919)
          ·
            refine ⟨2837840947645655731699379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1891893965097103821132919 2837840947645655731699379)
            ·
              refine ⟨4256761421468483597549069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2837840947645655731699379 4256761421468483597549069)
              ·
                refine ⟨1596285533050681349080901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4256761421468483597549069 1596285533050681349080901)
                ·
                  refine ⟨299303537447002752952669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1596285533050681349080901 299303537447002752952669)
                  ·
                    rfl

theorem cell20_655753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_655753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655753 prefixEnd_655753 := by exact prefixLift 655753
  have htrace : WordTrace (prefixWord ++ tailWord_655753) baseStart_655753 baseEnd_655753 := by
    simpa [prefixWord, tailWord_655753, baseEnd_655753] using wordTrace_append hprefix tailTrace_655753
  have hstable : (prefixWord ++ tailWord_655753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655753).length < 2 ^ (prefixWord ++ tailWord_655753).sum := by decide
  have hdescent : baseEnd_655753 < baseStart_655753 := by decide
  rcases family_descends (prefixWord ++ tailWord_655753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655773 : List Nat := [1, 4, 2, 1, 5, 1, 2, 4]
def baseStart_655773 : Nat := 118140960795 + 655773 * 2 ^ 59
def prefixEnd_655773 : Nat := 4983230072969 + 3 ^ 40 * 655773 * 2
def baseEnd_655773 : Nat := 99770888663990524095307

theorem tailTrace_655773 : CollatzResearch.WordTrace tailWord_655773 prefixEnd_655773 99770888663990524095307 := by
  unfold tailWord_655773
  simp only [CollatzResearch.WordTrace]
  refine ⟨23918006253253892956963973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15945337502169261971309315 23918006253253892956963973)
  ·
    refine ⟨4484626172485104929430745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23918006253253892956963973 4484626172485104929430745)
    ·
      refine ⟨3363469629363828697073059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4484626172485104929430745 3363469629363828697073059)
      ·
        refine ⟨5045204444045743045609589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3363469629363828697073059 5045204444045743045609589)
        ·
          refine ⟨472987916629288410525899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5045204444045743045609589 472987916629288410525899)
          ·
            refine ⟨709481874943932615788849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472987916629288410525899 709481874943932615788849)
            ·
              refine ⟨532111406207949461841637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 709481874943932615788849 532111406207949461841637)
              ·
                refine ⟨99770888663990524095307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 532111406207949461841637 99770888663990524095307)
                ·
                  rfl

theorem cell20_655773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 4].length) (baseStart_655773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655773 prefixEnd_655773 := by exact prefixLift 655773
  have htrace : WordTrace (prefixWord ++ tailWord_655773) baseStart_655773 baseEnd_655773 := by
    simpa [prefixWord, tailWord_655773, baseEnd_655773] using wordTrace_append hprefix tailTrace_655773
  have hstable : (prefixWord ++ tailWord_655773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655773).length < 2 ^ (prefixWord ++ tailWord_655773).sum := by decide
  have hdescent : baseEnd_655773 < baseStart_655773 := by decide
  rcases family_descends (prefixWord ++ tailWord_655773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655804 : List Nat := [2, 2, 2, 4, 1, 2, 3, 2, 2]
def baseStart_655804 : Nat := 118140960795 + 655804 * 2 ^ 59
def prefixEnd_655804 : Nat := 4983230072969 + 3 ^ 40 * 655804 * 2
def baseEnd_655804 : Nat := 299326815236673242252461

theorem tailTrace_655804 : CollatzResearch.WordTrace tailWord_655804 prefixEnd_655804 299326815236673242252461 := by
  unfold tailWord_655804
  simp only [CollatzResearch.WordTrace]
  refine ⟨11959568458070792625671233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15946091277427723500894977 11959568458070792625671233)
  ·
    refine ⟨8969676343553094469253425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11959568458070792625671233 8969676343553094469253425)
    ·
      refine ⟨6727257257664820851940069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8969676343553094469253425 6727257257664820851940069)
      ·
        refine ⟨1261360735812153909738763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6727257257664820851940069 1261360735812153909738763)
        ·
          refine ⟨1892041103718230864608145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1261360735812153909738763 1892041103718230864608145)
          ·
            refine ⟨1419030827788673148456109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1892041103718230864608145 1419030827788673148456109)
            ·
              refine ⟨532136560420752430671041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1419030827788673148456109 532136560420752430671041)
              ·
                refine ⟨399102420315564323003281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 532136560420752430671041 399102420315564323003281)
                ·
                  refine ⟨299326815236673242252461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399102420315564323003281 299326815236673242252461)
                  ·
                    rfl

theorem cell20_655804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_655804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655804 prefixEnd_655804 := by exact prefixLift 655804
  have htrace : WordTrace (prefixWord ++ tailWord_655804) baseStart_655804 baseEnd_655804 := by
    simpa [prefixWord, tailWord_655804, baseEnd_655804] using wordTrace_append hprefix tailTrace_655804
  have hstable : (prefixWord ++ tailWord_655804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655804).length < 2 ^ (prefixWord ++ tailWord_655804).sum := by decide
  have hdescent : baseEnd_655804 < baseStart_655804 := by decide
  rcases family_descends (prefixWord ++ tailWord_655804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655901 : List Nat := [1, 4, 2, 2, 1, 3, 2, 3, 2]
def baseStart_655901 : Nat := 118140960795 + 655901 * 2 ^ 59
def prefixEnd_655901 : Nat := 4983230072969 + 3 ^ 40 * 655901 * 2
def baseEnd_655901 : Nat := 299371088679772016018731

theorem tailTrace_655901 : CollatzResearch.WordTrace tailWord_655901 prefixEnd_655901 299371088679772016018731 := by
  unfold tailWord_655901
  simp only [CollatzResearch.WordTrace]
  refine ⟨23922674796790170817623557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15948449864526780545082371 23922674796790170817623557)
  ·
    refine ⟨4485501524398157028304417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23922674796790170817623557 4485501524398157028304417)
    ·
      refine ⟨3364126143298617771228313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4485501524398157028304417 3364126143298617771228313)
      ·
        refine ⟨2523094607473963328421235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3364126143298617771228313 2523094607473963328421235)
        ·
          refine ⟨3784641911210944992631853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2523094607473963328421235 3784641911210944992631853)
          ·
            refine ⟨1419240716704104372236945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3784641911210944992631853 1419240716704104372236945)
            ·
              refine ⟨1064430537528078279177709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1419240716704104372236945 1064430537528078279177709)
              ·
                refine ⟨399161451573029354691641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1064430537528078279177709 399161451573029354691641)
                ·
                  refine ⟨299371088679772016018731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399161451573029354691641 299371088679772016018731)
                  ·
                    rfl

theorem cell20_655901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_655901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655901 prefixEnd_655901 := by exact prefixLift 655901
  have htrace : WordTrace (prefixWord ++ tailWord_655901) baseStart_655901 baseEnd_655901 := by
    simpa [prefixWord, tailWord_655901, baseEnd_655901] using wordTrace_append hprefix tailTrace_655901
  have hstable : (prefixWord ++ tailWord_655901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655901).length < 2 ^ (prefixWord ++ tailWord_655901).sum := by decide
  have hdescent : baseEnd_655901 < baseStart_655901 := by decide
  rcases family_descends (prefixWord ++ tailWord_655901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655911 : List Nat := [1, 1, 7, 2, 1, 2, 1, 2, 3]
def baseStart_655911 : Nat := 118140960795 + 655911 * 2 ^ 59
def prefixEnd_655911 : Nat := 4983230072969 + 3 ^ 40 * 655911 * 2
def baseEnd_655911 : Nat := 299375652952256425685357

theorem tailTrace_655911 : CollatzResearch.WordTrace tailWord_655911 prefixEnd_655911 299375652952256425685357 := by
  unfold tailWord_655911
  simp only [CollatzResearch.WordTrace]
  refine ⟨23923039526753942525487587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15948693017835961683658391 23923039526753942525487587)
  ·
    refine ⟨35884559290130913788231381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23923039526753942525487587 35884559290130913788231381)
    ·
      refine ⟨841044358362443291911673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 35884559290130913788231381 841044358362443291911673)
      ·
        refine ⟨630783268771832468933755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 841044358362443291911673 630783268771832468933755)
        ·
          refine ⟨946174903157748703400633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630783268771832468933755 946174903157748703400633)
          ·
            refine ⟨709631177368311527550475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 946174903157748703400633 709631177368311527550475)
            ·
              refine ⟨1064446766052467291325713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 709631177368311527550475 1064446766052467291325713)
              ·
                refine ⟨798335074539350468494285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1064446766052467291325713 798335074539350468494285)
                ·
                  refine ⟨299375652952256425685357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 798335074539350468494285 299375652952256425685357)
                  ·
                    rfl

theorem cell20_655911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 3].length) (baseStart_655911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655911 prefixEnd_655911 := by exact prefixLift 655911
  have htrace : WordTrace (prefixWord ++ tailWord_655911) baseStart_655911 baseEnd_655911 := by
    simpa [prefixWord, tailWord_655911, baseEnd_655911] using wordTrace_append hprefix tailTrace_655911
  have hstable : (prefixWord ++ tailWord_655911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655911).length < 2 ^ (prefixWord ++ tailWord_655911).sum := by decide
  have hdescent : baseEnd_655911 < baseStart_655911 := by decide
  rcases family_descends (prefixWord ++ tailWord_655911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655922 : List Nat := [3, 2, 1, 1, 2, 1, 4, 4, 2]
def baseStart_655922 : Nat := 118140960795 + 655922 * 2 ^ 59
def prefixEnd_655922 : Nat := 4983230072969 + 3 ^ 40 * 655922 * 2
def baseEnd_655922 : Nat := 299380673651989276318645

theorem tailTrace_655922 : CollatzResearch.WordTrace tailWord_655922 prefixEnd_655922 299380673651989276318645 := by
  unfold tailWord_655922
  simp only [CollatzResearch.WordTrace]
  refine ⟨5980860182428522851034505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15948960486476060936092013 5980860182428522851034505)
  ·
    refine ⟨4485645136821392138275879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5980860182428522851034505 4485645136821392138275879)
    ·
      refine ⟨6728467705232088207413819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4485645136821392138275879 6728467705232088207413819)
      ·
        refine ⟨10092701557848132311120729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6728467705232088207413819 10092701557848132311120729)
        ·
          refine ⟨7569526168386099233340547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10092701557848132311120729 7569526168386099233340547)
          ·
            refine ⟨11354289252579148850010821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7569526168386099233340547 11354289252579148850010821)
            ·
              refine ⟨2128929234858590409377029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11354289252579148850010821 2128929234858590409377029)
              ·
                refine ⟨399174231535985701758193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2128929234858590409377029 399174231535985701758193)
                ·
                  refine ⟨299380673651989276318645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399174231535985701758193 299380673651989276318645)
                  ·
                    rfl

theorem cell20_655922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_655922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655922 prefixEnd_655922 := by exact prefixLift 655922
  have htrace : WordTrace (prefixWord ++ tailWord_655922) baseStart_655922 baseEnd_655922 := by
    simpa [prefixWord, tailWord_655922, baseEnd_655922] using wordTrace_append hprefix tailTrace_655922
  have hstable : (prefixWord ++ tailWord_655922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655922).length < 2 ^ (prefixWord ++ tailWord_655922).sum := by decide
  have hdescent : baseEnd_655922 < baseStart_655922 := by decide
  rcases family_descends (prefixWord ++ tailWord_655922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655943 : List Nat := [1, 1, 4, 1, 4, 1, 2, 2, 4]
def baseStart_655943 : Nat := 118140960795 + 655943 * 2 ^ 59
def prefixEnd_655943 : Nat := 4983230072969 + 3 ^ 40 * 655943 * 2
def baseEnd_655943 : Nat := 299390258624206536618559

theorem tailTrace_655943 : CollatzResearch.WordTrace tailWord_655943 prefixEnd_655943 299390258624206536618559 := by
  unfold tailWord_655943
  simp only [CollatzResearch.WordTrace]
  refine ⟨23924206662638011990652483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15949471108425341327101655 23924206662638011990652483)
  ·
    refine ⟨35886309993957017985978725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23924206662638011990652483 35886309993957017985978725)
    ·
      refine ⟨6728683123866940872371011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35886309993957017985978725 6728683123866940872371011)
      ·
        refine ⟨10093024685800411308556517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6728683123866940872371011 10093024685800411308556517)
        ·
          refine ⟨1892442128587577120354347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10093024685800411308556517 1892442128587577120354347)
          ·
            refine ⟨2838663192881365680531521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1892442128587577120354347 2838663192881365680531521)
            ·
              refine ⟨2128997394661024260398641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2838663192881365680531521 2128997394661024260398641)
              ·
                refine ⟨1596748045995768195298981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2128997394661024260398641 1596748045995768195298981)
                ·
                  refine ⟨299390258624206536618559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1596748045995768195298981 299390258624206536618559)
                  ·
                    rfl

theorem cell20_655943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 4].length) (baseStart_655943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655943 prefixEnd_655943 := by exact prefixLift 655943
  have htrace : WordTrace (prefixWord ++ tailWord_655943) baseStart_655943 baseEnd_655943 := by
    simpa [prefixWord, tailWord_655943, baseEnd_655943] using wordTrace_append hprefix tailTrace_655943
  have hstable : (prefixWord ++ tailWord_655943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655943).length < 2 ^ (prefixWord ++ tailWord_655943).sum := by decide
  have hdescent : baseEnd_655943 < baseStart_655943 := by decide
  rcases family_descends (prefixWord ++ tailWord_655943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655957 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 5]
def baseStart_655957 : Nat := 118140960795 + 655957 * 2 ^ 59
def prefixEnd_655957 : Nat := 4983230072969 + 3 ^ 40 * 655957 * 2
def baseEnd_655957 : Nat := 299396648605684710151835

theorem tailTrace_655957 : CollatzResearch.WordTrace tailWord_655957 prefixEnd_655957 299396648605684710151835 := by
  unfold tailWord_655957
  simp only [CollatzResearch.WordTrace]
  refine ⟨23924717284587292381662125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15949811523058194921108083 23924717284587292381662125)
  ·
    refine ⟨8971768981720234643123297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23924717284587292381662125 8971768981720234643123297)
    ·
      refine ⟨6728826736290175982342473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8971768981720234643123297 6728826736290175982342473)
      ·
        refine ⟨5046620052217631986756855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6728826736290175982342473 5046620052217631986756855)
        ·
          refine ⟨7569930078326447980135283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5046620052217631986756855 7569930078326447980135283)
          ·
            refine ⟨11354895117489671970202925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7569930078326447980135283 11354895117489671970202925)
            ·
              refine ⟨4258085669058626988826097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11354895117489671970202925 4258085669058626988826097)
              ·
                refine ⟨3193564251793970241619573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4258085669058626988826097 3193564251793970241619573)
                ·
                  refine ⟨299396648605684710151835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3193564251793970241619573 299396648605684710151835)
                  ·
                    rfl

theorem cell20_655957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_655957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655957 prefixEnd_655957 := by exact prefixLift 655957
  have htrace : WordTrace (prefixWord ++ tailWord_655957) baseStart_655957 baseEnd_655957 := by
    simpa [prefixWord, tailWord_655957, baseEnd_655957] using wordTrace_append hprefix tailTrace_655957
  have hstable : (prefixWord ++ tailWord_655957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655957).length < 2 ^ (prefixWord ++ tailWord_655957).sum := by decide
  have hdescent : baseEnd_655957 < baseStart_655957 := by decide
  rcases family_descends (prefixWord ++ tailWord_655957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_655960 : List Nat := [2, 1, 2, 2, 1, 2, 5, 3, 2]
def baseStart_655960 : Nat := 118140960795 + 655960 * 2 ^ 59
def prefixEnd_655960 : Nat := 4983230072969 + 3 ^ 40 * 655960 * 2
def baseEnd_655960 : Nat := 299398017887430033051823

theorem tailTrace_655960 : CollatzResearch.WordTrace tailWord_655960 prefixEnd_655960 299398017887430033051823 := by
  unfold tailWord_655960
  simp only [CollatzResearch.WordTrace]
  refine ⟨11962413351788211947010667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15949884469050949262680889 11962413351788211947010667)
  ·
    refine ⟨17943620027682317920516001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11962413351788211947010667 17943620027682317920516001)
    ·
      refine ⟨13457715020761738440387001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17943620027682317920516001 13457715020761738440387001)
      ·
        refine ⟨10093286265571303830290251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13457715020761738440387001 10093286265571303830290251)
        ·
          refine ⟨15139929398356955745435377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10093286265571303830290251 15139929398356955745435377)
          ·
            refine ⟨11354947048767716809076533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15139929398356955745435377 11354947048767716809076533)
            ·
              refine ⟨1064526285821973450850925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11354947048767716809076533 1064526285821973450850925)
              ·
                refine ⟨399197357183240044069097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1064526285821973450850925 399197357183240044069097)
                ·
                  refine ⟨299398017887430033051823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399197357183240044069097 299398017887430033051823)
                  ·
                    rfl

theorem cell20_655960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 2].length) (baseStart_655960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_655960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_655960 prefixEnd_655960 := by exact prefixLift 655960
  have htrace : WordTrace (prefixWord ++ tailWord_655960) baseStart_655960 baseEnd_655960 := by
    simpa [prefixWord, tailWord_655960, baseEnd_655960] using wordTrace_append hprefix tailTrace_655960
  have hstable : (prefixWord ++ tailWord_655960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_655960).length < 2 ^ (prefixWord ++ tailWord_655960).sum := by decide
  have hdescent : baseEnd_655960 < baseStart_655960 := by decide
  rcases family_descends (prefixWord ++ tailWord_655960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656026 : List Nat := [3, 1, 1, 6, 9]
def baseStart_656026 : Nat := 118140960795 + 656026 * 2 ^ 59
def prefixEnd_656026 : Nat := 4983230072969 + 3 ^ 40 * 656026 * 2
def baseEnd_656026 : Nat := 3696643729454656010513

theorem tailTrace_656026 : CollatzResearch.WordTrace tailWord_656026 prefixEnd_656026 3696643729454656010513 := by
  unfold tailWord_656026
  simp only [CollatzResearch.WordTrace]
  refine ⟨5981808480334329291480983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15951489280891544777282621 5981808480334329291480983)
  ·
    refine ⟨8972712720501493937221475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5981808480334329291480983 8972712720501493937221475)
    ·
      refine ⟨13459069080752240905832213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8972712720501493937221475 13459069080752240905832213)
      ·
        refine ⟨630893863160261292460885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13459069080752240905832213 630893863160261292460885)
        ·
          refine ⟨3696643729454656010513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 630893863160261292460885 3696643729454656010513)
          ·
            rfl

theorem cell20_656026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 9].length) (baseStart_656026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656026 prefixEnd_656026 := by exact prefixLift 656026
  have htrace : WordTrace (prefixWord ++ tailWord_656026) baseStart_656026 baseEnd_656026 := by
    simpa [prefixWord, tailWord_656026, baseEnd_656026] using wordTrace_append hprefix tailTrace_656026
  have hstable : (prefixWord ++ tailWord_656026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656026).length < 2 ^ (prefixWord ++ tailWord_656026).sum := by decide
  have hdescent : baseEnd_656026 < baseStart_656026 := by decide
  rcases family_descends (prefixWord ++ tailWord_656026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656032 : List Nat := [2, 1, 1, 4, 4, 2, 2, 2, 2]
def baseStart_656032 : Nat := 118140960795 + 656032 * 2 ^ 59
def prefixEnd_656032 : Nat := 4983230072969 + 3 ^ 40 * 656032 * 2
def baseEnd_656032 : Nat := 299430880649317782651529

theorem tailTrace_656032 : CollatzResearch.WordTrace tailWord_656032 prefixEnd_656032 299430880649317782651529 := by
  unfold tailWord_656032
  simp only [CollatzResearch.WordTrace]
  refine ⟨11963726379657790095321175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15951635172877053460428233 11963726379657790095321175)
  ·
    refine ⟨17945589569486685142981763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11963726379657790095321175 17945589569486685142981763)
    ·
      refine ⟨26918384354230027714472645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17945589569486685142981763 26918384354230027714472645)
      ·
        refine ⟨5047197066418130196463621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26918384354230027714472645 5047197066418130196463621)
        ·
          refine ⟨946349449953399411836929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5047197066418130196463621 946349449953399411836929)
          ·
            refine ⟨709762087465049558877697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 946349449953399411836929 709762087465049558877697)
            ·
              refine ⟨532321565598787169158273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 709762087465049558877697 532321565598787169158273)
              ·
                refine ⟨399241174199090376868705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 532321565598787169158273 399241174199090376868705)
                ·
                  refine ⟨299430880649317782651529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399241174199090376868705 299430880649317782651529)
                  ·
                    rfl

theorem cell20_656032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 2].length) (baseStart_656032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656032 prefixEnd_656032 := by exact prefixLift 656032
  have htrace : WordTrace (prefixWord ++ tailWord_656032) baseStart_656032 baseEnd_656032 := by
    simpa [prefixWord, tailWord_656032, baseEnd_656032] using wordTrace_append hprefix tailTrace_656032
  have hstable : (prefixWord ++ tailWord_656032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656032).length < 2 ^ (prefixWord ++ tailWord_656032).sum := by decide
  have hdescent : baseEnd_656032 < baseStart_656032 := by decide
  rcases family_descends (prefixWord ++ tailWord_656032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656036 : List Nat := [2, 3, 1, 2, 2, 1, 3, 4, 2]
def baseStart_656036 : Nat := 118140960795 + 656036 * 2 ^ 59
def prefixEnd_656036 : Nat := 4983230072969 + 3 ^ 40 * 656036 * 2
def baseEnd_656036 : Nat := 299432706358311546518179

theorem tailTrace_656036 : CollatzResearch.WordTrace tailWord_656036 prefixEnd_656036 299432706358311546518179 := by
  unfold tailWord_656036
  simp only [CollatzResearch.WordTrace]
  refine ⟨11963799325650544436893981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15951732434200725915858641 11963799325650544436893981)
  ·
    refine ⟨4486424747118954163835243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11963799325650544436893981 4486424747118954163835243)
    ·
      refine ⟨6729637120678431245752865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4486424747118954163835243 6729637120678431245752865)
      ·
        refine ⟨5047227840508823434314649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6729637120678431245752865 5047227840508823434314649)
        ·
          refine ⟨3785420880381617575735987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5047227840508823434314649 3785420880381617575735987)
          ·
            refine ⟨5678131320572426363603981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3785420880381617575735987 5678131320572426363603981)
            ·
              refine ⟨2129299245214659886351493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5678131320572426363603981 2129299245214659886351493)
              ·
                refine ⟨399243608477748728690905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2129299245214659886351493 399243608477748728690905)
                ·
                  refine ⟨299432706358311546518179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399243608477748728690905 299432706358311546518179)
                  ·
                    rfl

theorem cell20_656036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_656036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656036 prefixEnd_656036 := by exact prefixLift 656036
  have htrace : WordTrace (prefixWord ++ tailWord_656036) baseStart_656036 baseEnd_656036 := by
    simpa [prefixWord, tailWord_656036, baseEnd_656036] using wordTrace_append hprefix tailTrace_656036
  have hstable : (prefixWord ++ tailWord_656036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656036).length < 2 ^ (prefixWord ++ tailWord_656036).sum := by decide
  have hdescent : baseEnd_656036 < baseStart_656036 := by decide
  rcases family_descends (prefixWord ++ tailWord_656036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656039 : List Nat := [1, 1, 6, 3, 2, 1, 1, 5]
def baseStart_656039 : Nat := 118140960795 + 656039 * 2 ^ 59
def prefixEnd_656039 : Nat := 4983230072969 + 3 ^ 40 * 656039 * 2
def baseEnd_656039 : Nat := 99811358546685623139389

theorem tailTrace_656039 : CollatzResearch.WordTrace tailWord_656039 prefixEnd_656039 99811358546685623139389 := by
  unfold tailWord_656039
  simp only [CollatzResearch.WordTrace]
  refine ⟨23927708070290220386147171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15951805380193480257431447 23927708070290220386147171)
  ·
    refine ⟨35891562105435330579220757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23927708070290220386147171 35891562105435330579220757)
    ·
      refine ⟨1682416973692281120900973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35891562105435330579220757 1682416973692281120900973)
      ·
        refine ⟨630906365134605420337865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1682416973692281120900973 630906365134605420337865)
        ·
          refine ⟨473179773850954065253399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 630906365134605420337865 473179773850954065253399)
          ·
            refine ⟨709769660776431097880099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473179773850954065253399 709769660776431097880099)
            ·
              refine ⟨1064654491164646646820149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 709769660776431097880099 1064654491164646646820149)
              ·
                refine ⟨99811358546685623139389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1064654491164646646820149 99811358546685623139389)
                ·
                  rfl

theorem cell20_656039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 5].length) (baseStart_656039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656039 prefixEnd_656039 := by exact prefixLift 656039
  have htrace : WordTrace (prefixWord ++ tailWord_656039) baseStart_656039 baseEnd_656039 := by
    simpa [prefixWord, tailWord_656039, baseEnd_656039] using wordTrace_append hprefix tailTrace_656039
  have hstable : (prefixWord ++ tailWord_656039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656039).length < 2 ^ (prefixWord ++ tailWord_656039).sum := by decide
  have hdescent : baseEnd_656039 < baseStart_656039 := by decide
  rcases family_descends (prefixWord ++ tailWord_656039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656074 : List Nat := [3, 1, 2, 1, 4, 1, 1, 5, 2]
def baseStart_656074 : Nat := 118140960795 + 656074 * 2 ^ 59
def prefixEnd_656074 : Nat := 4983230072969 + 3 ^ 40 * 656074 * 2
def baseEnd_656074 : Nat := 299450050593752303251357

theorem tailTrace_656074 : CollatzResearch.WordTrace tailWord_656074 prefixEnd_656074 299450050593752303251357 := by
  unfold tailWord_656074
  simp only [CollatzResearch.WordTrace]
  refine ⟨5982246156290855340917819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15952656416775614242447517 5982246156290855340917819)
  ·
    refine ⟨8973369234436283011376729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5982246156290855340917819 8973369234436283011376729)
    ·
      refine ⟨6730026925827212258532547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8973369234436283011376729 6730026925827212258532547)
      ·
        refine ⟨10095040388740818387798821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6730026925827212258532547 10095040388740818387798821)
        ·
          refine ⟨1892820072888903447712279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10095040388740818387798821 1892820072888903447712279)
          ·
            refine ⟨2839230109333355171568419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1892820072888903447712279 2839230109333355171568419)
            ·
              refine ⟨4258845164000032757352629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2839230109333355171568419 4258845164000032757352629)
              ·
                refine ⟨399266734125003071001809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4258845164000032757352629 399266734125003071001809)
                ·
                  refine ⟨299450050593752303251357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399266734125003071001809 299450050593752303251357)
                  ·
                    rfl

theorem cell20_656074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_656074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656074 prefixEnd_656074 := by exact prefixLift 656074
  have htrace : WordTrace (prefixWord ++ tailWord_656074) baseStart_656074 baseEnd_656074 := by
    simpa [prefixWord, tailWord_656074, baseEnd_656074] using wordTrace_append hprefix tailTrace_656074
  have hstable : (prefixWord ++ tailWord_656074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656074).length < 2 ^ (prefixWord ++ tailWord_656074).sum := by decide
  have hdescent : baseEnd_656074 < baseStart_656074 := by decide
  rcases family_descends (prefixWord ++ tailWord_656074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656084 : List Nat := [2, 4, 1, 3, 2, 2, 1, 2, 3]
def baseStart_656084 : Nat := 118140960795 + 656084 * 2 ^ 59
def prefixEnd_656084 : Nat := 4983230072969 + 3 ^ 40 * 656084 * 2
def baseEnd_656084 : Nat := 299454614866236712917983

theorem tailTrace_656084 : CollatzResearch.WordTrace tailWord_656084 prefixEnd_656084 299454614866236712917983 := by
  unfold tailWord_656084
  simp only [CollatzResearch.WordTrace]
  refine ⟨11964674677563596535767653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15952899570084795381023537 11964674677563596535767653)
  ·
    refine ⟨2243376502043174350456435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11964674677563596535767653 2243376502043174350456435)
    ·
      refine ⟨3365064753064761525684653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2243376502043174350456435 3365064753064761525684653)
      ·
        refine ⟨1261899282399285572131745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3365064753064761525684653 1261899282399285572131745)
        ·
          refine ⟨946424461799464179098809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1261899282399285572131745 946424461799464179098809)
          ·
            refine ⟨709818346349598134324107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 946424461799464179098809 709818346349598134324107)
            ·
              refine ⟨1064727519524397201486161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 709818346349598134324107 1064727519524397201486161)
              ·
                refine ⟨798545639643297901114621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1064727519524397201486161 798545639643297901114621)
                ·
                  refine ⟨299454614866236712917983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 798545639643297901114621 299454614866236712917983)
                  ·
                    rfl

theorem cell20_656084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_656084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656084 prefixEnd_656084 := by exact prefixLift 656084
  have htrace : WordTrace (prefixWord ++ tailWord_656084) baseStart_656084 baseEnd_656084 := by
    simpa [prefixWord, tailWord_656084, baseEnd_656084] using wordTrace_append hprefix tailTrace_656084
  have hstable : (prefixWord ++ tailWord_656084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656084).length < 2 ^ (prefixWord ++ tailWord_656084).sum := by decide
  have hdescent : baseEnd_656084 < baseStart_656084 := by decide
  rcases family_descends (prefixWord ++ tailWord_656084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656088 : List Nat := [2, 1, 2, 2, 3, 2, 3, 2, 3]
def baseStart_656088 : Nat := 118140960795 + 656088 * 2 ^ 59
def prefixEnd_656088 : Nat := 4983230072969 + 3 ^ 40 * 656088 * 2
def baseEnd_656088 : Nat := 299456440575230476784633

theorem tailTrace_656088 : CollatzResearch.WordTrace tailWord_656088 prefixEnd_656088 299456440575230476784633 := by
  unfold tailWord_656088
  simp only [CollatzResearch.WordTrace]
  refine ⟨11964747623556350877340459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15952996831408467836453945 11964747623556350877340459)
  ·
    refine ⟨17947121435334526316010689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11964747623556350877340459 17947121435334526316010689)
    ·
      refine ⟨13460341076500894737008017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17947121435334526316010689 13460341076500894737008017)
      ·
        refine ⟨10095255807375671052756013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13460341076500894737008017 10095255807375671052756013)
        ·
          refine ⟨3785720927765876644783505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10095255807375671052756013 3785720927765876644783505)
          ·
            refine ⟨2839290695824407483587629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3785720927765876644783505 2839290695824407483587629)
            ·
              refine ⟨1064734010934152806345361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2839290695824407483587629 1064734010934152806345361)
              ·
                refine ⟨798550508200614604759021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1064734010934152806345361 798550508200614604759021)
                ·
                  refine ⟨299456440575230476784633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 798550508200614604759021 299456440575230476784633)
                  ·
                    rfl

theorem cell20_656088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_656088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656088 prefixEnd_656088 := by exact prefixLift 656088
  have htrace : WordTrace (prefixWord ++ tailWord_656088) baseStart_656088 baseEnd_656088 := by
    simpa [prefixWord, tailWord_656088, baseEnd_656088] using wordTrace_append hprefix tailTrace_656088
  have hstable : (prefixWord ++ tailWord_656088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656088).length < 2 ^ (prefixWord ++ tailWord_656088).sum := by decide
  have hdescent : baseEnd_656088 < baseStart_656088 := by decide
  rcases family_descends (prefixWord ++ tailWord_656088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656095 : List Nat := [1, 1, 2, 3, 2, 4, 2, 1, 4]
def baseStart_656095 : Nat := 118140960795 + 656095 * 2 ^ 59
def prefixEnd_656095 : Nat := 4983230072969 + 3 ^ 40 * 656095 * 2
def baseEnd_656095 : Nat := 299459635565969563551271

theorem tailTrace_656095 : CollatzResearch.WordTrace tailWord_656095 prefixEnd_656095 299459635565969563551271 := by
  unfold tailWord_656095
  simp only [CollatzResearch.WordTrace]
  refine ⟨23929750558087341950185739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15953167038724894633457159 23929750558087341950185739)
  ·
    refine ⟨35894625837131012925278609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23929750558087341950185739 35894625837131012925278609)
    ·
      refine ⟨26920969377848259693958957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35894625837131012925278609 26920969377848259693958957)
      ·
        refine ⟨10095363516693097385234609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26920969377848259693958957 10095363516693097385234609)
        ·
          refine ⟨7571522637519823038925957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10095363516693097385234609 7571522637519823038925957)
          ·
            refine ⟨1419660494534966819798617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7571522637519823038925957 1419660494534966819798617)
            ·
              refine ⟨1064745370901225114848963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1419660494534966819798617 1064745370901225114848963)
              ·
                refine ⟨1597118056351837672273445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1064745370901225114848963 1597118056351837672273445)
                ·
                  refine ⟨299459635565969563551271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1597118056351837672273445 299459635565969563551271)
                  ·
                    rfl

theorem cell20_656095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 4].length) (baseStart_656095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656095 prefixEnd_656095 := by exact prefixLift 656095
  have htrace : WordTrace (prefixWord ++ tailWord_656095) baseStart_656095 baseEnd_656095 := by
    simpa [prefixWord, tailWord_656095, baseEnd_656095] using wordTrace_append hprefix tailTrace_656095
  have hstable : (prefixWord ++ tailWord_656095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656095).length < 2 ^ (prefixWord ++ tailWord_656095).sum := by decide
  have hdescent : baseEnd_656095 < baseStart_656095 := by decide
  rcases family_descends (prefixWord ++ tailWord_656095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656126 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_656126 : Nat := 118140960795 + 656126 * 2 ^ 59
def prefixEnd_656126 : Nat := 4983230072969 + 3 ^ 40 * 656126 * 2
def baseEnd_656126 : Nat := 299473784810671233517811

theorem tailTrace_656126 : CollatzResearch.WordTrace tailWord_656126 prefixEnd_656126 299473784810671233517811 := by
  unfold tailWord_656126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2991360152621879280570529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15953920813983356163042821 2991360152621879280570529)
  ·
    refine ⟨2243520114466409460427897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2991360152621879280570529 2243520114466409460427897)
    ·
      refine ⟨1682640085849807095320923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2243520114466409460427897 1682640085849807095320923)
      ·
        refine ⟨2523960128774710642981385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1682640085849807095320923 2523960128774710642981385)
        ·
          refine ⟨1892970096581032982236039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2523960128774710642981385 1892970096581032982236039)
          ·
            refine ⟨2839455144871549473354059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1892970096581032982236039 2839455144871549473354059)
            ·
              refine ⟨4259182717307324210031089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2839455144871549473354059 4259182717307324210031089)
              ·
                refine ⟨3194387037980493157523317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4259182717307324210031089 3194387037980493157523317)
                ·
                  refine ⟨299473784810671233517811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3194387037980493157523317 299473784810671233517811)
                  ·
                    rfl

theorem cell20_656126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_656126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656126 prefixEnd_656126 := by exact prefixLift 656126
  have htrace : WordTrace (prefixWord ++ tailWord_656126) baseStart_656126 baseEnd_656126 := by
    simpa [prefixWord, tailWord_656126, baseEnd_656126] using wordTrace_append hprefix tailTrace_656126
  have hstable : (prefixWord ++ tailWord_656126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656126).length < 2 ^ (prefixWord ++ tailWord_656126).sum := by decide
  have hdescent : baseEnd_656126 < baseStart_656126 := by decide
  rcases family_descends (prefixWord ++ tailWord_656126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656146 : List Nat := [3, 2, 4, 1, 3, 1, 1, 1, 4]
def baseStart_656146 : Nat := 118140960795 + 656146 * 2 ^ 59
def prefixEnd_656146 : Nat := 4983230072969 + 3 ^ 40 * 656146 * 2
def baseEnd_656146 : Nat := 299482913355640052851063

theorem tailTrace_656146 : CollatzResearch.WordTrace tailWord_656146 prefixEnd_656146 299482913355640052851063 := by
  unfold tailWord_656146
  simp only [CollatzResearch.WordTrace]
  refine ⟨5982902670225644415073073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15954407120601718440194861 5982902670225644415073073)
  ·
    refine ⟨4487177002669233311304805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5982902670225644415073073 4487177002669233311304805)
    ·
      refine ⟨841345688000481245869651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4487177002669233311304805 841345688000481245869651)
      ·
        refine ⟨1262018532000721868804477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 841345688000481245869651 1262018532000721868804477)
        ·
          refine ⟨473256949500270700801679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1262018532000721868804477 473256949500270700801679)
          ·
            refine ⟨709885424250406051202519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473256949500270700801679 709885424250406051202519)
            ·
              refine ⟨1064828136375609076803779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 709885424250406051202519 1064828136375609076803779)
              ·
                refine ⟨1597242204563413615205669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1064828136375609076803779 1597242204563413615205669)
                ·
                  refine ⟨299482913355640052851063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1597242204563413615205669 299482913355640052851063)
                  ·
                    rfl

theorem cell20_656146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_656146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656146 prefixEnd_656146 := by exact prefixLift 656146
  have htrace : WordTrace (prefixWord ++ tailWord_656146) baseStart_656146 baseEnd_656146 := by
    simpa [prefixWord, tailWord_656146, baseEnd_656146] using wordTrace_append hprefix tailTrace_656146
  have hstable : (prefixWord ++ tailWord_656146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656146).length < 2 ^ (prefixWord ++ tailWord_656146).sum := by decide
  have hdescent : baseEnd_656146 < baseStart_656146 := by decide
  rcases family_descends (prefixWord ++ tailWord_656146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656147 : List Nat := [1, 1, 1, 2, 1, 3, 4, 4, 3]
def baseStart_656147 : Nat := 118140960795 + 656147 * 2 ^ 59
def prefixEnd_656147 : Nat := 4983230072969 + 3 ^ 40 * 656147 * 2
def baseEnd_656147 : Nat := 299483369782888493817725

theorem tailTrace_656147 : CollatzResearch.WordTrace tailWord_656147 prefixEnd_656147 299483369782888493817725 := by
  unfold tailWord_656147
  simp only [CollatzResearch.WordTrace]
  refine ⟨23931647153898954831078695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15954431435932636554052463 23931647153898954831078695)
  ·
    refine ⟨35897470730848432246618043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23931647153898954831078695 35897470730848432246618043)
    ·
      refine ⟨53846206096272648369927065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35897470730848432246618043 53846206096272648369927065)
      ·
        refine ⟨40384654572204486277445299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53846206096272648369927065 40384654572204486277445299)
        ·
          refine ⟨60576981858306729416167949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40384654572204486277445299 60576981858306729416167949)
          ·
            refine ⟨22716368196865023531062981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60576981858306729416167949 22716368196865023531062981)
            ·
              refine ⟨4259319036912191912074309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22716368196865023531062981 4259319036912191912074309)
              ·
                refine ⟨798622319421035983513933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4259319036912191912074309 798622319421035983513933)
                ·
                  refine ⟨299483369782888493817725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 798622319421035983513933 299483369782888493817725)
                  ·
                    rfl

theorem cell20_656147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 3].length) (baseStart_656147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656147 prefixEnd_656147 := by exact prefixLift 656147
  have htrace : WordTrace (prefixWord ++ tailWord_656147) baseStart_656147 baseEnd_656147 := by
    simpa [prefixWord, tailWord_656147, baseEnd_656147] using wordTrace_append hprefix tailTrace_656147
  have hstable : (prefixWord ++ tailWord_656147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656147).length < 2 ^ (prefixWord ++ tailWord_656147).sum := by decide
  have hdescent : baseEnd_656147 < baseStart_656147 := by decide
  rcases family_descends (prefixWord ++ tailWord_656147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656212 : List Nat := [2, 4, 1, 1, 5, 1, 1, 5]
def baseStart_656212 : Nat := 118140960795 + 656212 * 2 ^ 59
def prefixEnd_656212 : Nat := 4983230072969 + 3 ^ 40 * 656212 * 2
def baseEnd_656212 : Nat := 99837679184679052216931

theorem tailTrace_656212 : CollatzResearch.WordTrace tailWord_656212 prefixEnd_656212 99837679184679052216931 := by
  unfold tailWord_656212
  simp only [CollatzResearch.WordTrace]
  refine ⟨11967008949331735466097445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15956011932442313954796593 11967008949331735466097445)
  ·
    refine ⟨2243814177999700399893271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11967008949331735466097445 2243814177999700399893271)
    ·
      refine ⟨3365721266999550599839907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2243814177999700399893271 3365721266999550599839907)
      ·
        refine ⟨5048581900499325899759861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3365721266999550599839907 5048581900499325899759861)
        ·
          refine ⟨473304553171811803102487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5048581900499325899759861 473304553171811803102487)
          ·
            refine ⟨709956829757717704653731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473304553171811803102487 709956829757717704653731)
            ·
              refine ⟨1064935244636576556980597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 709956829757717704653731 1064935244636576556980597)
              ·
                refine ⟨99837679184679052216931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1064935244636576556980597 99837679184679052216931)
                ·
                  rfl

theorem cell20_656212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 5].length) (baseStart_656212 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656212 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656212 prefixEnd_656212 := by exact prefixLift 656212
  have htrace : WordTrace (prefixWord ++ tailWord_656212) baseStart_656212 baseEnd_656212 := by
    simpa [prefixWord, tailWord_656212, baseEnd_656212] using wordTrace_append hprefix tailTrace_656212
  have hstable : (prefixWord ++ tailWord_656212).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656212).length < 2 ^ (prefixWord ++ tailWord_656212).sum := by decide
  have hdescent : baseEnd_656212 < baseStart_656212 := by decide
  rcases family_descends (prefixWord ++ tailWord_656212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656223 : List Nat := [1, 1, 2, 3, 1, 3, 1, 5, 3]
def baseStart_656223 : Nat := 118140960795 + 656223 * 2 ^ 59
def prefixEnd_656223 : Nat := 4983230072969 + 3 ^ 40 * 656223 * 2
def baseEnd_656223 : Nat := 299518058253770007284081

theorem tailTrace_656223 : CollatzResearch.WordTrace tailWord_656223 prefixEnd_656223 299518058253770007284081 := by
  unfold tailWord_656223
  simp only [CollatzResearch.WordTrace]
  refine ⟨23934419101623619810845323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15956279401082413207230215 23934419101623619810845323)
  ·
    refine ⟨35901628652435429716267985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23934419101623619810845323 35901628652435429716267985)
    ·
      refine ⟨26926221489326572287200989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35901628652435429716267985 26926221489326572287200989)
      ·
        refine ⟨10097333058497464607700371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26926221489326572287200989 10097333058497464607700371)
        ·
          refine ⟨15145999587746196911550557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10097333058497464607700371 15145999587746196911550557)
          ·
            refine ⟨5679749845404823841831459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15145999587746196911550557 5679749845404823841831459)
            ·
              refine ⟨8519624768107235762747189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5679749845404823841831459 8519624768107235762747189)
              ·
                refine ⟨798714822010053352757549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8519624768107235762747189 798714822010053352757549)
                ·
                  refine ⟨299518058253770007284081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 798714822010053352757549 299518058253770007284081)
                  ·
                    rfl

theorem cell20_656223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 3].length) (baseStart_656223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656223 prefixEnd_656223 := by exact prefixLift 656223
  have htrace : WordTrace (prefixWord ++ tailWord_656223) baseStart_656223 baseEnd_656223 := by
    simpa [prefixWord, tailWord_656223, baseEnd_656223] using wordTrace_append hprefix tailTrace_656223
  have hstable : (prefixWord ++ tailWord_656223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656223).length < 2 ^ (prefixWord ++ tailWord_656223).sum := by decide
  have hdescent : baseEnd_656223 < baseStart_656223 := by decide
  rcases family_descends (prefixWord ++ tailWord_656223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656226 : List Nat := [3, 3, 2, 1, 3, 1, 1, 2, 4]
def baseStart_656226 : Nat := 118140960795 + 656226 * 2 ^ 59
def prefixEnd_656226 : Nat := 4983230072969 + 3 ^ 40 * 656226 * 2
def baseEnd_656226 : Nat := 299519427535515330184069

theorem tailTrace_656226 : CollatzResearch.WordTrace tailWord_656226 prefixEnd_656226 299519427535515330184069 := by
  unfold tailWord_656226
  simp only [CollatzResearch.WordTrace]
  refine ⟨5983632130153187830801133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15956352347075167548803021 5983632130153187830801133)
  ·
    refine ⟨2243862048807445436550425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5983632130153187830801133 2243862048807445436550425)
    ·
      refine ⟨1682896536605584077412819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2243862048807445436550425 1682896536605584077412819)
      ·
        refine ⟨2524344804908376116119229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1682896536605584077412819 2524344804908376116119229)
        ·
          refine ⟨946629301840641043544711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2524344804908376116119229 946629301840641043544711)
          ·
            refine ⟨1419943952760961565317067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 946629301840641043544711 1419943952760961565317067)
            ·
              refine ⟨2129915929141442347975601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419943952760961565317067 2129915929141442347975601)
              ·
                refine ⟨1597436946856081760981701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2129915929141442347975601 1597436946856081760981701)
                ·
                  refine ⟨299519427535515330184069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1597436946856081760981701 299519427535515330184069)
                  ·
                    rfl

theorem cell20_656226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_656226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656226 prefixEnd_656226 := by exact prefixLift 656226
  have htrace : WordTrace (prefixWord ++ tailWord_656226) baseStart_656226 baseEnd_656226 := by
    simpa [prefixWord, tailWord_656226, baseEnd_656226] using wordTrace_append hprefix tailTrace_656226
  have hstable : (prefixWord ++ tailWord_656226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656226).length < 2 ^ (prefixWord ++ tailWord_656226).sum := by decide
  have hdescent : baseEnd_656226 < baseStart_656226 := by decide
  rcases family_descends (prefixWord ++ tailWord_656226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656261 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 5]
def baseStart_656261 : Nat := 118140960795 + 656261 * 2 ^ 59
def prefixEnd_656261 : Nat := 4983230072969 + 3 ^ 40 * 656261 * 2
def baseEnd_656261 : Nat := 299535402489210764017259

theorem tailTrace_656261 : CollatzResearch.WordTrace tailWord_656261 prefixEnd_656261 299535402489210764017259 := by
  unfold tailWord_656261
  simp only [CollatzResearch.WordTrace]
  refine ⟨23935805075485952300728637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15957203383657301533819091 23935805075485952300728637)
  ·
    refine ⟨8975926903307232112773239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23935805075485952300728637 8975926903307232112773239)
    ·
      refine ⟨13463890354960848169159859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8975926903307232112773239 13463890354960848169159859)
      ·
        refine ⟨20195835532441272253739789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13463890354960848169159859 20195835532441272253739789)
        ·
          refine ⟨7573438324665477095152421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20195835532441272253739789 7573438324665477095152421)
          ·
            refine ⟨1420019685874776955341079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7573438324665477095152421 1420019685874776955341079)
            ·
              refine ⟨2130029528812165433011619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1420019685874776955341079 2130029528812165433011619)
              ·
                refine ⟨3195044293218248149517429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2130029528812165433011619 3195044293218248149517429)
                ·
                  refine ⟨299535402489210764017259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3195044293218248149517429 299535402489210764017259)
                  ·
                    rfl

theorem cell20_656261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 5].length) (baseStart_656261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656261 prefixEnd_656261 := by exact prefixLift 656261
  have htrace : WordTrace (prefixWord ++ tailWord_656261) baseStart_656261 baseEnd_656261 := by
    simpa [prefixWord, tailWord_656261, baseEnd_656261] using wordTrace_append hprefix tailTrace_656261
  have hstable : (prefixWord ++ tailWord_656261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656261).length < 2 ^ (prefixWord ++ tailWord_656261).sum := by decide
  have hdescent : baseEnd_656261 < baseStart_656261 := by decide
  rcases family_descends (prefixWord ++ tailWord_656261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656264 : List Nat := [2, 1, 3, 3, 2, 1, 2, 4, 2]
def baseStart_656264 : Nat := 118140960795 + 656264 * 2 ^ 59
def prefixEnd_656264 : Nat := 4983230072969 + 3 ^ 40 * 656264 * 2
def baseEnd_656264 : Nat := 299536771770956086917247

theorem tailTrace_656264 : CollatzResearch.WordTrace tailWord_656264 prefixEnd_656264 299536771770956086917247 := by
  unfold tailWord_656264
  simp only [CollatzResearch.WordTrace]
  refine ⟨11967957247237541906543923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15957276329650055875391897 11967957247237541906543923)
  ·
    refine ⟨17951935870856312859815885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11967957247237541906543923 17951935870856312859815885)
    ·
      refine ⟨6731975951571117322430957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17951935870856312859815885 6731975951571117322430957)
      ·
        refine ⟨2524490981839168995911609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6731975951571117322430957 2524490981839168995911609)
        ·
          refine ⟨1893368236379376746933707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2524490981839168995911609 1893368236379376746933707)
          ·
            refine ⟨2840052354569065120400561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1893368236379376746933707 2840052354569065120400561)
            ·
              refine ⟨2130039265926798840300421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2840052354569065120400561 2130039265926798840300421)
              ·
                refine ⟨399382362361274782556329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2130039265926798840300421 399382362361274782556329)
                ·
                  refine ⟨299536771770956086917247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399382362361274782556329 299536771770956086917247)
                  ·
                    rfl

theorem cell20_656264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 2].length) (baseStart_656264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656264 prefixEnd_656264 := by exact prefixLift 656264
  have htrace : WordTrace (prefixWord ++ tailWord_656264) baseStart_656264 baseEnd_656264 := by
    simpa [prefixWord, tailWord_656264, baseEnd_656264] using wordTrace_append hprefix tailTrace_656264
  have hstable : (prefixWord ++ tailWord_656264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656264).length < 2 ^ (prefixWord ++ tailWord_656264).sum := by decide
  have hdescent : baseEnd_656264 < baseStart_656264 := by decide
  rcases family_descends (prefixWord ++ tailWord_656264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656268 : List Nat := [2, 2, 1, 2, 1, 2, 3, 3, 4]
def baseStart_656268 : Nat := 118140960795 + 656268 * 2 ^ 59
def prefixEnd_656268 : Nat := 4983230072969 + 3 ^ 40 * 656268 * 2
def baseEnd_656268 : Nat := 299538597479949850783897

theorem tailTrace_656268 : CollatzResearch.WordTrace tailWord_656268 prefixEnd_656268 299538597479949850783897 := by
  unfold tailWord_656268
  simp only [CollatzResearch.WordTrace]
  refine ⟨11968030193230296248116729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15957373590973728330822305 11968030193230296248116729)
  ·
    refine ⟨8976022644922722186087547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11968030193230296248116729 8976022644922722186087547)
    ·
      refine ⟨13464033967384083279131321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8976022644922722186087547 13464033967384083279131321)
      ·
        refine ⟨10098025475538062459348491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13464033967384083279131321 10098025475538062459348491)
        ·
          refine ⟨15147038213307093689022737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10098025475538062459348491 15147038213307093689022737)
          ·
            refine ⟨11360278659980320266767053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15147038213307093689022737 11360278659980320266767053)
            ·
              refine ⟨4260104497492620100037645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11360278659980320266767053 4260104497492620100037645)
              ·
                refine ⟨1597539186559732537514117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4260104497492620100037645 1597539186559732537514117)
                ·
                  refine ⟨299538597479949850783897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1597539186559732537514117 299538597479949850783897)
                  ·
                    rfl

theorem cell20_656268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_656268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656268 prefixEnd_656268 := by exact prefixLift 656268
  have htrace : WordTrace (prefixWord ++ tailWord_656268) baseStart_656268 baseEnd_656268 := by
    simpa [prefixWord, tailWord_656268, baseEnd_656268] using wordTrace_append hprefix tailTrace_656268
  have hstable : (prefixWord ++ tailWord_656268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656268).length < 2 ^ (prefixWord ++ tailWord_656268).sum := by decide
  have hdescent : baseEnd_656268 < baseStart_656268 := by decide
  rcases family_descends (prefixWord ++ tailWord_656268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656274 : List Nat := [3, 2, 3, 2, 2, 1, 3, 1, 3]
def baseStart_656274 : Nat := 118140960795 + 656274 * 2 ^ 59
def prefixEnd_656274 : Nat := 4983230072969 + 3 ^ 40 * 656274 * 2
def baseEnd_656274 : Nat := 299541336043440496583873

theorem tailTrace_656274 : CollatzResearch.WordTrace tailWord_656274 prefixEnd_656274 299541336043440496583873 := by
  unfold tailWord_656274
  simp only [CollatzResearch.WordTrace]
  refine ⟨5984069806109713880237969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15957519482959237013967917 5984069806109713880237969)
  ·
    refine ⟨4488052354582285410178477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5984069806109713880237969 4488052354582285410178477)
    ·
      refine ⟨1683019632968357028816929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4488052354582285410178477 1683019632968357028816929)
      ·
        refine ⟨1262264724726267771612697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1683019632968357028816929 1262264724726267771612697)
        ·
          refine ⟨946698543544700828709523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1262264724726267771612697 946698543544700828709523)
          ·
            refine ⟨1420047815317051243064285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 946698543544700828709523 1420047815317051243064285)
            ·
              refine ⟨532517930743894216149107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1420047815317051243064285 532517930743894216149107)
              ·
                refine ⟨798776896115841324223661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532517930743894216149107 798776896115841324223661)
                ·
                  refine ⟨299541336043440496583873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 798776896115841324223661 299541336043440496583873)
                  ·
                    rfl

theorem cell20_656274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_656274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656274 prefixEnd_656274 := by exact prefixLift 656274
  have htrace : WordTrace (prefixWord ++ tailWord_656274) baseStart_656274 baseEnd_656274 := by
    simpa [prefixWord, tailWord_656274, baseEnd_656274] using wordTrace_append hprefix tailTrace_656274
  have hstable : (prefixWord ++ tailWord_656274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656274).length < 2 ^ (prefixWord ++ tailWord_656274).sum := by decide
  have hdescent : baseEnd_656274 < baseStart_656274 := by decide
  rcases family_descends (prefixWord ++ tailWord_656274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656313 : List Nat := [1, 2, 1, 4, 2, 2, 8]
def baseStart_656313 : Nat := 118140960795 + 656313 * 2 ^ 59
def prefixEnd_656313 : Nat := 4983230072969 + 3 ^ 40 * 656313 * 2
def baseEnd_656313 : Nat := 33284348522903299364857

theorem tailTrace_656313 : CollatzResearch.WordTrace tailWord_656313 prefixEnd_656313 33284348522903299364857 := by
  unfold tailWord_656313
  simp only [CollatzResearch.WordTrace]
  refine ⟨23937701671297565181621593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15958467780865043454414395 23937701671297565181621593)
  ·
    refine ⟨17953276253473173886216195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23937701671297565181621593 17953276253473173886216195)
    ·
      refine ⟨26929914380209760829324293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17953276253473173886216195 26929914380209760829324293)
      ·
        refine ⟨5049358946289330155498305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26929914380209760829324293 5049358946289330155498305)
        ·
          refine ⟨3787019209716997616623729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5049358946289330155498305 3787019209716997616623729)
          ·
            refine ⟨2840264407287748212467797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3787019209716997616623729 2840264407287748212467797)
            ·
              refine ⟨33284348522903299364857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2840264407287748212467797 33284348522903299364857)
              ·
                rfl

theorem cell20_656313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 8].length) (baseStart_656313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656313 prefixEnd_656313 := by exact prefixLift 656313
  have htrace : WordTrace (prefixWord ++ tailWord_656313) baseStart_656313 baseEnd_656313 := by
    simpa [prefixWord, tailWord_656313, baseEnd_656313] using wordTrace_append hprefix tailTrace_656313
  have hstable : (prefixWord ++ tailWord_656313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656313).length < 2 ^ (prefixWord ++ tailWord_656313).sum := by decide
  have hdescent : baseEnd_656313 < baseStart_656313 := by decide
  rcases family_descends (prefixWord ++ tailWord_656313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656337 : List Nat := [1, 2, 2, 1, 2, 1, 5, 3, 3]
def baseStart_656337 : Nat := 118140960795 + 656337 * 2 ^ 59
def prefixEnd_656337 : Nat := 4983230072969 + 3 ^ 40 * 656337 * 2
def baseEnd_656337 : Nat := 299570090960092277483615

theorem tailTrace_656337 : CollatzResearch.WordTrace tailWord_656337 prefixEnd_656337 299570090960092277483615 := by
  unfold tailWord_656337
  simp only [CollatzResearch.WordTrace]
  refine ⟨23938577023210617280495265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15959051348807078186996843 23938577023210617280495265)
  ·
    refine ⟨17953932767407962960371449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23938577023210617280495265 17953932767407962960371449)
    ·
      refine ⟨13465449575555972220278587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17953932767407962960371449 13465449575555972220278587)
      ·
        refine ⟨20198174363333958330417881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13465449575555972220278587 20198174363333958330417881)
        ·
          refine ⟨15148630772500468747813411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20198174363333958330417881 15148630772500468747813411)
          ·
            refine ⟨22722946158750703121720117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15148630772500468747813411 22722946158750703121720117)
            ·
              refine ⟨2130276202382878417661261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22722946158750703121720117 2130276202382878417661261)
              ·
                refine ⟨798853575893579406622973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2130276202382878417661261 798853575893579406622973)
                ·
                  refine ⟨299570090960092277483615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 798853575893579406622973 299570090960092277483615)
                  ·
                    rfl

theorem cell20_656337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_656337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656337 prefixEnd_656337 := by exact prefixLift 656337
  have htrace : WordTrace (prefixWord ++ tailWord_656337) baseStart_656337 baseEnd_656337 := by
    simpa [prefixWord, tailWord_656337, baseEnd_656337] using wordTrace_append hprefix tailTrace_656337
  have hstable : (prefixWord ++ tailWord_656337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656337).length < 2 ^ (prefixWord ++ tailWord_656337).sum := by decide
  have hdescent : baseEnd_656337 < baseStart_656337 := by decide
  rcases family_descends (prefixWord ++ tailWord_656337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656374 : List Nat := [5, 1, 1, 1, 3, 3, 2, 2, 2]
def baseStart_656374 : Nat := 118140960795 + 656374 * 2 ^ 59
def prefixEnd_656374 : Nat := 4983230072969 + 3 ^ 40 * 656374 * 2
def baseEnd_656374 : Nat := 299586978768284593250131

theorem tailTrace_656374 : CollatzResearch.WordTrace tailWord_656374 prefixEnd_656374 299586978768284593250131 := by
  unfold tailWord_656374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1496245407754785787474511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15959951016051048399728117 1496245407754785787474511)
  ·
    refine ⟨2244368111632178681211767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1496245407754785787474511 2244368111632178681211767)
    ·
      refine ⟨3366552167448268021817651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2244368111632178681211767 3366552167448268021817651)
      ·
        refine ⟨5049828251172402032726477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3366552167448268021817651 5049828251172402032726477)
        ·
          refine ⟨1893685594189650762272429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5049828251172402032726477 1893685594189650762272429)
          ·
            refine ⟨710132097821119035852161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1893685594189650762272429 710132097821119035852161)
            ·
              refine ⟨532599073365839276889121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 710132097821119035852161 532599073365839276889121)
              ·
                refine ⟨399449305024379457666841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 532599073365839276889121 399449305024379457666841)
                ·
                  refine ⟨299586978768284593250131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399449305024379457666841 299586978768284593250131)
                  ·
                    rfl

theorem cell20_656374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_656374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656374 prefixEnd_656374 := by exact prefixLift 656374
  have htrace : WordTrace (prefixWord ++ tailWord_656374) baseStart_656374 baseEnd_656374 := by
    simpa [prefixWord, tailWord_656374, baseEnd_656374] using wordTrace_append hprefix tailTrace_656374
  have hstable : (prefixWord ++ tailWord_656374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656374).length < 2 ^ (prefixWord ++ tailWord_656374).sum := by decide
  have hdescent : baseEnd_656374 < baseStart_656374 := by decide
  rcases family_descends (prefixWord ++ tailWord_656374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656426 : List Nat := [3, 1, 4, 1, 4, 1, 1, 2, 3]
def baseStart_656426 : Nat := 118140960795 + 656426 * 2 ^ 59
def prefixEnd_656426 : Nat := 4983230072969 + 3 ^ 40 * 656426 * 2
def baseEnd_656426 : Nat := 299610712985203523516585

theorem tailTrace_656426 : CollatzResearch.WordTrace tailWord_656426 prefixEnd_656426 299610712985203523516585 := by
  unfold tailWord_656426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5985455779972046370121283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15961215413258790320323421 5985455779972046370121283)
  ·
    refine ⟨8978183669958069555181925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5985455779972046370121283 8978183669958069555181925)
    ·
      refine ⟨1683409438117138041596611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8978183669958069555181925 1683409438117138041596611)
      ·
        refine ⟨2525114157175707062394917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1683409438117138041596611 2525114157175707062394917)
        ·
          refine ⟨473458904470445074199047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2525114157175707062394917 473458904470445074199047)
          ·
            refine ⟨710188356705667611298571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473458904470445074199047 710188356705667611298571)
            ·
              refine ⟨1065282535058501416947857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710188356705667611298571 1065282535058501416947857)
              ·
                refine ⟨798961901293876062710893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1065282535058501416947857 798961901293876062710893)
                ·
                  refine ⟨299610712985203523516585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 798961901293876062710893 299610712985203523516585)
                  ·
                    rfl

theorem cell20_656426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_656426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656426 prefixEnd_656426 := by exact prefixLift 656426
  have htrace : WordTrace (prefixWord ++ tailWord_656426) baseStart_656426 baseEnd_656426 := by
    simpa [prefixWord, tailWord_656426, baseEnd_656426] using wordTrace_append hprefix tailTrace_656426
  have hstable : (prefixWord ++ tailWord_656426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656426).length < 2 ^ (prefixWord ++ tailWord_656426).sum := by decide
  have hdescent : baseEnd_656426 < baseStart_656426 := by decide
  rcases family_descends (prefixWord ++ tailWord_656426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656454 : List Nat := [6, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_656454 : Nat := 118140960795 + 656454 * 2 ^ 59
def prefixEnd_656454 : Nat := 4983230072969 + 3 ^ 40 * 656454 * 2
def baseEnd_656454 : Nat := 299623492948159870583137

theorem tailTrace_656454 : CollatzResearch.WordTrace tailWord_656454 prefixEnd_656454 299623492948159870583137 := by
  unfold tailWord_656454
  simp only [CollatzResearch.WordTrace]
  refine ⟨748213886368335820703263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15961896242524497508336277 748213886368335820703263)
  ·
    refine ⟨1122320829552503731054895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 748213886368335820703263 1122320829552503731054895)
    ·
      refine ⟨1683481244328755596582343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1122320829552503731054895 1683481244328755596582343)
      ·
        refine ⟨2525221866493133394873515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1683481244328755596582343 2525221866493133394873515)
        ·
          refine ⟨3787832799739700092310273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2525221866493133394873515 3787832799739700092310273)
          ·
            refine ⟨2840874599804775069232705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3787832799739700092310273 2840874599804775069232705)
            ·
              refine ⟨2130655949853581301924529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2840874599804775069232705 2130655949853581301924529)
              ·
                refine ⟨1597991962390185976443397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2130655949853581301924529 1597991962390185976443397)
                ·
                  refine ⟨299623492948159870583137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1597991962390185976443397 299623492948159870583137)
                  ·
                    rfl

theorem cell20_656454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_656454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656454 prefixEnd_656454 := by exact prefixLift 656454
  have htrace : WordTrace (prefixWord ++ tailWord_656454) baseStart_656454 baseEnd_656454 := by
    simpa [prefixWord, tailWord_656454, baseEnd_656454] using wordTrace_append hprefix tailTrace_656454
  have hstable : (prefixWord ++ tailWord_656454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656454).length < 2 ^ (prefixWord ++ tailWord_656454).sum := by decide
  have hdescent : baseEnd_656454 < baseStart_656454 := by decide
  rcases family_descends (prefixWord ++ tailWord_656454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656458 : List Nat := [3, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_656458 : Nat := 118140960795 + 656458 * 2 ^ 59
def prefixEnd_656458 : Nat := 4983230072969 + 3 ^ 40 * 656458 * 2
def baseEnd_656458 : Nat := 299625318657153634449787

theorem tailTrace_656458 : CollatzResearch.WordTrace tailWord_656458 prefixEnd_656458 299625318657153634449787 := by
  unfold tailWord_656458
  simp only [CollatzResearch.WordTrace]
  refine ⟨5985747563943063736412507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15961993503848169963766685 5985747563943063736412507)
  ·
    refine ⟨8978621345914595604618761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5985747563943063736412507 8978621345914595604618761)
    ·
      refine ⟨6733966009435946703464071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8978621345914595604618761 6733966009435946703464071)
      ·
        refine ⟨10100949014153920055196107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6733966009435946703464071 10100949014153920055196107)
        ·
          refine ⟨15151423521230880082794161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10100949014153920055196107 15151423521230880082794161)
          ·
            refine ⟨11363567640923160062095621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15151423521230880082794161 11363567640923160062095621)
            ·
              refine ⟨2130668932673092511642929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11363567640923160062095621 2130668932673092511642929)
              ·
                refine ⟨1598001699504819383732197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2130668932673092511642929 1598001699504819383732197)
                ·
                  refine ⟨299625318657153634449787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1598001699504819383732197 299625318657153634449787)
                  ·
                    rfl

theorem cell20_656458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_656458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656458 prefixEnd_656458 := by exact prefixLift 656458
  have htrace : WordTrace (prefixWord ++ tailWord_656458) baseStart_656458 baseEnd_656458 := by
    simpa [prefixWord, tailWord_656458, baseEnd_656458] using wordTrace_append hprefix tailTrace_656458
  have hstable : (prefixWord ++ tailWord_656458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656458).length < 2 ^ (prefixWord ++ tailWord_656458).sum := by decide
  have hdescent : baseEnd_656458 < baseStart_656458 := by decide
  rcases family_descends (prefixWord ++ tailWord_656458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656461 : List Nat := [1, 6, 1, 1, 1, 2, 4, 4]
def baseStart_656461 : Nat := 118140960795 + 656461 * 2 ^ 59
def prefixEnd_656461 : Nat := 4983230072969 + 3 ^ 40 * 656461 * 2
def baseEnd_656461 : Nat := 99875562646299652449925

theorem tailTrace_656461 : CollatzResearch.WordTrace tailWord_656461 prefixEnd_656461 99875562646299652449925 := by
  unfold tailWord_656461
  simp only [CollatzResearch.WordTrace]
  refine ⟨23943099674761386458009237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15962066449840924305339491 23943099674761386458009237)
  ·
    refine ⟨1122332797254439990219183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23943099674761386458009237 1122332797254439990219183)
    ·
      refine ⟨1683499195881659985328775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1122332797254439990219183 1683499195881659985328775)
      ·
        refine ⟨2525248793822489977993163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1683499195881659985328775 2525248793822489977993163)
        ·
          refine ⟨3787873190733734966989745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2525248793822489977993163 3787873190733734966989745)
          ·
            refine ⟨2840904893050301225242309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3787873190733734966989745 2840904893050301225242309)
            ·
              refine ⟨532669667446931479732933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2840904893050301225242309 532669667446931479732933)
              ·
                refine ⟨99875562646299652449925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 532669667446931479732933 99875562646299652449925)
                ·
                  rfl

theorem cell20_656461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 4].length) (baseStart_656461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656461 prefixEnd_656461 := by exact prefixLift 656461
  have htrace : WordTrace (prefixWord ++ tailWord_656461) baseStart_656461 baseEnd_656461 := by
    simpa [prefixWord, tailWord_656461, baseEnd_656461] using wordTrace_append hprefix tailTrace_656461
  have hstable : (prefixWord ++ tailWord_656461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656461).length < 2 ^ (prefixWord ++ tailWord_656461).sum := by decide
  have hdescent : baseEnd_656461 < baseStart_656461 := by decide
  rcases family_descends (prefixWord ++ tailWord_656461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656472 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 7]
def baseStart_656472 : Nat := 118140960795 + 656472 * 2 ^ 59
def prefixEnd_656472 : Nat := 4983230072969 + 3 ^ 40 * 656472 * 2
def baseEnd_656472 : Nat := 299631708638631807983063

theorem tailTrace_656472 : CollatzResearch.WordTrace tailWord_656472 prefixEnd_656472 299631708638631807983063 := by
  unfold tailWord_656472
  simp only [CollatzResearch.WordTrace]
  refine ⟨11971750438860767668329835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15962333918481023557773113 11971750438860767668329835)
  ·
    refine ⟨17957625658291151502494753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11971750438860767668329835 17957625658291151502494753)
    ·
      refine ⟨13468219243718363626871065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17957625658291151502494753 13468219243718363626871065)
      ·
        refine ⟨10101164432788772720153299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13468219243718363626871065 10101164432788772720153299)
        ·
          refine ⟨15151746649183159080229949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10101164432788772720153299 15151746649183159080229949)
          ·
            refine ⟨5681904993443684655086231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15151746649183159080229949 5681904993443684655086231)
            ·
              refine ⟨8522857490165526982629347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5681904993443684655086231 8522857490165526982629347)
              ·
                refine ⟨12784286235248290473944021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8522857490165526982629347 12784286235248290473944021)
                ·
                  refine ⟨299631708638631807983063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12784286235248290473944021 299631708638631807983063)
                  ·
                    rfl

theorem cell20_656472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_656472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656472 prefixEnd_656472 := by exact prefixLift 656472
  have htrace : WordTrace (prefixWord ++ tailWord_656472) baseStart_656472 baseEnd_656472 := by
    simpa [prefixWord, tailWord_656472, baseEnd_656472] using wordTrace_append hprefix tailTrace_656472
  have hstable : (prefixWord ++ tailWord_656472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656472).length < 2 ^ (prefixWord ++ tailWord_656472).sum := by decide
  have hdescent : baseEnd_656472 < baseStart_656472 := by decide
  rcases family_descends (prefixWord ++ tailWord_656472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656478 : List Nat := [4, 4, 1, 1, 1, 3, 6]
def baseStart_656478 : Nat := 118140960795 + 656478 * 2 ^ 59
def prefixEnd_656478 : Nat := 4983230072969 + 3 ^ 40 * 656478 * 2
def baseEnd_656478 : Nat := 33292716355791383753671

theorem tailTrace_656478 : CollatzResearch.WordTrace tailWord_656478 prefixEnd_656478 33292716355791383753671 := by
  unfold tailWord_656478
  simp only [CollatzResearch.WordTrace]
  refine ⟨2992964964462474795172261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15962479810466532240918725 2992964964462474795172261)
  ·
    refine ⟨561180930836714024094799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2992964964462474795172261 561180930836714024094799)
    ·
      refine ⟨841771396255071036142199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 561180930836714024094799 841771396255071036142199)
      ·
        refine ⟨1262657094382606554213299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 841771396255071036142199 1262657094382606554213299)
        ·
          refine ⟨1893985641573909831319949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1262657094382606554213299 1893985641573909831319949)
          ·
            refine ⟨710244615590216186744981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1893985641573909831319949 710244615590216186744981)
            ·
              refine ⟨33292716355791383753671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 710244615590216186744981 33292716355791383753671)
              ·
                rfl

theorem cell20_656478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 6].length) (baseStart_656478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656478 prefixEnd_656478 := by exact prefixLift 656478
  have htrace : WordTrace (prefixWord ++ tailWord_656478) baseStart_656478 baseEnd_656478 := by
    simpa [prefixWord, tailWord_656478, baseEnd_656478] using wordTrace_append hprefix tailTrace_656478
  have hstable : (prefixWord ++ tailWord_656478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656478).length < 2 ^ (prefixWord ++ tailWord_656478).sum := by decide
  have hdescent : baseEnd_656478 < baseStart_656478 := by decide
  rcases family_descends (prefixWord ++ tailWord_656478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656482 : List Nat := [3, 3, 2, 2, 1, 1, 8]
def baseStart_656482 : Nat := 118140960795 + 656482 * 2 ^ 59
def prefixEnd_656482 : Nat := 4983230072969 + 3 ^ 40 * 656482 * 2
def baseEnd_656482 : Nat := 33292919212346246405521

theorem tailTrace_656482 : CollatzResearch.WordTrace tailWord_656482 prefixEnd_656482 33292919212346246405521 := by
  unfold tailWord_656482
  simp only [CollatzResearch.WordTrace]
  refine ⟨5985966401921326761130925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15962577071790204696349133 5985966401921326761130925)
  ·
    refine ⟨2244737400720497535424097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5985966401921326761130925 2244737400720497535424097)
    ·
      refine ⟨1683553050540373151568073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2244737400720497535424097 1683553050540373151568073)
      ·
        refine ⟨1262664787905279863676055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1683553050540373151568073 1262664787905279863676055)
        ·
          refine ⟨1893997181857919795514083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1262664787905279863676055 1893997181857919795514083)
          ·
            refine ⟨2840995772786879693271125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1893997181857919795514083 2840995772786879693271125)
            ·
              refine ⟨33292919212346246405521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2840995772786879693271125 33292919212346246405521)
              ·
                rfl

theorem cell20_656482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 8].length) (baseStart_656482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656482 prefixEnd_656482 := by exact prefixLift 656482
  have htrace : WordTrace (prefixWord ++ tailWord_656482) baseStart_656482 baseEnd_656482 := by
    simpa [prefixWord, tailWord_656482, baseEnd_656482] using wordTrace_append hprefix tailTrace_656482
  have hstable : (prefixWord ++ tailWord_656482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656482).length < 2 ^ (prefixWord ++ tailWord_656482).sum := by decide
  have hdescent : baseEnd_656482 < baseStart_656482 := by decide
  rcases family_descends (prefixWord ++ tailWord_656482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656488 : List Nat := [2, 1, 4, 4, 1, 1, 3, 2, 2]
def baseStart_656488 : Nat := 118140960795 + 656488 * 2 ^ 59
def prefixEnd_656488 : Nat := 4983230072969 + 3 ^ 40 * 656488 * 2
def baseEnd_656488 : Nat := 299639011474606863449665

theorem tailTrace_656488 : CollatzResearch.WordTrace tailWord_656488 prefixEnd_656488 299639011474606863449665 := by
  unfold tailWord_656488
  simp only [CollatzResearch.WordTrace]
  refine ⟨11972042222831785034621059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15962722963775713379494745 11972042222831785034621059)
  ·
    refine ⟨17958063334247677551931589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11972042222831785034621059 17958063334247677551931589)
    ·
      refine ⟨3367136875171439540987173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17958063334247677551931589 3367136875171439540987173)
      ·
        refine ⟨631338164094644913935095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3367136875171439540987173 631338164094644913935095)
        ·
          refine ⟨947007246141967370902643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 631338164094644913935095 947007246141967370902643)
          ·
            refine ⟨1420510869212951056353965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 947007246141967370902643 1420510869212951056353965)
            ·
              refine ⟨532691575954856646132737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1420510869212951056353965 532691575954856646132737)
              ·
                refine ⟨399518681966142484599553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 532691575954856646132737 399518681966142484599553)
                ·
                  refine ⟨299639011474606863449665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399518681966142484599553 299639011474606863449665)
                  ·
                    rfl

theorem cell20_656488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 2].length) (baseStart_656488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656488 prefixEnd_656488 := by exact prefixLift 656488
  have htrace : WordTrace (prefixWord ++ tailWord_656488) baseStart_656488 baseEnd_656488 := by
    simpa [prefixWord, tailWord_656488, baseEnd_656488] using wordTrace_append hprefix tailTrace_656488
  have hstable : (prefixWord ++ tailWord_656488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656488).length < 2 ^ (prefixWord ++ tailWord_656488).sum := by decide
  have hdescent : baseEnd_656488 < baseStart_656488 := by decide
  rcases family_descends (prefixWord ++ tailWord_656488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656492 : List Nat := [2, 2, 1, 1, 3, 2, 5, 2, 2]
def baseStart_656492 : Nat := 118140960795 + 656492 * 2 ^ 59
def prefixEnd_656492 : Nat := 4983230072969 + 3 ^ 40 * 656492 * 2
def baseEnd_656492 : Nat := 299640837183600627316315

theorem tailTrace_656492 : CollatzResearch.WordTrace tailWord_656492 prefixEnd_656492 299640837183600627316315 := by
  unfold tailWord_656492
  simp only [CollatzResearch.WordTrace]
  refine ⟨11972115168824539376193865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15962820225099385834925153 11972115168824539376193865)
  ·
    refine ⟨8979086376618404532145399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11972115168824539376193865 8979086376618404532145399)
    ·
      refine ⟨13468629564927606798218099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8979086376618404532145399 13468629564927606798218099)
      ·
        refine ⟨20202944347391410197327149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13468629564927606798218099 20202944347391410197327149)
        ·
          refine ⟨7576104130271778823997681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20202944347391410197327149 7576104130271778823997681)
          ·
            refine ⟨5682078097703834117998261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7576104130271778823997681 5682078097703834117998261)
            ·
              refine ⟨532694821659734448562337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5682078097703834117998261 532694821659734448562337)
              ·
                refine ⟨399521116244800836421753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 532694821659734448562337 399521116244800836421753)
                ·
                  refine ⟨299640837183600627316315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399521116244800836421753 299640837183600627316315)
                  ·
                    rfl

theorem cell20_656492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_656492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656492 prefixEnd_656492 := by exact prefixLift 656492
  have htrace : WordTrace (prefixWord ++ tailWord_656492) baseStart_656492 baseEnd_656492 := by
    simpa [prefixWord, tailWord_656492, baseEnd_656492] using wordTrace_append hprefix tailTrace_656492
  have hstable : (prefixWord ++ tailWord_656492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656492).length < 2 ^ (prefixWord ++ tailWord_656492).sum := by decide
  have hdescent : baseEnd_656492 < baseStart_656492 := by decide
  rcases family_descends (prefixWord ++ tailWord_656492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656503 : List Nat := [1, 1, 3, 1, 1, 4, 4, 5]
def baseStart_656503 : Nat := 118140960795 + 656503 * 2 ^ 59
def prefixEnd_656503 : Nat := 4983230072969 + 3 ^ 40 * 656503 * 2
def baseEnd_656503 : Nat := 99881952627777825983201

theorem tailTrace_656503 : CollatzResearch.WordTrace tailWord_656503 prefixEnd_656503 99881952627777825983201 := by
  unfold tailWord_656503
  simp only [CollatzResearch.WordTrace]
  refine ⟨23944631540609227631038163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15963087693739485087358775 23944631540609227631038163)
  ·
    refine ⟨35916947310913841446557245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23944631540609227631038163 35916947310913841446557245)
    ·
      refine ⟨13468855241592690542458967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35916947310913841446557245 13468855241592690542458967)
      ·
        refine ⟨20203282862389035813688451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13468855241592690542458967 20203282862389035813688451)
        ·
          refine ⟨30304924293583553720532677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20203282862389035813688451 30304924293583553720532677)
          ·
            refine ⟨5682173305046916322599877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30304924293583553720532677 5682173305046916322599877)
            ·
              refine ⟨1065407494696296810487477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5682173305046916322599877 1065407494696296810487477)
              ·
                refine ⟨99881952627777825983201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1065407494696296810487477 99881952627777825983201)
                ·
                  rfl

theorem cell20_656503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 5].length) (baseStart_656503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656503 prefixEnd_656503 := by exact prefixLift 656503
  have htrace : WordTrace (prefixWord ++ tailWord_656503) baseStart_656503 baseEnd_656503 := by
    simpa [prefixWord, tailWord_656503, baseEnd_656503] using wordTrace_append hprefix tailTrace_656503
  have hstable : (prefixWord ++ tailWord_656503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656503).length < 2 ^ (prefixWord ++ tailWord_656503).sum := by decide
  have hdescent : baseEnd_656503 < baseStart_656503 := by decide
  rcases family_descends (prefixWord ++ tailWord_656503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656572 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 6]
def baseStart_656572 : Nat := 118140960795 + 656572 * 2 ^ 59
def prefixEnd_656572 : Nat := 4983230072969 + 3 ^ 40 * 656572 * 2
def baseEnd_656572 : Nat := 299677351363475904649321

theorem tailTrace_656572 : CollatzResearch.WordTrace tailWord_656572 prefixEnd_656572 299677351363475904649321 := by
  unfold tailWord_656572
  simp only [CollatzResearch.WordTrace]
  refine ⟨11973574088679626207649985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15964765451572834943533313 11973574088679626207649985)
  ·
    refine ⟨8980180566509719655737489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11973574088679626207649985 8980180566509719655737489)
    ·
      refine ⟨6735135424882289741803117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8980180566509719655737489 6735135424882289741803117)
      ·
        refine ⟨2525675784330858653176169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6735135424882289741803117 2525675784330858653176169)
        ·
          refine ⟨1894256838248143989882127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2525675784330858653176169 1894256838248143989882127)
          ·
            refine ⟨2841385257372215984823191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894256838248143989882127 2841385257372215984823191)
            ·
              refine ⟨4262077886058323977234787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2841385257372215984823191 4262077886058323977234787)
              ·
                refine ⟨6393116829087485965852181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4262077886058323977234787 6393116829087485965852181)
                ·
                  refine ⟨299677351363475904649321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6393116829087485965852181 299677351363475904649321)
                  ·
                    rfl

theorem cell20_656572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_656572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656572 prefixEnd_656572 := by exact prefixLift 656572
  have htrace : WordTrace (prefixWord ++ tailWord_656572) baseStart_656572 baseEnd_656572 := by
    simpa [prefixWord, tailWord_656572, baseEnd_656572] using wordTrace_append hprefix tailTrace_656572
  have hstable : (prefixWord ++ tailWord_656572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656572).length < 2 ^ (prefixWord ++ tailWord_656572).sum := by decide
  have hdescent : baseEnd_656572 < baseStart_656572 := by decide
  rcases family_descends (prefixWord ++ tailWord_656572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656593 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 8]
def baseStart_656593 : Nat := 118140960795 + 656593 * 2 ^ 59
def prefixEnd_656593 : Nat := 4983230072969 + 3 ^ 40 * 656593 * 2
def baseEnd_656593 : Nat := 299686936335693164949235

theorem tailTrace_656593 : CollatzResearch.WordTrace tailWord_656593 prefixEnd_656593 299686936335693164949235 := by
  unfold tailWord_656593
  simp only [CollatzResearch.WordTrace]
  refine ⟨23947914110283173001814433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15965276073522115334542955 23947914110283173001814433)
  ·
    refine ⟨17960935582712379751360825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23947914110283173001814433 17960935582712379751360825)
    ·
      refine ⟨13470701687034284813520619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17960935582712379751360825 13470701687034284813520619)
      ·
        refine ⟨20206052530551427220280929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13470701687034284813520619 20206052530551427220280929)
        ·
          refine ⟨15154539397913570415210697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20206052530551427220280929 15154539397913570415210697)
          ·
            refine ⟨11365904548435177811408023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15154539397913570415210697 11365904548435177811408023)
            ·
              refine ⟨17048856822652766717112035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11365904548435177811408023 17048856822652766717112035)
              ·
                refine ⟨25573285233979150075668053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17048856822652766717112035 25573285233979150075668053)
                ·
                  refine ⟨299686936335693164949235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25573285233979150075668053 299686936335693164949235)
                  ·
                    rfl

theorem cell20_656593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_656593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656593 prefixEnd_656593 := by exact prefixLift 656593
  have htrace : WordTrace (prefixWord ++ tailWord_656593) baseStart_656593 baseEnd_656593 := by
    simpa [prefixWord, tailWord_656593, baseEnd_656593] using wordTrace_append hprefix tailTrace_656593
  have hstable : (prefixWord ++ tailWord_656593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656593).length < 2 ^ (prefixWord ++ tailWord_656593).sum := by decide
  have hdescent : baseEnd_656593 < baseStart_656593 := by decide
  rcases family_descends (prefixWord ++ tailWord_656593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656620 : List Nat := [2, 2, 1, 1, 2, 5, 3, 1, 3]
def baseStart_656620 : Nat := 118140960795 + 656620 * 2 ^ 59
def prefixEnd_656620 : Nat := 4983230072969 + 3 ^ 40 * 656620 * 2
def baseEnd_656620 : Nat := 299699259871401071049125

theorem tailTrace_656620 : CollatzResearch.WordTrace tailWord_656620 prefixEnd_656620 299699259871401071049125 := by
  unfold tailWord_656620
  simp only [CollatzResearch.WordTrace]
  refine ⟨11974449440592678306523657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15965932587456904408698209 11974449440592678306523657)
  ·
    refine ⟨8980837080444508729892743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11974449440592678306523657 8980837080444508729892743)
    ·
      refine ⟨13471255620666763094839115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8980837080444508729892743 13471255620666763094839115)
      ·
        refine ⟨20206883431000144642258673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13471255620666763094839115 20206883431000144642258673)
        ·
          refine ⟨15155162573250108481694005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20206883431000144642258673 15155162573250108481694005)
          ·
            refine ⟨1420796491242197670158813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15155162573250108481694005 1420796491242197670158813)
            ·
              refine ⟨532798684215824126309555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1420796491242197670158813 532798684215824126309555)
              ·
                refine ⟨799198026323736189464333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532798684215824126309555 799198026323736189464333)
                ·
                  refine ⟨299699259871401071049125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 799198026323736189464333 299699259871401071049125)
                  ·
                    rfl

theorem cell20_656620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_656620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656620 prefixEnd_656620 := by exact prefixLift 656620
  have htrace : WordTrace (prefixWord ++ tailWord_656620) baseStart_656620 baseEnd_656620 := by
    simpa [prefixWord, tailWord_656620, baseEnd_656620] using wordTrace_append hprefix tailTrace_656620
  have hstable : (prefixWord ++ tailWord_656620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656620).length < 2 ^ (prefixWord ++ tailWord_656620).sum := by decide
  have hdescent : baseEnd_656620 < baseStart_656620 := by decide
  rcases family_descends (prefixWord ++ tailWord_656620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656644 : List Nat := [2, 3, 2, 2, 2, 1, 3, 3, 2]
def baseStart_656644 : Nat := 118140960795 + 656644 * 2 ^ 59
def prefixEnd_656644 : Nat := 4983230072969 + 3 ^ 40 * 656644 * 2
def baseEnd_656644 : Nat := 299710214125363654249027

theorem tailTrace_656644 : CollatzResearch.WordTrace tailWord_656644 prefixEnd_656644 299710214125363654249027 := by
  unfold tailWord_656644
  simp only [CollatzResearch.WordTrace]
  refine ⟨11974887116549204355960493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15966516155398939141280657 11974887116549204355960493)
  ·
    refine ⟨4490582668705951633485185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11974887116549204355960493 4490582668705951633485185)
    ·
      refine ⟨3367937001529463725113889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4490582668705951633485185 3367937001529463725113889)
      ·
        refine ⟨2525952751147097793835417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3367937001529463725113889 2525952751147097793835417)
        ·
          refine ⟨1894464563360323345376563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2525952751147097793835417 1894464563360323345376563)
          ·
            refine ⟨2841696845040485018064845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1894464563360323345376563 2841696845040485018064845)
            ·
              refine ⟨1065636316890181881774317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2841696845040485018064845 1065636316890181881774317)
              ·
                refine ⟨399613618833818205665369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1065636316890181881774317 399613618833818205665369)
                ·
                  refine ⟨299710214125363654249027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399613618833818205665369 299710214125363654249027)
                  ·
                    rfl

theorem cell20_656644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_656644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656644 prefixEnd_656644 := by exact prefixLift 656644
  have htrace : WordTrace (prefixWord ++ tailWord_656644) baseStart_656644 baseEnd_656644 := by
    simpa [prefixWord, tailWord_656644, baseEnd_656644] using wordTrace_append hprefix tailTrace_656644
  have hstable : (prefixWord ++ tailWord_656644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656644).length < 2 ^ (prefixWord ++ tailWord_656644).sum := by decide
  have hdescent : baseEnd_656644 < baseStart_656644 := by decide
  rcases family_descends (prefixWord ++ tailWord_656644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656672 : List Nat := [2, 1, 1, 5, 3, 1, 2, 5]
def baseStart_656672 : Nat := 118140960795 + 656672 * 2 ^ 59
def prefixEnd_656672 : Nat := 4983230072969 + 3 ^ 40 * 656672 * 2
def baseEnd_656672 : Nat := 99907664696106667105193

theorem tailTrace_656672 : CollatzResearch.WordTrace tailWord_656672 prefixEnd_656672 99907664696106667105193 := by
  unfold tailWord_656672
  simp only [CollatzResearch.WordTrace]
  refine ⟨11975397738498484746970135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15967196984664646329293513 11975397738498484746970135)
  ·
    refine ⟨17963096607747727120455203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11975397738498484746970135 17963096607747727120455203)
    ·
      refine ⟨26944644911621590680682805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17963096607747727120455203 26944644911621590680682805)
      ·
        refine ⟨2526060460464524126314013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26944644911621590680682805 2526060460464524126314013)
        ·
          refine ⟨947272672674196547367755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2526060460464524126314013 947272672674196547367755)
          ·
            refine ⟨1420909009011294821051633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 947272672674196547367755 1420909009011294821051633)
            ·
              refine ⟨1065681756758471115788725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1420909009011294821051633 1065681756758471115788725)
              ·
                refine ⟨99907664696106667105193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1065681756758471115788725 99907664696106667105193)
                ·
                  rfl

theorem cell20_656672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 5].length) (baseStart_656672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656672 prefixEnd_656672 := by exact prefixLift 656672
  have htrace : WordTrace (prefixWord ++ tailWord_656672) baseStart_656672 baseEnd_656672 := by
    simpa [prefixWord, tailWord_656672, baseEnd_656672] using wordTrace_append hprefix tailTrace_656672
  have hstable : (prefixWord ++ tailWord_656672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656672).length < 2 ^ (prefixWord ++ tailWord_656672).sum := by decide
  have hdescent : baseEnd_656672 < baseStart_656672 := by decide
  rcases family_descends (prefixWord ++ tailWord_656672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656693 : List Nat := [1, 3, 3, 1, 2, 2, 2, 6]
def baseStart_656693 : Nat := 118140960795 + 656693 * 2 ^ 59
def prefixEnd_656693 : Nat := 4983230072969 + 3 ^ 40 * 656693 * 2
def baseEnd_656693 : Nat := 99910859686845753871831

theorem tailTrace_656693 : CollatzResearch.WordTrace tailWord_656693 prefixEnd_656693 99910859686845753871831 := by
  unfold tailWord_656693
  simp only [CollatzResearch.WordTrace]
  refine ⟨23951561409920890080454733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15967707606613926720303155 23951561409920890080454733)
  ·
    refine ⟨8981835528720333780170525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23951561409920890080454733 8981835528720333780170525)
    ·
      refine ⟨3368188323270125167563947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8981835528720333780170525 3368188323270125167563947)
      ·
        refine ⟨5052282484905187751345921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3368188323270125167563947 5052282484905187751345921)
        ·
          refine ⟨3789211863678890813509441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5052282484905187751345921 3789211863678890813509441)
          ·
            refine ⟨2841908897759168110132081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3789211863678890813509441 2841908897759168110132081)
            ·
              refine ⟨2131431673319376082599061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2841908897759168110132081 2131431673319376082599061)
              ·
                refine ⟨99910859686845753871831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2131431673319376082599061 99910859686845753871831)
                ·
                  rfl

theorem cell20_656693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 6].length) (baseStart_656693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656693 prefixEnd_656693 := by exact prefixLift 656693
  have htrace : WordTrace (prefixWord ++ tailWord_656693) baseStart_656693 baseEnd_656693 := by
    simpa [prefixWord, tailWord_656693, baseEnd_656693] using wordTrace_append hprefix tailTrace_656693
  have hstable : (prefixWord ++ tailWord_656693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656693).length < 2 ^ (prefixWord ++ tailWord_656693).sum := by decide
  have hdescent : baseEnd_656693 < baseStart_656693 := by decide
  rcases family_descends (prefixWord ++ tailWord_656693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656724 : List Nat := [2, 4, 1, 1, 2, 1, 2, 3, 4]
def baseStart_656724 : Nat := 118140960795 + 656724 * 2 ^ 59
def prefixEnd_656724 : Nat := 4983230072969 + 3 ^ 40 * 656724 * 2
def baseEnd_656724 : Nat := 299746728305238931582033

theorem tailTrace_656724 : CollatzResearch.WordTrace tailWord_656724 prefixEnd_656724 299746728305238931582033 := by
  unfold tailWord_656724
  simp only [CollatzResearch.WordTrace]
  refine ⟨11976346036404291187416613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15968461381872388249888817 11976346036404291187416613)
  ·
    refine ⟨2245564881825804597640615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11976346036404291187416613 2245564881825804597640615)
    ·
      refine ⟨3368347322738706896460923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2245564881825804597640615 3368347322738706896460923)
      ·
        refine ⟨5052520984108060344691385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3368347322738706896460923 5052520984108060344691385)
        ·
          refine ⟨3789390738081045258518539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5052520984108060344691385 3789390738081045258518539)
          ·
            refine ⟨5684086107121567887777809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3789390738081045258518539 5684086107121567887777809)
            ·
              refine ⟨4263064580341175915833357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5684086107121567887777809 4263064580341175915833357)
              ·
                refine ⟨1598649217627940968437509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4263064580341175915833357 1598649217627940968437509)
                ·
                  refine ⟨299746728305238931582033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1598649217627940968437509 299746728305238931582033)
                  ·
                    rfl

theorem cell20_656724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_656724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656724 prefixEnd_656724 := by exact prefixLift 656724
  have htrace : WordTrace (prefixWord ++ tailWord_656724) baseStart_656724 baseEnd_656724 := by
    simpa [prefixWord, tailWord_656724, baseEnd_656724] using wordTrace_append hprefix tailTrace_656724
  have hstable : (prefixWord ++ tailWord_656724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656724).length < 2 ^ (prefixWord ++ tailWord_656724).sum := by decide
  have hdescent : baseEnd_656724 < baseStart_656724 := by decide
  rcases family_descends (prefixWord ++ tailWord_656724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656748 : List Nat := [2, 2, 1, 1, 5, 2, 3, 4]
def baseStart_656748 : Nat := 118140960795 + 656748 * 2 ^ 59
def prefixEnd_656748 : Nat := 4983230072969 + 3 ^ 40 * 656748 * 2
def baseEnd_656748 : Nat := 99919227519733838260645

theorem tailTrace_656748 : CollatzResearch.WordTrace tailWord_656748 prefixEnd_656748 99919227519733838260645 := by
  unfold tailWord_656748
  simp only [CollatzResearch.WordTrace]
  refine ⟨11976783712360817236853449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15969044949814422982471265 11976783712360817236853449)
  ·
    refine ⟨8982587784270612927640087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11976783712360817236853449 8982587784270612927640087)
    ·
      refine ⟨13473881676405919391460131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8982587784270612927640087 13473881676405919391460131)
      ·
        refine ⟨20210822514608879087190197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13473881676405919391460131 20210822514608879087190197)
        ·
          refine ⟨1894764610744582414424081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20210822514608879087190197 1894764610744582414424081)
          ·
            refine ⟨1421073458058436810818061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1894764610744582414424081 1421073458058436810818061)
            ·
              refine ⟨532902546771913804056773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1421073458058436810818061 532902546771913804056773)
              ·
                refine ⟨99919227519733838260645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 532902546771913804056773 99919227519733838260645)
                ·
                  rfl

theorem cell20_656748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 4].length) (baseStart_656748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656748 prefixEnd_656748 := by exact prefixLift 656748
  have htrace : WordTrace (prefixWord ++ tailWord_656748) baseStart_656748 baseEnd_656748 := by
    simpa [prefixWord, tailWord_656748, baseEnd_656748] using wordTrace_append hprefix tailTrace_656748
  have hstable : (prefixWord ++ tailWord_656748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656748).length < 2 ^ (prefixWord ++ tailWord_656748).sum := by decide
  have hdescent : baseEnd_656748 < baseStart_656748 := by decide
  rcases family_descends (prefixWord ++ tailWord_656748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656772 : List Nat := [2, 3, 2, 1, 1, 5, 1, 2, 3]
def baseStart_656772 : Nat := 118140960795 + 656772 * 2 ^ 59
def prefixEnd_656772 : Nat := 4983230072969 + 3 ^ 40 * 656772 * 2
def baseEnd_656772 : Nat := 299768636813164097981837

theorem tailTrace_656772 : CollatzResearch.WordTrace tailWord_656772 prefixEnd_656772 299768636813164097981837 := by
  unfold tailWord_656772
  simp only [CollatzResearch.WordTrace]
  refine ⟨11977221388317343286290285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15969628517756457715053713 11977221388317343286290285)
  ·
    refine ⟨4491458020619003732358857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11977221388317343286290285 4491458020619003732358857)
    ·
      refine ⟨3368593515464252799269143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4491458020619003732358857 3368593515464252799269143)
      ·
        refine ⟨5052890273196379198903715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3368593515464252799269143 5052890273196379198903715)
        ·
          refine ⟨7579335409794568798355573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5052890273196379198903715 7579335409794568798355573)
          ·
            refine ⟨710562694668240824845835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7579335409794568798355573 710562694668240824845835)
            ·
              refine ⟨1065844042002361237268753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710562694668240824845835 1065844042002361237268753)
              ·
                refine ⟨799383031501770927951565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1065844042002361237268753 799383031501770927951565)
                ·
                  refine ⟨299768636813164097981837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 799383031501770927951565 299768636813164097981837)
                  ·
                    rfl

theorem cell20_656772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_656772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656772 prefixEnd_656772 := by exact prefixLift 656772
  have htrace : WordTrace (prefixWord ++ tailWord_656772) baseStart_656772 baseEnd_656772 := by
    simpa [prefixWord, tailWord_656772, baseEnd_656772] using wordTrace_append hprefix tailTrace_656772
  have hstable : (prefixWord ++ tailWord_656772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656772).length < 2 ^ (prefixWord ++ tailWord_656772).sum := by decide
  have hdescent : baseEnd_656772 < baseStart_656772 := by decide
  rcases family_descends (prefixWord ++ tailWord_656772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656807 : List Nat := [1, 1, 6, 1, 1, 1, 3, 6]
def baseStart_656807 : Nat := 118140960795 + 656807 * 2 ^ 59
def prefixEnd_656807 : Nat := 4983230072969 + 3 ^ 40 * 656807 * 2
def baseEnd_656807 : Nat := 99928203922286510605009

theorem tailTrace_656807 : CollatzResearch.WordTrace tailWord_656807 prefixEnd_656807 99928203922286510605009 := by
  unfold tailWord_656807
  simp only [CollatzResearch.WordTrace]
  refine ⟨23955719331507887550104675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15970479554338591700069783 23955719331507887550104675)
  ·
    refine ⟨35933578997261831325157013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23955719331507887550104675 35933578997261831325157013)
    ·
      refine ⟨1684386515496648343366735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35933578997261831325157013 1684386515496648343366735)
      ·
        refine ⟨2526579773244972515050103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1684386515496648343366735 2526579773244972515050103)
        ·
          refine ⟨3789869659867458772575155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2526579773244972515050103 3789869659867458772575155)
          ·
            refine ⟨5684804489801188158862733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3789869659867458772575155 5684804489801188158862733)
            ·
              refine ⟨2131801683675445559573525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5684804489801188158862733 2131801683675445559573525)
              ·
                refine ⟨99928203922286510605009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2131801683675445559573525 99928203922286510605009)
                ·
                  rfl

theorem cell20_656807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 6].length) (baseStart_656807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656807 prefixEnd_656807 := by exact prefixLift 656807
  have htrace : WordTrace (prefixWord ++ tailWord_656807) baseStart_656807 baseEnd_656807 := by
    simpa [prefixWord, tailWord_656807, baseEnd_656807] using wordTrace_append hprefix tailTrace_656807
  have hstable : (prefixWord ++ tailWord_656807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656807).length < 2 ^ (prefixWord ++ tailWord_656807).sum := by decide
  have hdescent : baseEnd_656807 < baseStart_656807 := by decide
  rcases family_descends (prefixWord ++ tailWord_656807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656813 : List Nat := [1, 5, 2, 2, 1, 3, 1, 3, 2]
def baseStart_656813 : Nat := 118140960795 + 656813 * 2 ^ 59
def prefixEnd_656813 : Nat := 4983230072969 + 3 ^ 40 * 656813 * 2
def baseEnd_656813 : Nat := 299787350330350177615003

theorem tailTrace_656813 : CollatzResearch.WordTrace tailWord_656813 prefixEnd_656813 299787350330350177615003 := by
  unfold tailWord_656813
  simp only [CollatzResearch.WordTrace]
  refine ⟨23955938169486150574823093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15970625446324100383215395 23955938169486150574823093)
  ·
    refine ⟨2245869203389326616389665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 23955938169486150574823093 2245869203389326616389665)
    ·
      refine ⟨1684401902541994962292249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2245869203389326616389665 1684401902541994962292249)
      ·
        refine ⟨1263301426906496221719187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1684401902541994962292249 1263301426906496221719187)
        ·
          refine ⟨1894952140359744332578781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1263301426906496221719187 1894952140359744332578781)
          ·
            refine ⟨710607052634904124717043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1894952140359744332578781 710607052634904124717043)
            ·
              refine ⟨1065910578952356187075565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710607052634904124717043 1065910578952356187075565)
              ·
                refine ⟨399716467107133570153337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1065910578952356187075565 399716467107133570153337)
                ·
                  refine ⟨299787350330350177615003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399716467107133570153337 299787350330350177615003)
                  ·
                    rfl

theorem cell20_656813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_656813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656813 prefixEnd_656813 := by exact prefixLift 656813
  have htrace : WordTrace (prefixWord ++ tailWord_656813) baseStart_656813 baseEnd_656813 := by
    simpa [prefixWord, tailWord_656813, baseEnd_656813] using wordTrace_append hprefix tailTrace_656813
  have hstable : (prefixWord ++ tailWord_656813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656813).length < 2 ^ (prefixWord ++ tailWord_656813).sum := by decide
  have hdescent : baseEnd_656813 < baseStart_656813 := by decide
  rcases family_descends (prefixWord ++ tailWord_656813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656886 : List Nat := [5, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_656886 : Nat := 118140960795 + 656886 * 2 ^ 59
def prefixEnd_656886 : Nat := 4983230072969 + 3 ^ 40 * 656886 * 2
def baseEnd_656886 : Nat := 299820669519486368181371

theorem tailTrace_656886 : CollatzResearch.WordTrace tailWord_656886 prefixEnd_656886 299820669519486368181371 := by
  unfold tailWord_656886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1497412543638855252639407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15972400465481122694820341 1497412543638855252639407)
  ·
    refine ⟨2246118815458282878959111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1497412543638855252639407 2246118815458282878959111)
    ·
      refine ⟨3369178223187424318438667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2246118815458282878959111 3369178223187424318438667)
      ·
        refine ⟨5053767334781136477658001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3369178223187424318438667 5053767334781136477658001)
        ·
          refine ⟨3790325501085852358243501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5053767334781136477658001 3790325501085852358243501)
          ·
            refine ⟨1421372062907194634341313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3790325501085852358243501 1421372062907194634341313)
            ·
              refine ⟨1066029047180395975755985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1421372062907194634341313 1066029047180395975755985)
              ·
                refine ⟨799521785385296981816989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1066029047180395975755985 799521785385296981816989)
                ·
                  refine ⟨299820669519486368181371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 799521785385296981816989 299820669519486368181371)
                  ·
                    rfl

theorem cell20_656886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_656886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656886 prefixEnd_656886 := by exact prefixLift 656886
  have htrace : WordTrace (prefixWord ++ tailWord_656886) baseStart_656886 baseEnd_656886 := by
    simpa [prefixWord, tailWord_656886, baseEnd_656886] using wordTrace_append hprefix tailTrace_656886
  have hstable : (prefixWord ++ tailWord_656886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656886).length < 2 ^ (prefixWord ++ tailWord_656886).sum := by decide
  have hdescent : baseEnd_656886 < baseStart_656886 := by decide
  rcases family_descends (prefixWord ++ tailWord_656886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656893 : List Nat := [1, 4, 1, 1, 1, 5, 1, 4, 2]
def baseStart_656893 : Nat := 118140960795 + 656893 * 2 ^ 59
def prefixEnd_656893 : Nat := 4983230072969 + 3 ^ 40 * 656893 * 2
def baseEnd_656893 : Nat := 299823864510225454948009

theorem tailTrace_656893 : CollatzResearch.WordTrace tailWord_656893 prefixEnd_656893 299823864510225454948009 := by
  unfold tailWord_656893
  simp only [CollatzResearch.WordTrace]
  refine ⟨23958856009196324237735333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15972570672797549491823555 23958856009196324237735333)
  ·
    refine ⟨4492285501724310794575375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23958856009196324237735333 4492285501724310794575375)
    ·
      refine ⟨6738428252586466191863063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4492285501724310794575375 6738428252586466191863063)
      ·
        refine ⟨10107642378879699287794595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6738428252586466191863063 10107642378879699287794595)
        ·
          refine ⟨15161463568319548931691893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10107642378879699287794595 15161463568319548931691893)
          ·
            refine ⟨1421387209529957712346115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15161463568319548931691893 1421387209529957712346115)
            ·
              refine ⟨2132080814294936568519173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421387209529957712346115 2132080814294936568519173)
              ·
                refine ⟨399765152680300606597345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2132080814294936568519173 399765152680300606597345)
                ·
                  refine ⟨299823864510225454948009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399765152680300606597345 299823864510225454948009)
                  ·
                    rfl

theorem cell20_656893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_656893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656893 prefixEnd_656893 := by exact prefixLift 656893
  have htrace : WordTrace (prefixWord ++ tailWord_656893) baseStart_656893 baseEnd_656893 := by
    simpa [prefixWord, tailWord_656893, baseEnd_656893] using wordTrace_append hprefix tailTrace_656893
  have hstable : (prefixWord ++ tailWord_656893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656893).length < 2 ^ (prefixWord ++ tailWord_656893).sum := by decide
  have hdescent : baseEnd_656893 < baseStart_656893 := by decide
  rcases family_descends (prefixWord ++ tailWord_656893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656952 : List Nat := [2, 1, 2, 1, 4, 3, 2, 1, 4]
def baseStart_656952 : Nat := 118140960795 + 656952 * 2 ^ 59
def prefixEnd_656952 : Nat := 4983230072969 + 3 ^ 40 * 656952 * 2
def baseEnd_656952 : Nat := 299850793717883471981101

theorem tailTrace_656952 : CollatzResearch.WordTrace tailWord_656952 prefixEnd_656952 299850793717883471981101 := by
  unfold tailWord_656952
  simp only [CollatzResearch.WordTrace]
  refine ⟨11980503957991288657066555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15974005277321718209422073 11980503957991288657066555)
  ·
    refine ⟨17970755936986932985599833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11980503957991288657066555 17970755936986932985599833)
    ·
      refine ⟨13478066952740199739199875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17970755936986932985599833 13478066952740199739199875)
      ·
        refine ⟨20217100429110299608799813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13478066952740199739199875 20217100429110299608799813)
        ·
          refine ⟨3790706330458181176649965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20217100429110299608799813 3790706330458181176649965)
          ·
            refine ⟨1421514873921817941243737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3790706330458181176649965 1421514873921817941243737)
            ·
              refine ⟨1066136155441363455932803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1421514873921817941243737 1066136155441363455932803)
              ·
                refine ⟨1599204233162045183899205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066136155441363455932803 1599204233162045183899205)
                ·
                  refine ⟨299850793717883471981101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1599204233162045183899205 299850793717883471981101)
                  ·
                    rfl

theorem cell20_656952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_656952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656952 prefixEnd_656952 := by exact prefixLift 656952
  have htrace : WordTrace (prefixWord ++ tailWord_656952) baseStart_656952 baseEnd_656952 := by
    simpa [prefixWord, tailWord_656952, baseEnd_656952] using wordTrace_append hprefix tailTrace_656952
  have hstable : (prefixWord ++ tailWord_656952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656952).length < 2 ^ (prefixWord ++ tailWord_656952).sum := by decide
  have hdescent : baseEnd_656952 < baseStart_656952 := by decide
  rcases family_descends (prefixWord ++ tailWord_656952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656997 : List Nat := [1, 3, 1, 3, 3, 3, 6]
def baseStart_656997 : Nat := 118140960795 + 656997 * 2 ^ 59
def prefixEnd_656997 : Nat := 4983230072969 + 3 ^ 40 * 656997 * 2
def baseEnd_656997 : Nat := 33319036993784812831213

theorem tailTrace_656997 : CollatzResearch.WordTrace tailWord_656997 prefixEnd_656997 33319036993784812831213 := by
  unfold tailWord_656997
  simp only [CollatzResearch.WordTrace]
  refine ⟨23962649200819549999521245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15975099467213033333014163 23962649200819549999521245)
  ·
    refine ⟨8985993450307331249820467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23962649200819549999521245 8985993450307331249820467)
    ·
      refine ⟨13478990175460996874730701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8985993450307331249820467 13478990175460996874730701)
      ·
        refine ⟨5054621315797873828024013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13478990175460996874730701 5054621315797873828024013)
        ·
          refine ⟨1895482993424202685509005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5054621315797873828024013 1895482993424202685509005)
          ·
            refine ⟨710806122534076007065877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1895482993424202685509005 710806122534076007065877)
            ·
              refine ⟨33319036993784812831213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 710806122534076007065877 33319036993784812831213)
              ·
                rfl

theorem cell20_656997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 6].length) (baseStart_656997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_656997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_656997 prefixEnd_656997 := by exact prefixLift 656997
  have htrace : WordTrace (prefixWord ++ tailWord_656997) baseStart_656997 baseEnd_656997 := by
    simpa [prefixWord, tailWord_656997, baseEnd_656997] using wordTrace_append hprefix tailTrace_656997
  have hstable : (prefixWord ++ tailWord_656997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656997).length < 2 ^ (prefixWord ++ tailWord_656997).sum := by decide
  have hdescent : baseEnd_656997 < baseStart_656997 := by decide
  rcases family_descends (prefixWord ++ tailWord_656997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657004 : List Nat := [2, 2, 1, 1, 3, 1, 1, 6, 3]
def baseStart_657004 : Nat := 118140960795 + 657004 * 2 ^ 59
def prefixEnd_657004 : Nat := 4983230072969 + 3 ^ 40 * 657004 * 2
def baseEnd_657004 : Nat := 299874527934802402247555

theorem tailTrace_657004 : CollatzResearch.WordTrace tailWord_657004 prefixEnd_657004 299874527934802402247555 := by
  unfold tailWord_657004
  simp only [CollatzResearch.WordTrace]
  refine ⟨11981452255897095097513033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15975269674529460130017377 11981452255897095097513033)
  ·
    refine ⟨8986089191922821323134775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11981452255897095097513033 8986089191922821323134775)
    ·
      refine ⟨13479133787884231984702163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8986089191922821323134775 13479133787884231984702163)
      ·
        refine ⟨20218700681826347977053245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13479133787884231984702163 20218700681826347977053245)
        ·
          refine ⟨7582012755684880491394967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20218700681826347977053245 7582012755684880491394967)
          ·
            refine ⟨11373019133527320737092451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7582012755684880491394967 11373019133527320737092451)
            ·
              refine ⟨17059528700290981105638677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11373019133527320737092451 17059528700290981105638677)
              ·
                refine ⟨799665407826139739326813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17059528700290981105638677 799665407826139739326813)
                ·
                  refine ⟨299874527934802402247555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 799665407826139739326813 299874527934802402247555)
                  ·
                    rfl

theorem cell20_657004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_657004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657004 prefixEnd_657004 := by exact prefixLift 657004
  have htrace : WordTrace (prefixWord ++ tailWord_657004) baseStart_657004 baseEnd_657004 := by
    simpa [prefixWord, tailWord_657004, baseEnd_657004] using wordTrace_append hprefix tailTrace_657004
  have hstable : (prefixWord ++ tailWord_657004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657004).length < 2 ^ (prefixWord ++ tailWord_657004).sum := by decide
  have hdescent : baseEnd_657004 < baseStart_657004 := by decide
  rcases family_descends (prefixWord ++ tailWord_657004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657014 : List Nat := [5, 1, 1, 2, 2, 2, 2, 5]
def baseStart_657014 : Nat := 118140960795 + 657014 * 2 ^ 59
def prefixEnd_657014 : Nat := 4983230072969 + 3 ^ 40 * 657014 * 2
def baseEnd_657014 : Nat := 99959697402428937304727

theorem tailTrace_657014 : CollatzResearch.WordTrace tailWord_657014 prefixEnd_657014 99959697402428937304727 := by
  unfold tailWord_657014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1497704327609872618930631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15975512827838641268593397 1497704327609872618930631)
  ·
    refine ⟨2246556491414808928395947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1497704327609872618930631 2246556491414808928395947)
    ·
      refine ⟨3369834737122213392593921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2246556491414808928395947 3369834737122213392593921)
      ·
        refine ⟨2527376052841660044445441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3369834737122213392593921 2527376052841660044445441)
        ·
          refine ⟨1895532039631245033334081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2527376052841660044445441 1895532039631245033334081)
          ·
            refine ⟨1421649029723433775000561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1895532039631245033334081 1421649029723433775000561)
            ·
              refine ⟨1066236772292575331250421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1421649029723433775000561 1066236772292575331250421)
              ·
                refine ⟨99959697402428937304727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1066236772292575331250421 99959697402428937304727)
                ·
                  rfl

theorem cell20_657014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_657014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657014 prefixEnd_657014 := by exact prefixLift 657014
  have htrace : WordTrace (prefixWord ++ tailWord_657014) baseStart_657014 baseEnd_657014 := by
    simpa [prefixWord, tailWord_657014, baseEnd_657014] using wordTrace_append hprefix tailTrace_657014
  have hstable : (prefixWord ++ tailWord_657014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657014).length < 2 ^ (prefixWord ++ tailWord_657014).sum := by decide
  have hdescent : baseEnd_657014 < baseStart_657014 := by decide
  rcases family_descends (prefixWord ++ tailWord_657014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657021 : List Nat := [1, 4, 1, 1, 4, 2, 1, 3, 3]
def baseStart_657021 : Nat := 118140960795 + 657021 * 2 ^ 59
def prefixEnd_657021 : Nat := 4983230072969 + 3 ^ 40 * 657021 * 2
def baseEnd_657021 : Nat := 299882287198025898680819

theorem tailTrace_657021 : CollatzResearch.WordTrace tailWord_657021 prefixEnd_657021 299882287198025898680819 := by
  unfold tailWord_657021
  simp only [CollatzResearch.WordTrace]
  refine ⟨23963524552732602098394917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15975683035155068065596611 23963524552732602098394917)
  ·
    refine ⟨4493160853637362893449047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23963524552732602098394917 4493160853637362893449047)
    ·
      refine ⟨6739741280456044340173571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4493160853637362893449047 6739741280456044340173571)
      ·
        refine ⟨10109611920684066510260357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6739741280456044340173571 10109611920684066510260357)
        ·
          refine ⟨1895552235128262470673817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10109611920684066510260357 1895552235128262470673817)
          ·
            refine ⟨1421664176346196853005363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1895552235128262470673817 1421664176346196853005363)
            ·
              refine ⟨2132496264519295279508045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421664176346196853005363 2132496264519295279508045)
              ·
                refine ⟨799686099194735729815517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2132496264519295279508045 799686099194735729815517)
                ·
                  refine ⟨299882287198025898680819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 799686099194735729815517 299882287198025898680819)
                  ·
                    rfl

theorem cell20_657021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_657021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657021 prefixEnd_657021 := by exact prefixLift 657021
  have htrace : WordTrace (prefixWord ++ tailWord_657021) baseStart_657021 baseEnd_657021 := by
    simpa [prefixWord, tailWord_657021, baseEnd_657021] using wordTrace_append hprefix tailTrace_657021
  have hstable : (prefixWord ++ tailWord_657021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657021).length < 2 ^ (prefixWord ++ tailWord_657021).sum := by decide
  have hdescent : baseEnd_657021 < baseStart_657021 := by decide
  rcases family_descends (prefixWord ++ tailWord_657021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657056 : List Nat := [2, 1, 1, 4, 3, 9]
def baseStart_657056 : Nat := 118140960795 + 657056 * 2 ^ 59
def prefixEnd_657056 : Nat := 4983230072969 + 3 ^ 40 * 657056 * 2
def baseEnd_657056 : Nat := 11107343042656345648667

theorem tailTrace_657056 : CollatzResearch.WordTrace tailWord_657056 prefixEnd_657056 11107343042656345648667 := by
  unfold tailWord_657056
  simp only [CollatzResearch.WordTrace]
  refine ⟨11982400553802901537959511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15976534071737202050612681 11982400553802901537959511)
  ·
    refine ⟨17973600830704352306939267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11982400553802901537959511 17973600830704352306939267)
    ·
      refine ⟨26960401246056528460408901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17973600830704352306939267 26960401246056528460408901)
      ·
        refine ⟨5055075233635599086326669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26960401246056528460408901 5055075233635599086326669)
        ·
          refine ⟨1895653212613349657372501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5055075233635599086326669 1895653212613349657372501)
          ·
            refine ⟨11107343042656345648667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1895653212613349657372501 11107343042656345648667)
            ·
              rfl

theorem cell20_657056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 9].length) (baseStart_657056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657056 prefixEnd_657056 := by exact prefixLift 657056
  have htrace : WordTrace (prefixWord ++ tailWord_657056) baseStart_657056 baseEnd_657056 := by
    simpa [prefixWord, tailWord_657056, baseEnd_657056] using wordTrace_append hprefix tailTrace_657056
  have hstable : (prefixWord ++ tailWord_657056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657056).length < 2 ^ (prefixWord ++ tailWord_657056).sum := by decide
  have hdescent : baseEnd_657056 < baseStart_657056 := by decide
  rcases family_descends (prefixWord ++ tailWord_657056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657058 : List Nat := [3, 3, 1, 4, 1, 2, 2, 2, 2]
def baseStart_657058 : Nat := 118140960795 + 657058 * 2 ^ 59
def prefixEnd_657058 : Nat := 4983230072969 + 3 ^ 40 * 657058 * 2
def baseEnd_657058 : Nat := 299899175006218214447335

theorem tailTrace_657058 : CollatzResearch.WordTrace tailWord_657058 prefixEnd_657058 299899175006218214447335 := by
  unfold tailWord_657058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5991218513399639354372957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15976582702399038278327885 5991218513399639354372957)
  ·
    refine ⟨2246706942524864757889859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5991218513399639354372957 2246706942524864757889859)
    ·
      refine ⟨3370060413787297136834789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2246706942524864757889859 3370060413787297136834789)
      ·
        refine ⟨631886327585118213156523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3370060413787297136834789 631886327585118213156523)
        ·
          refine ⟨947829491377677319734785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 631886327585118213156523 947829491377677319734785)
          ·
            refine ⟨710872118533257989801089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 947829491377677319734785 710872118533257989801089)
            ·
              refine ⟨533154088899943492350817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 710872118533257989801089 533154088899943492350817)
              ·
                refine ⟨399865566674957619263113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 533154088899943492350817 399865566674957619263113)
                ·
                  refine ⟨299899175006218214447335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399865566674957619263113 299899175006218214447335)
                  ·
                    rfl

theorem cell20_657058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_657058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657058 prefixEnd_657058 := by exact prefixLift 657058
  have htrace : WordTrace (prefixWord ++ tailWord_657058) baseStart_657058 baseEnd_657058 := by
    simpa [prefixWord, tailWord_657058, baseEnd_657058] using wordTrace_append hprefix tailTrace_657058
  have hstable : (prefixWord ++ tailWord_657058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657058).length < 2 ^ (prefixWord ++ tailWord_657058).sum := by decide
  have hdescent : baseEnd_657058 < baseStart_657058 := by decide
  rcases family_descends (prefixWord ++ tailWord_657058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657087 : List Nat := [1, 1, 2, 2, 2, 3, 3, 2, 4]
def baseStart_657087 : Nat := 118140960795 + 657087 * 2 ^ 59
def prefixEnd_657087 : Nat := 4983230072969 + 3 ^ 40 * 657087 * 2
def baseEnd_657087 : Nat := 299912411396423002480549

theorem tailTrace_657087 : CollatzResearch.WordTrace tailWord_657087 prefixEnd_657087 299912411396423002480549 := by
  unfold tailWord_657087
  simp only [CollatzResearch.WordTrace]
  refine ⟨23965931770493495370297515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15977287846995663580198343 23965931770493495370297515)
  ·
    refine ⟨35948897655740243055446273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23965931770493495370297515 35948897655740243055446273)
    ·
      refine ⟨26961673241805182291584705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35948897655740243055446273 26961673241805182291584705)
      ·
        refine ⟨20221254931353886718688529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26961673241805182291584705 20221254931353886718688529)
        ·
          refine ⟨15165941198515415039016397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20221254931353886718688529 15165941198515415039016397)
          ·
            refine ⟨5687227949443280639631149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15165941198515415039016397 5687227949443280639631149)
            ·
              refine ⟨2132710481041230239861681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5687227949443280639631149 2132710481041230239861681)
              ·
                refine ⟨1599532860780922679896261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2132710481041230239861681 1599532860780922679896261)
                ·
                  refine ⟨299912411396423002480549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1599532860780922679896261 299912411396423002480549)
                  ·
                    rfl

theorem cell20_657087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 4].length) (baseStart_657087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657087 prefixEnd_657087 := by exact prefixLift 657087
  have htrace : WordTrace (prefixWord ++ tailWord_657087) baseStart_657087 baseEnd_657087 := by
    simpa [prefixWord, tailWord_657087, baseEnd_657087] using wordTrace_append hprefix tailTrace_657087
  have hstable : (prefixWord ++ tailWord_657087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657087).length < 2 ^ (prefixWord ++ tailWord_657087).sum := by decide
  have hdescent : baseEnd_657087 < baseStart_657087 := by decide
  rcases family_descends (prefixWord ++ tailWord_657087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657100 : List Nat := [2, 2, 1, 5, 2, 1, 2, 3, 2]
def baseStart_657100 : Nat := 118140960795 + 657100 * 2 ^ 59
def prefixEnd_657100 : Nat := 4983230072969 + 3 ^ 40 * 657100 * 2
def baseEnd_657100 : Nat := 299918344950652735047163

theorem tailTrace_657100 : CollatzResearch.WordTrace tailWord_657100 prefixEnd_657100 299918344950652735047163 := by
  unfold tailWord_657100
  simp only [CollatzResearch.WordTrace]
  refine ⟨11983202959723199295260377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15977603946297599060347169 11983202959723199295260377)
  ·
    refine ⟨8987402219792399471445283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11983202959723199295260377 8987402219792399471445283)
    ·
      refine ⟨13481103329688599207167925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8987402219792399471445283 13481103329688599207167925)
      ·
        refine ⟨1263853437158306175671993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13481103329688599207167925 1263853437158306175671993)
        ·
          refine ⟨947890077868729631753995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1263853437158306175671993 947890077868729631753995)
          ·
            refine ⟨1421835116803094447630993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 947890077868729631753995 1421835116803094447630993)
            ·
              refine ⟨1066376337602320835723245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1421835116803094447630993 1066376337602320835723245)
              ·
                refine ⟨399891126600870313396217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1066376337602320835723245 399891126600870313396217)
                ·
                  refine ⟨299918344950652735047163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 399891126600870313396217 299918344950652735047163)
                  ·
                    rfl

theorem cell20_657100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_657100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657100 prefixEnd_657100 := by exact prefixLift 657100
  have htrace : WordTrace (prefixWord ++ tailWord_657100) baseStart_657100 baseEnd_657100 := by
    simpa [prefixWord, tailWord_657100, baseEnd_657100] using wordTrace_append hprefix tailTrace_657100
  have hstable : (prefixWord ++ tailWord_657100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657100).length < 2 ^ (prefixWord ++ tailWord_657100).sum := by decide
  have hdescent : baseEnd_657100 < baseStart_657100 := by decide
  rcases family_descends (prefixWord ++ tailWord_657100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657110 : List Nat := [5, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_657110 : Nat := 118140960795 + 657110 * 2 ^ 59
def prefixEnd_657110 : Nat := 4983230072969 + 3 ^ 40 * 657110 * 2
def baseEnd_657110 : Nat := 299922909223137144713789

theorem tailTrace_657110 : CollatzResearch.WordTrace tailWord_657110 prefixEnd_657110 299922909223137144713789 := by
  unfold tailWord_657110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1497923165588135643649049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15977847099606780198923189 1497923165588135643649049)
  ·
    refine ⟨1123442374191101732736787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1497923165588135643649049 1123442374191101732736787)
    ·
      refine ⟨1685163561286652599105181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1123442374191101732736787 1685163561286652599105181)
      ·
        refine ⟨631936335482494724664443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1685163561286652599105181 631936335482494724664443)
        ·
          refine ⟨947904503223742086996665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 631936335482494724664443 947904503223742086996665)
          ·
            refine ⟨710928377417806565247499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 947904503223742086996665 710928377417806565247499)
            ·
              refine ⟨1066392566126709847871249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710928377417806565247499 1066392566126709847871249)
              ·
                refine ⟨799794424595032385903437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1066392566126709847871249 799794424595032385903437)
                ·
                  refine ⟨299922909223137144713789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 799794424595032385903437 299922909223137144713789)
                  ·
                    rfl

theorem cell20_657110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_657110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657110 prefixEnd_657110 := by exact prefixLift 657110
  have htrace : WordTrace (prefixWord ++ tailWord_657110) baseStart_657110 baseEnd_657110 := by
    simpa [prefixWord, tailWord_657110, baseEnd_657110] using wordTrace_append hprefix tailTrace_657110
  have hstable : (prefixWord ++ tailWord_657110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657110).length < 2 ^ (prefixWord ++ tailWord_657110).sum := by decide
  have hdescent : baseEnd_657110 < baseStart_657110 := by decide
  rcases family_descends (prefixWord ++ tailWord_657110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657135 : List Nat := [1, 1, 2, 1, 5, 1, 5, 1, 3]
def baseStart_657135 : Nat := 118140960795 + 657135 * 2 ^ 59
def prefixEnd_657135 : Nat := 4983230072969 + 3 ^ 40 * 657135 * 2
def baseEnd_657135 : Nat := 299934319904348168880353

theorem tailTrace_657135 : CollatzResearch.WordTrace tailWord_657135 prefixEnd_657135 299934319904348168880353 := by
  unfold tailWord_657135
  simp only [CollatzResearch.WordTrace]
  refine ⟨23967682474319599568044859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15978454982879733045363239 23967682474319599568044859)
  ·
    refine ⟨35951523711479399352067289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23967682474319599568044859 35951523711479399352067289)
    ·
      refine ⟨26963642783609549514050467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35951523711479399352067289 26963642783609549514050467)
      ·
        refine ⟨40445464175414324271075701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26963642783609549514050467 40445464175414324271075701)
        ·
          refine ⟨3791762266445092900413347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40445464175414324271075701 3791762266445092900413347)
          ·
            refine ⟨5687643399667639350620021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3791762266445092900413347 5687643399667639350620021)
            ·
              refine ⟨533216568718841189120627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5687643399667639350620021 533216568718841189120627)
              ·
                refine ⟨799824853078261783680941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 533216568718841189120627 799824853078261783680941)
                ·
                  refine ⟨299934319904348168880353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 799824853078261783680941 299934319904348168880353)
                  ·
                    rfl

theorem cell20_657135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 3].length) (baseStart_657135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657135 prefixEnd_657135 := by exact prefixLift 657135
  have htrace : WordTrace (prefixWord ++ tailWord_657135) baseStart_657135 baseEnd_657135 := by
    simpa [prefixWord, tailWord_657135, baseEnd_657135] using wordTrace_append hprefix tailTrace_657135
  have hstable : (prefixWord ++ tailWord_657135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657135).length < 2 ^ (prefixWord ++ tailWord_657135).sum := by decide
  have hdescent : baseEnd_657135 < baseStart_657135 := by decide
  rcases family_descends (prefixWord ++ tailWord_657135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657142 : List Nat := [5, 1, 1, 1, 1, 3, 2, 2, 4]
def baseStart_657142 : Nat := 118140960795 + 657142 * 2 ^ 59
def prefixEnd_657142 : Nat := 4983230072969 + 3 ^ 40 * 657142 * 2
def baseEnd_657142 : Nat := 299937514895087255646991

theorem tailTrace_657142 : CollatzResearch.WordTrace tailWord_657142 prefixEnd_657142 299937514895087255646991 := by
  unfold tailWord_657142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1497996111580889985221855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15978625190196159842366453 1497996111580889985221855)
  ·
    refine ⟨2246994167371334977832783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1497996111580889985221855 2246994167371334977832783)
    ·
      refine ⟨3370491251057002466749175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2246994167371334977832783 3370491251057002466749175)
      ·
        refine ⟨5055736876585503700123763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3370491251057002466749175 5055736876585503700123763)
        ·
          refine ⟨7583605314878255550185645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5055736876585503700123763 7583605314878255550185645)
          ·
            refine ⟨2843851993079345831319617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7583605314878255550185645 2843851993079345831319617)
            ·
              refine ⟨2132888994809509373489713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2843851993079345831319617 2132888994809509373489713)
              ·
                refine ⟨1599666746107132030117285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2132888994809509373489713 1599666746107132030117285)
                ·
                  refine ⟨299937514895087255646991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1599666746107132030117285 299937514895087255646991)
                  ·
                    rfl

theorem cell20_657142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_657142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657142 prefixEnd_657142 := by exact prefixLift 657142
  have htrace : WordTrace (prefixWord ++ tailWord_657142) baseStart_657142 baseEnd_657142 := by
    simpa [prefixWord, tailWord_657142, baseEnd_657142] using wordTrace_append hprefix tailTrace_657142
  have hstable : (prefixWord ++ tailWord_657142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657142).length < 2 ^ (prefixWord ++ tailWord_657142).sum := by decide
  have hdescent : baseEnd_657142 < baseStart_657142 := by decide
  rcases family_descends (prefixWord ++ tailWord_657142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657156 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 5]
def baseStart_657156 : Nat := 118140960795 + 657156 * 2 ^ 59
def prefixEnd_657156 : Nat := 4983230072969 + 3 ^ 40 * 657156 * 2
def baseEnd_657156 : Nat := 299943904876565429180267

theorem tailTrace_657156 : CollatzResearch.WordTrace tailWord_657156 prefixEnd_657156 299943904876565429180267 := by
  unfold tailWord_657156
  simp only [CollatzResearch.WordTrace]
  refine ⟨11984224203621760077279661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15978965604829013436372881 11984224203621760077279661)
  ·
    refine ⟨4494084076358160028979873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11984224203621760077279661 4494084076358160028979873)
    ·
      refine ⟨3370563057268620021734905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4494084076358160028979873 3370563057268620021734905)
      ·
        refine ⟨2527922292951465016301179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3370563057268620021734905 2527922292951465016301179)
        ·
          refine ⟨3791883439427197524451769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2527922292951465016301179 3791883439427197524451769)
          ·
            refine ⟨2843912579570398143338827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3791883439427197524451769 2843912579570398143338827)
            ·
              refine ⟨4265868869355597215008241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2843912579570398143338827 4265868869355597215008241)
              ·
                refine ⟨3199401652016697911256181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4265868869355597215008241 3199401652016697911256181)
                ·
                  refine ⟨299943904876565429180267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3199401652016697911256181 299943904876565429180267)
                  ·
                    rfl

theorem cell20_657156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_657156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657156 prefixEnd_657156 := by exact prefixLift 657156
  have htrace : WordTrace (prefixWord ++ tailWord_657156) baseStart_657156 baseEnd_657156 := by
    simpa [prefixWord, tailWord_657156, baseEnd_657156] using wordTrace_append hprefix tailTrace_657156
  have hstable : (prefixWord ++ tailWord_657156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657156).length < 2 ^ (prefixWord ++ tailWord_657156).sum := by decide
  have hdescent : baseEnd_657156 < baseStart_657156 := by decide
  rcases family_descends (prefixWord ++ tailWord_657156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657158 : List Nat := [6, 2, 2, 1, 2, 1, 6]
def baseStart_657158 : Nat := 118140960795 + 657158 * 2 ^ 59
def prefixEnd_657158 : Nat := 4983230072969 + 3 ^ 40 * 657158 * 2
def baseEnd_657158 : Nat := 33327201970118034568177

theorem tailTrace_657158 : CollatzResearch.WordTrace tailWord_657158 prefixEnd_657158 33327201970118034568177 := by
  unfold tailWord_657158
  simp only [CollatzResearch.WordTrace]
  refine ⟨749016292288633578004129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15979014235490849664088085 749016292288633578004129)
  ·
    refine ⟨561762219216475183503097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 749016292288633578004129 561762219216475183503097)
    ·
      refine ⟨421321664412356387627323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 561762219216475183503097 421321664412356387627323)
      ·
        refine ⟨631982496618534581440985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421321664412356387627323 631982496618534581440985)
        ·
          refine ⟨473986872463900936080739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 631982496618534581440985 473986872463900936080739)
          ·
            refine ⟨710980308695851404121109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473986872463900936080739 710980308695851404121109)
            ·
              refine ⟨33327201970118034568177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 710980308695851404121109 33327201970118034568177)
              ·
                rfl

theorem cell20_657158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 6].length) (baseStart_657158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657158 prefixEnd_657158 := by exact prefixLift 657158
  have htrace : WordTrace (prefixWord ++ tailWord_657158) baseStart_657158 baseEnd_657158 := by
    simpa [prefixWord, tailWord_657158, baseEnd_657158] using wordTrace_append hprefix tailTrace_657158
  have hstable : (prefixWord ++ tailWord_657158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657158).length < 2 ^ (prefixWord ++ tailWord_657158).sum := by decide
  have hdescent : baseEnd_657158 < baseStart_657158 := by decide
  rcases family_descends (prefixWord ++ tailWord_657158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657172 : List Nat := [2, 4, 4, 1, 2, 1, 1, 1, 4]
def baseStart_657172 : Nat := 118140960795 + 657172 * 2 ^ 59
def prefixEnd_657172 : Nat := 4983230072969 + 3 ^ 40 * 657172 * 2
def baseEnd_657172 : Nat := 299951207712540484646869

theorem tailTrace_657172 : CollatzResearch.WordTrace tailWord_657172 prefixEnd_657172 299951207712540484646869 := by
  unfold tailWord_657172
  simp only [CollatzResearch.WordTrace]
  refine ⟨11984515987592777443570885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15979354650123703258094513 11984515987592777443570885)
  ·
    refine ⟨2247096747673645770669541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11984515987592777443570885 2247096747673645770669541)
    ·
      refine ⟨421330640188808582000539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2247096747673645770669541 421330640188808582000539)
      ·
        refine ⟨631995960283212873000809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421330640188808582000539 631995960283212873000809)
        ·
          refine ⟨473996970212409654750607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 631995960283212873000809 473996970212409654750607)
          ·
            refine ⟨710995455318614482125911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473996970212409654750607 710995455318614482125911)
            ·
              refine ⟨1066493182977921723188867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710995455318614482125911 1066493182977921723188867)
              ·
                refine ⟨1599739774466882584783301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066493182977921723188867 1599739774466882584783301)
                ·
                  refine ⟨299951207712540484646869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1599739774466882584783301 299951207712540484646869)
                  ·
                    rfl

theorem cell20_657172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_657172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657172 prefixEnd_657172 := by exact prefixLift 657172
  have htrace : WordTrace (prefixWord ++ tailWord_657172) baseStart_657172 baseEnd_657172 := by
    simpa [prefixWord, tailWord_657172, baseEnd_657172] using wordTrace_append hprefix tailTrace_657172
  have hstable : (prefixWord ++ tailWord_657172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657172).length < 2 ^ (prefixWord ++ tailWord_657172).sum := by decide
  have hdescent : baseEnd_657172 < baseStart_657172 := by decide
  rcases family_descends (prefixWord ++ tailWord_657172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657208 : List Nat := [2, 1, 2, 1, 3, 3, 2, 6]
def baseStart_657208 : Nat := 118140960795 + 657208 * 2 ^ 59
def prefixEnd_657208 : Nat := 4983230072969 + 3 ^ 40 * 657208 * 2
def baseEnd_657208 : Nat := 99989213031161453148907

theorem tailTrace_657208 : CollatzResearch.WordTrace tailWord_657208 prefixEnd_657208 99989213031161453148907 := by
  unfold tailWord_657208
  simp only [CollatzResearch.WordTrace]
  refine ⟨11985172501527566517726139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15980230002036755356968185 11985172501527566517726139)
  ·
    refine ⟨17977758752291349776589209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11985172501527566517726139 17977758752291349776589209)
    ·
      refine ⟨13483319064218512332441907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17977758752291349776589209 13483319064218512332441907)
      ·
        refine ⟨20224978596327768498662861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13483319064218512332441907 20224978596327768498662861)
        ·
          refine ⟨7584366973622913186998573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20224978596327768498662861 7584366973622913186998573)
          ·
            refine ⟨2844137615108592445124465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7584366973622913186998573 2844137615108592445124465)
            ·
              refine ⟨2133103211331444333843349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2844137615108592445124465 2133103211331444333843349)
              ·
                refine ⟨99989213031161453148907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2133103211331444333843349 99989213031161453148907)
                ·
                  rfl

theorem cell20_657208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_657208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657208 prefixEnd_657208 := by exact prefixLift 657208
  have htrace : WordTrace (prefixWord ++ tailWord_657208) baseStart_657208 baseEnd_657208 := by
    simpa [prefixWord, tailWord_657208, baseEnd_657208] using wordTrace_append hprefix tailTrace_657208
  have hstable : (prefixWord ++ tailWord_657208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657208).length < 2 ^ (prefixWord ++ tailWord_657208).sum := by decide
  have hdescent : baseEnd_657208 < baseStart_657208 := by decide
  rcases family_descends (prefixWord ++ tailWord_657208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657253 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 7]
def baseStart_657253 : Nat := 118140960795 + 657253 * 2 ^ 59
def prefixEnd_657253 : Nat := 4983230072969 + 3 ^ 40 * 657253 * 2
def baseEnd_657253 : Nat := 299988178319664202946537

theorem tailTrace_657253 : CollatzResearch.WordTrace tailWord_657253 prefixEnd_657253 299988178319664202946537 := by
  unfold tailWord_657253
  simp only [CollatzResearch.WordTrace]
  refine ⟨23971986287892105720840413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15981324191928070480560275 23971986287892105720840413)
  ·
    refine ⟨8989494857959539645315155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23971986287892105720840413 8989494857959539645315155)
    ·
      refine ⟨13484242286939309467972733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8989494857959539645315155 13484242286939309467972733)
      ·
        refine ⟨5056590857602241050489775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13484242286939309467972733 5056590857602241050489775)
        ·
          refine ⟨7584886286403361575734663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5056590857602241050489775 7584886286403361575734663)
          ·
            refine ⟨11377329429605042363601995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7584886286403361575734663 11377329429605042363601995)
            ·
              refine ⟨17065994144407563545402993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11377329429605042363601995 17065994144407563545402993)
              ·
                refine ⟨12799495608305672659052245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17065994144407563545402993 12799495608305672659052245)
                ·
                  refine ⟨299988178319664202946537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12799495608305672659052245 299988178319664202946537)
                  ·
                    rfl

theorem cell20_657253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_657253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657253 prefixEnd_657253 := by exact prefixLift 657253
  have htrace : WordTrace (prefixWord ++ tailWord_657253) baseStart_657253 baseEnd_657253 := by
    simpa [prefixWord, tailWord_657253, baseEnd_657253] using wordTrace_append hprefix tailTrace_657253
  have hstable : (prefixWord ++ tailWord_657253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657253).length < 2 ^ (prefixWord ++ tailWord_657253).sum := by decide
  have hdescent : baseEnd_657253 < baseStart_657253 := by decide
  rcases family_descends (prefixWord ++ tailWord_657253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657398 : List Nat := [5, 1, 1, 1, 12]
def baseStart_657398 : Nat := 118140960795 + 657398 * 2 ^ 59
def prefixEnd_657398 : Nat := 4983230072969 + 3 ^ 40 * 657398 * 2
def baseEnd_657398 : Nat := 3704374818156643742131

theorem tailTrace_657398 : CollatzResearch.WordTrace tailWord_657398 prefixEnd_657398 3704374818156643742131 := by
  unfold tailWord_657398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1498579679522924717804303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15984849914911196989912565 1498579679522924717804303)
  ·
    refine ⟨2247869519284387076706455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1498579679522924717804303 2247869519284387076706455)
    ·
      refine ⟨3371804278926580615059683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2247869519284387076706455 3371804278926580615059683)
      ·
        refine ⟨5057706418389870922589525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3371804278926580615059683 5057706418389870922589525)
        ·
          refine ⟨3704374818156643742131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5057706418389870922589525 3704374818156643742131)
          ·
            rfl

theorem cell20_657398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 12].length) (baseStart_657398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657398 prefixEnd_657398 := by exact prefixLift 657398
  have htrace : WordTrace (prefixWord ++ tailWord_657398) baseStart_657398 baseEnd_657398 := by
    simpa [prefixWord, tailWord_657398, baseEnd_657398] using wordTrace_append hprefix tailTrace_657398
  have hstable : (prefixWord ++ tailWord_657398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657398).length < 2 ^ (prefixWord ++ tailWord_657398).sum := by decide
  have hdescent : baseEnd_657398 < baseStart_657398 := by decide
  rcases family_descends (prefixWord ++ tailWord_657398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657405 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 5]
def baseStart_657405 : Nat := 118140960795 + 657405 * 2 ^ 59
def prefixEnd_657405 : Nat := 4983230072969 + 3 ^ 40 * 657405 * 2
def baseEnd_657405 : Nat := 300057555261427229879249

theorem tailTrace_657405 : CollatzResearch.WordTrace tailWord_657405 prefixEnd_657405 300057555261427229879249 := by
  unfold tailWord_657405
  simp only [CollatzResearch.WordTrace]
  refine ⟨23977530183341435680373669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15985020122227623786915779 23977530183341435680373669)
  ·
    refine ⟨4495786909376519190070063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23977530183341435680373669 4495786909376519190070063)
    ·
      refine ⟨6743680364064778785105095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4495786909376519190070063 6743680364064778785105095)
      ·
        refine ⟨10115520546097168177657643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6743680364064778785105095 10115520546097168177657643)
        ·
          refine ⟨15173280819145752266486465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10115520546097168177657643 15173280819145752266486465)
          ·
            refine ⟨11379960614359314199864849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15173280819145752266486465 11379960614359314199864849)
            ·
              refine ⟨8534970460769485649898637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11379960614359314199864849 8534970460769485649898637)
              ·
                refine ⟨3200613922788557118711989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8534970460769485649898637 3200613922788557118711989)
                ·
                  refine ⟨300057555261427229879249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3200613922788557118711989 300057555261427229879249)
                  ·
                    rfl

theorem cell20_657405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_657405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657405 prefixEnd_657405 := by exact prefixLift 657405
  have htrace : WordTrace (prefixWord ++ tailWord_657405) baseStart_657405 baseEnd_657405 := by
    simpa [prefixWord, tailWord_657405, baseEnd_657405] using wordTrace_append hprefix tailTrace_657405
  have hstable : (prefixWord ++ tailWord_657405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657405).length < 2 ^ (prefixWord ++ tailWord_657405).sum := by decide
  have hdescent : baseEnd_657405 < baseStart_657405 := by decide
  rcases family_descends (prefixWord ++ tailWord_657405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657415 : List Nat := [1, 1, 4, 3, 1, 4, 1, 5]
def baseStart_657415 : Nat := 118140960795 + 657415 * 2 ^ 59
def prefixEnd_657415 : Nat := 4983230072969 + 3 ^ 40 * 657415 * 2
def baseEnd_657415 : Nat := 100020706511303879848625

theorem tailTrace_657415 : CollatzResearch.WordTrace tailWord_657415 prefixEnd_657415 100020706511303879848625 := by
  unfold tailWord_657415
  simp only [CollatzResearch.WordTrace]
  refine ⟨23977894913305207388237699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15985263275536804925491799 23977894913305207388237699)
  ·
    refine ⟨35966842369957811082356549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23977894913305207388237699 35966842369957811082356549)
    ·
      refine ⟨6743782944367089577941853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35966842369957811082356549 6743782944367089577941853)
      ·
        refine ⟨2528918604137658591728195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6743782944367089577941853 2528918604137658591728195)
        ·
          refine ⟨3793377906206487887592293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2528918604137658591728195 3793377906206487887592293)
          ·
            refine ⟨711258357413716478923555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3793377906206487887592293 711258357413716478923555)
            ·
              refine ⟨1066887536120574718385333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 711258357413716478923555 1066887536120574718385333)
              ·
                refine ⟨100020706511303879848625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1066887536120574718385333 100020706511303879848625)
                ·
                  rfl

theorem cell20_657415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 5].length) (baseStart_657415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657415 prefixEnd_657415 := by exact prefixLift 657415
  have htrace : WordTrace (prefixWord ++ tailWord_657415) baseStart_657415 baseEnd_657415 := by
    simpa [prefixWord, tailWord_657415, baseEnd_657415] using wordTrace_append hprefix tailTrace_657415
  have hstable : (prefixWord ++ tailWord_657415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657415).length < 2 ^ (prefixWord ++ tailWord_657415).sum := by decide
  have hdescent : baseEnd_657415 < baseStart_657415 := by decide
  rcases family_descends (prefixWord ++ tailWord_657415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657422 : List Nat := [4, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_657422 : Nat := 118140960795 + 657422 * 2 ^ 59
def prefixEnd_657422 : Nat := 4983230072969 + 3 ^ 40 * 657422 * 2
def baseEnd_657422 : Nat := 300065314524650726312513

theorem tailTrace_657422 : CollatzResearch.WordTrace tailWord_657422 prefixEnd_657422 300065314524650726312513 := by
  unfold tailWord_657422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2997268778034980947967815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15985433482853231722495013 2997268778034980947967815)
  ·
    refine ⟨4495903167052471421951723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2997268778034980947967815 4495903167052471421951723)
    ·
      refine ⟨6743854750578707132927585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4495903167052471421951723 6743854750578707132927585)
      ·
        refine ⟨5057891062934030349695689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6743854750578707132927585 5057891062934030349695689)
        ·
          refine ⟨3793418297200522762271767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5057891062934030349695689 3793418297200522762271767)
          ·
            refine ⟨5690127445800784143407651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3793418297200522762271767 5690127445800784143407651)
            ·
              refine ⟨8535191168701176215111477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5690127445800784143407651 8535191168701176215111477)
              ·
                refine ⟨800174172065735270166701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8535191168701176215111477 800174172065735270166701)
                ·
                  refine ⟨300065314524650726312513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 800174172065735270166701 300065314524650726312513)
                  ·
                    rfl

theorem cell20_657422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_657422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657422 prefixEnd_657422 := by exact prefixLift 657422
  have htrace : WordTrace (prefixWord ++ tailWord_657422) baseStart_657422 baseEnd_657422 := by
    simpa [prefixWord, tailWord_657422, baseEnd_657422] using wordTrace_append hprefix tailTrace_657422
  have hstable : (prefixWord ++ tailWord_657422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657422).length < 2 ^ (prefixWord ++ tailWord_657422).sum := by decide
  have hdescent : baseEnd_657422 < baseStart_657422 := by decide
  rcases family_descends (prefixWord ++ tailWord_657422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657443 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 5]
def baseStart_657443 : Nat := 118140960795 + 657443 * 2 ^ 59
def prefixEnd_657443 : Nat := 4983230072969 + 3 ^ 40 * 657443 * 2
def baseEnd_657443 : Nat := 300074899496867986612427

theorem tailTrace_657443 : CollatzResearch.WordTrace tailWord_657443 prefixEnd_657443 300074899496867986612427 := by
  unfold tailWord_657443
  simp only [CollatzResearch.WordTrace]
  refine ⟨23978916157203768170256983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15985944104802512113504655 23978916157203768170256983)
  ·
    refine ⟨35968374235805652255385475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23978916157203768170256983 35968374235805652255385475)
    ·
      refine ⟨53952561353708478383078213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35968374235805652255385475 53952561353708478383078213)
      ·
        refine ⟨10116105253820339696827165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53952561353708478383078213 10116105253820339696827165)
        ·
          refine ⟨3793539470182627386310187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10116105253820339696827165 3793539470182627386310187)
          ·
            refine ⟨5690309205273941079465281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3793539470182627386310187 5690309205273941079465281)
            ·
              refine ⟨4267731903955455809598961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5690309205273941079465281 4267731903955455809598961)
              ·
                refine ⟨3200798927966591857199221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4267731903955455809598961 3200798927966591857199221)
                ·
                  refine ⟨300074899496867986612427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3200798927966591857199221 300074899496867986612427)
                  ·
                    rfl

theorem cell20_657443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_657443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657443 prefixEnd_657443 := by exact prefixLift 657443
  have htrace : WordTrace (prefixWord ++ tailWord_657443) baseStart_657443 baseEnd_657443 := by
    simpa [prefixWord, tailWord_657443, baseEnd_657443] using wordTrace_append hprefix tailTrace_657443
  have hstable : (prefixWord ++ tailWord_657443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657443).length < 2 ^ (prefixWord ++ tailWord_657443).sum := by decide
  have hdescent : baseEnd_657443 < baseStart_657443 := by decide
  rcases family_descends (prefixWord ++ tailWord_657443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657519 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 5]
def baseStart_657519 : Nat := 118140960795 + 657519 * 2 ^ 59
def prefixEnd_657519 : Nat := 4983230072969 + 3 ^ 40 * 657519 * 2
def baseEnd_657519 : Nat := 300109587967749500078783

theorem tailTrace_657519 : CollatzResearch.WordTrace tailWord_657519 prefixEnd_657519 300109587967749500078783 := by
  unfold tailWord_657519
  simp only [CollatzResearch.WordTrace]
  refine ⟨23981688104928433150023611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15987792069952288766682407 23981688104928433150023611)
  ·
    refine ⟨35972532157392649725035417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23981688104928433150023611 35972532157392649725035417)
    ·
      refine ⟨26979399118044487293776563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35972532157392649725035417 26979399118044487293776563)
      ·
        refine ⟨40469098677066730940664845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26979399118044487293776563 40469098677066730940664845)
        ·
          refine ⟨15175912003900024102749317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40469098677066730940664845 15175912003900024102749317)
          ·
            refine ⟨2845483500731254519265497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15175912003900024102749317 2845483500731254519265497)
            ·
              refine ⟨2134112625548440889449123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2845483500731254519265497 2134112625548440889449123)
              ·
                refine ⟨3201168938322661334173685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2134112625548440889449123 3201168938322661334173685)
                ·
                  refine ⟨300109587967749500078783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3201168938322661334173685 300109587967749500078783)
                  ·
                    rfl

theorem cell20_657519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 5].length) (baseStart_657519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657519 prefixEnd_657519 := by exact prefixLift 657519
  have htrace : WordTrace (prefixWord ++ tailWord_657519) baseStart_657519 baseEnd_657519 := by
    simpa [prefixWord, tailWord_657519, baseEnd_657519] using wordTrace_append hprefix tailTrace_657519
  have hstable : (prefixWord ++ tailWord_657519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657519).length < 2 ^ (prefixWord ++ tailWord_657519).sum := by decide
  have hdescent : baseEnd_657519 < baseStart_657519 := by decide
  rcases family_descends (prefixWord ++ tailWord_657519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657522 : List Nat := [3, 2, 1, 2, 2, 4, 1, 1, 4]
def baseStart_657522 : Nat := 118140960795 + 657522 * 2 ^ 59
def prefixEnd_657522 : Nat := 4983230072969 + 3 ^ 40 * 657522 * 2
def baseEnd_657522 : Nat := 300110957249494822978771

theorem tailTrace_657522 : CollatzResearch.WordTrace tailWord_657522 prefixEnd_657522 300110957249494822978771 := by
  unfold tailWord_657522
  simp only [CollatzResearch.WordTrace]
  refine ⟨5995449380979391165595705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15987865015945043108255213 5995449380979391165595705)
  ·
    refine ⟨4496587035734543374196779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5995449380979391165595705 4496587035734543374196779)
    ·
      refine ⟨6744880553601815061295169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4496587035734543374196779 6744880553601815061295169)
      ·
        refine ⟨5058660415201361295971377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6744880553601815061295169 5058660415201361295971377)
        ·
          refine ⟨3793995311401020971978533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5058660415201361295971377 3793995311401020971978533)
          ·
            refine ⟨711374120887691432245975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3793995311401020971978533 711374120887691432245975)
            ·
              refine ⟨1067061181331537148368963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 711374120887691432245975 1067061181331537148368963)
              ·
                refine ⟨1600591771997305722553445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1067061181331537148368963 1600591771997305722553445)
                ·
                  refine ⟨300110957249494822978771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1600591771997305722553445 300110957249494822978771)
                  ·
                    rfl

theorem cell20_657522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_657522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657522 prefixEnd_657522 := by exact prefixLift 657522
  have htrace : WordTrace (prefixWord ++ tailWord_657522) baseStart_657522 baseEnd_657522 := by
    simpa [prefixWord, tailWord_657522, baseEnd_657522] using wordTrace_append hprefix tailTrace_657522
  have hstable : (prefixWord ++ tailWord_657522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657522).length < 2 ^ (prefixWord ++ tailWord_657522).sum := by decide
  have hdescent : baseEnd_657522 < baseStart_657522 := by decide
  rcases family_descends (prefixWord ++ tailWord_657522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657595 : List Nat := [1, 1, 1, 1, 1, 2, 5, 5, 3]
def baseStart_657595 : Nat := 118140960795 + 657595 * 2 ^ 59
def prefixEnd_657595 : Nat := 4983230072969 + 3 ^ 40 * 657595 * 2
def baseEnd_657595 : Nat := 300144276438631013545139

theorem tailTrace_657595 : CollatzResearch.WordTrace tailWord_657595 prefixEnd_657595 300144276438631013545139 := by
  unfold tailWord_657595
  simp only [CollatzResearch.WordTrace]
  refine ⟨23984460052653098129790239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15989640035102065419860159 23984460052653098129790239)
  ·
    refine ⟨35976690078979647194685359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23984460052653098129790239 35976690078979647194685359)
    ·
      refine ⟨53965035118469470792028039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35976690078979647194685359 53965035118469470792028039)
      ·
        refine ⟨80947552677704206188042059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53965035118469470792028039 80947552677704206188042059)
        ·
          refine ⟨121421329016556309282063089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80947552677704206188042059 121421329016556309282063089)
          ·
            refine ⟨91065996762417231961547317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121421329016556309282063089 91065996762417231961547317)
            ·
              refine ⟨8537437196476615496395061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91065996762417231961547317 8537437196476615496395061)
              ·
                refine ⟨800384737169682702787037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8537437196476615496395061 800384737169682702787037)
                ·
                  refine ⟨300144276438631013545139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 800384737169682702787037 300144276438631013545139)
                  ·
                    rfl

theorem cell20_657595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 3].length) (baseStart_657595 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657595 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657595 prefixEnd_657595 := by exact prefixLift 657595
  have htrace : WordTrace (prefixWord ++ tailWord_657595) baseStart_657595 baseEnd_657595 := by
    simpa [prefixWord, tailWord_657595, baseEnd_657595] using wordTrace_append hprefix tailTrace_657595
  have hstable : (prefixWord ++ tailWord_657595).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657595).length < 2 ^ (prefixWord ++ tailWord_657595).sum := by decide
  have hdescent : baseEnd_657595 < baseStart_657595 := by decide
  rcases family_descends (prefixWord ++ tailWord_657595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657598 : List Nat := [4, 2, 1, 1, 4, 1, 1, 2, 4]
def baseStart_657598 : Nat := 118140960795 + 657598 * 2 ^ 59
def prefixEnd_657598 : Nat := 4983230072969 + 3 ^ 40 * 657598 * 2
def baseEnd_657598 : Nat := 300145645720376336445127

theorem tailTrace_657598 : CollatzResearch.WordTrace tailWord_657598 prefixEnd_657598 300145645720376336445127 := by
  unfold tailWord_657598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2998071183955278705268681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15989712981094819761432965 2998071183955278705268681)
  ·
    refine ⟨2248553387966459028951511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2998071183955278705268681 2248553387966459028951511)
    ·
      refine ⟨3372830081949688543427267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2248553387966459028951511 3372830081949688543427267)
      ·
        refine ⟨5059245122924532815140901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3372830081949688543427267 5059245122924532815140901)
        ·
          refine ⟨948608460548349902838919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5059245122924532815140901 948608460548349902838919)
          ·
            refine ⟨1422912690822524854258379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948608460548349902838919 1422912690822524854258379)
            ·
              refine ⟨2134369036233787281387569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422912690822524854258379 2134369036233787281387569)
              ·
                refine ⟨1600776777175340461040677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2134369036233787281387569 1600776777175340461040677)
                ·
                  refine ⟨300145645720376336445127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1600776777175340461040677 300145645720376336445127)
                  ·
                    rfl

theorem cell20_657598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_657598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657598 prefixEnd_657598 := by exact prefixLift 657598
  have htrace : WordTrace (prefixWord ++ tailWord_657598) baseStart_657598 baseEnd_657598 := by
    simpa [prefixWord, tailWord_657598, baseEnd_657598] using wordTrace_append hprefix tailTrace_657598
  have hstable : (prefixWord ++ tailWord_657598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657598).length < 2 ^ (prefixWord ++ tailWord_657598).sum := by decide
  have hdescent : baseEnd_657598 < baseStart_657598 := by decide
  rcases family_descends (prefixWord ++ tailWord_657598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657629 : List Nat := [1, 4, 3, 2, 1, 1, 3, 2, 3]
def baseStart_657629 : Nat := 118140960795 + 657629 * 2 ^ 59
def prefixEnd_657629 : Nat := 4983230072969 + 3 ^ 40 * 657629 * 2
def baseEnd_657629 : Nat := 300159794965078006411667

theorem tailTrace_657629 : CollatzResearch.WordTrace tailWord_657629 prefixEnd_657629 300159794965078006411667 := by
  unfold tailWord_657629
  simp only [CollatzResearch.WordTrace]
  refine ⟨23985700134529921936527941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15990466756353281291018627 23985700134529921936527941)
  ·
    refine ⟨4497318775224360363098989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23985700134529921936527941 4497318775224360363098989)
    ·
      refine ⟨1686494540709135136162121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4497318775224360363098989 1686494540709135136162121)
      ·
        refine ⟨1264870905531851352121591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1686494540709135136162121 1264870905531851352121591)
        ·
          refine ⟨1897306358297777028182387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1264870905531851352121591 1897306358297777028182387)
          ·
            refine ⟨2845959537446665542273581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1897306358297777028182387 2845959537446665542273581)
            ·
              refine ⟨1067234826542499578352593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2845959537446665542273581 1067234826542499578352593)
              ·
                refine ⟨800426119906874683764445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1067234826542499578352593 800426119906874683764445)
                ·
                  refine ⟨300159794965078006411667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 800426119906874683764445 300159794965078006411667)
                  ·
                    rfl

theorem cell20_657629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_657629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657629 prefixEnd_657629 := by exact prefixLift 657629
  have htrace : WordTrace (prefixWord ++ tailWord_657629) baseStart_657629 baseEnd_657629 := by
    simpa [prefixWord, tailWord_657629, baseEnd_657629] using wordTrace_append hprefix tailTrace_657629
  have hstable : (prefixWord ++ tailWord_657629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657629).length < 2 ^ (prefixWord ++ tailWord_657629).sum := by decide
  have hdescent : baseEnd_657629 < baseStart_657629 := by decide
  rcases family_descends (prefixWord ++ tailWord_657629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657633 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 5]
def baseStart_657633 : Nat := 118140960795 + 657633 * 2 ^ 59
def prefixEnd_657633 : Nat := 4983230072969 + 3 ^ 40 * 657633 * 2
def baseEnd_657633 : Nat := 300161620674071770278317

theorem tailTrace_657633 : CollatzResearch.WordTrace tailWord_657633 prefixEnd_657633 300161620674071770278317 := by
  unfold tailWord_657633
  simp only [CollatzResearch.WordTrace]
  refine ⟨23985846026515430619673553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15990564017676953746449035 23985846026515430619673553)
  ·
    refine ⟨17989384519886572964755165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23985846026515430619673553 17989384519886572964755165)
    ·
      refine ⟨6746019194957464861783187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17989384519886572964755165 6746019194957464861783187)
      ·
        refine ⟨10119028792436197292674781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6746019194957464861783187 10119028792436197292674781)
        ·
          refine ⟨3794635797163573984753043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10119028792436197292674781 3794635797163573984753043)
          ·
            refine ⟨5691953695745360977129565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3794635797163573984753043 5691953695745360977129565)
            ·
              refine ⟨2134482635904510366423587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5691953695745360977129565 2134482635904510366423587)
              ·
                refine ⟨3201723953856765549635381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2134482635904510366423587 3201723953856765549635381)
                ·
                  refine ⟨300161620674071770278317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3201723953856765549635381 300161620674071770278317)
                  ·
                    rfl

theorem cell20_657633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_657633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657633 prefixEnd_657633 := by exact prefixLift 657633
  have htrace : WordTrace (prefixWord ++ tailWord_657633) baseStart_657633 baseEnd_657633 := by
    simpa [prefixWord, tailWord_657633, baseEnd_657633] using wordTrace_append hprefix tailTrace_657633
  have hstable : (prefixWord ++ tailWord_657633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657633).length < 2 ^ (prefixWord ++ tailWord_657633).sum := by decide
  have hdescent : baseEnd_657633 < baseStart_657633 := by decide
  rcases family_descends (prefixWord ++ tailWord_657633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657664 : List Nat := [2, 1, 1, 2, 1, 1, 8, 4]
def baseStart_657664 : Nat := 118140960795 + 657664 * 2 ^ 59
def prefixEnd_657664 : Nat := 4983230072969 + 3 ^ 40 * 657664 * 2
def baseEnd_657664 : Nat := 100058589972924480081619

theorem tailTrace_657664 : CollatzResearch.WordTrace tailWord_657664 prefixEnd_657664 100058589972924480081619 := by
  unfold tailWord_657664
  simp only [CollatzResearch.WordTrace]
  refine ⟨11993488344701561457026023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15991317792935415276034697 11993488344701561457026023)
  ·
    refine ⟨17990232517052342185539035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11993488344701561457026023 17990232517052342185539035)
    ·
      refine ⟨26985348775578513278308553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17990232517052342185539035 26985348775578513278308553)
      ·
        refine ⟨20239011581683884958731415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26985348775578513278308553 20239011581683884958731415)
        ·
          refine ⟨30358517372525827438097123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20239011581683884958731415 30358517372525827438097123)
          ·
            refine ⟨45537776058788741157145685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30358517372525827438097123 45537776058788741157145685)
            ·
              refine ⟨533645813188930560435301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 45537776058788741157145685 533645813188930560435301)
              ·
                refine ⟨100058589972924480081619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 533645813188930560435301 100058589972924480081619)
                ·
                  rfl

theorem cell20_657664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 4].length) (baseStart_657664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657664 prefixEnd_657664 := by exact prefixLift 657664
  have htrace : WordTrace (prefixWord ++ tailWord_657664) baseStart_657664 baseEnd_657664 := by
    simpa [prefixWord, tailWord_657664, baseEnd_657664] using wordTrace_append hprefix tailTrace_657664
  have hstable : (prefixWord ++ tailWord_657664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657664).length < 2 ^ (prefixWord ++ tailWord_657664).sum := by decide
  have hdescent : baseEnd_657664 < baseStart_657664 := by decide
  rcases family_descends (prefixWord ++ tailWord_657664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657674 : List Nat := [3, 1, 2, 2, 1, 1, 5, 3, 2]
def baseStart_657674 : Nat := 118140960795 + 657674 * 2 ^ 59
def prefixEnd_657674 : Nat := 4983230072969 + 3 ^ 40 * 657674 * 2
def baseEnd_657674 : Nat := 300180334191257849911483

theorem tailTrace_657674 : CollatzResearch.WordTrace tailWord_657674 prefixEnd_657674 300180334191257849911483 := by
  unfold tailWord_657674
  simp only [CollatzResearch.WordTrace]
  refine ⟨5996835354841723655479019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15991560946244596414610717 5996835354841723655479019)
  ·
    refine ⟨8995253032262585483218529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5996835354841723655479019 8995253032262585483218529)
    ·
      refine ⟨6746439774196939112413897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8995253032262585483218529 6746439774196939112413897)
      ·
        refine ⟨5059829830647704334310423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6746439774196939112413897 5059829830647704334310423)
        ·
          refine ⟨7589744745971556501465635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5059829830647704334310423 7589744745971556501465635)
          ·
            refine ⟨11384617118957334752198453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7589744745971556501465635 11384617118957334752198453)
            ·
              refine ⟨1067307854902250133018605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11384617118957334752198453 1067307854902250133018605)
              ·
                refine ⟨400240445588343799881977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1067307854902250133018605 400240445588343799881977)
                ·
                  refine ⟨300180334191257849911483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 400240445588343799881977 300180334191257849911483)
                  ·
                    rfl

theorem cell20_657674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_657674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657674 prefixEnd_657674 := by exact prefixLift 657674
  have htrace : WordTrace (prefixWord ++ tailWord_657674) baseStart_657674 baseEnd_657674 := by
    simpa [prefixWord, tailWord_657674, baseEnd_657674] using wordTrace_append hprefix tailTrace_657674
  have hstable : (prefixWord ++ tailWord_657674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657674).length < 2 ^ (prefixWord ++ tailWord_657674).sum := by decide
  have hdescent : baseEnd_657674 < baseStart_657674 := by decide
  rcases family_descends (prefixWord ++ tailWord_657674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657685 : List Nat := [1, 3, 2, 1, 2, 1, 10]
def baseStart_657685 : Nat := 118140960795 + 657685 * 2 ^ 59
def prefixEnd_657685 : Nat := 4983230072969 + 3 ^ 40 * 657685 * 2
def baseEnd_657685 : Nat := 33353928321221188949419

theorem tailTrace_657685 : CollatzResearch.WordTrace tailWord_657685 prefixEnd_657685 33353928321221188949419 := by
  unfold tailWord_657685
  simp only [CollatzResearch.WordTrace]
  refine ⟨23987742622327043500566509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15991828414884695667044339 23987742622327043500566509)
  ·
    refine ⟨8995403483372641312712441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23987742622327043500566509 8995403483372641312712441)
    ·
      refine ⟨6746552612529480984534331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8995403483372641312712441 6746552612529480984534331)
      ·
        refine ⟨10119828918794221476801497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6746552612529480984534331 10119828918794221476801497)
        ·
          refine ⟨7589871689095666107601123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10119828918794221476801497 7589871689095666107601123)
          ·
            refine ⟨11384807533643499161401685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7589871689095666107601123 11384807533643499161401685)
            ·
              refine ⟨33353928321221188949419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11384807533643499161401685 33353928321221188949419)
              ·
                rfl

theorem cell20_657685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 10].length) (baseStart_657685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657685 prefixEnd_657685 := by exact prefixLift 657685
  have htrace : WordTrace (prefixWord ++ tailWord_657685) baseStart_657685 baseEnd_657685 := by
    simpa [prefixWord, tailWord_657685, baseEnd_657685] using wordTrace_append hprefix tailTrace_657685
  have hstable : (prefixWord ++ tailWord_657685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657685).length < 2 ^ (prefixWord ++ tailWord_657685).sum := by decide
  have hdescent : baseEnd_657685 < baseStart_657685 := by decide
  rcases family_descends (prefixWord ++ tailWord_657685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657695 : List Nat := [1, 1, 2, 4, 3, 1, 3, 1, 4]
def baseStart_657695 : Nat := 118140960795 + 657695 * 2 ^ 59
def prefixEnd_657695 : Nat := 4983230072969 + 3 ^ 40 * 657695 * 2
def baseEnd_657695 : Nat := 300189919163475110211397

theorem tailTrace_657695 : CollatzResearch.WordTrace tailWord_657695 prefixEnd_657695 300189919163475110211397 := by
  unfold tailWord_657695
  simp only [CollatzResearch.WordTrace]
  refine ⟨23988107352290815208430539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15992071568193876805620359 23988107352290815208430539)
  ·
    refine ⟨35982161028436222812645809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23988107352290815208430539 35982161028436222812645809)
    ·
      refine ⟨26986620771327167109484357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35982161028436222812645809 26986620771327167109484357)
      ·
        refine ⟨5059991394623843833028317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26986620771327167109484357 5059991394623843833028317)
        ·
          refine ⟨1897496772983941437385619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5059991394623843833028317 1897496772983941437385619)
          ·
            refine ⟨2846245159475912156078429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1897496772983941437385619 2846245159475912156078429)
            ·
              refine ⟨1067341934803467058529411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2846245159475912156078429 1067341934803467058529411)
              ·
                refine ⟨1601012902205200587794117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1067341934803467058529411 1601012902205200587794117)
                ·
                  refine ⟨300189919163475110211397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1601012902205200587794117 300189919163475110211397)
                  ·
                    rfl

theorem cell20_657695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 4].length) (baseStart_657695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657695 prefixEnd_657695 := by exact prefixLift 657695
  have htrace : WordTrace (prefixWord ++ tailWord_657695) baseStart_657695 baseEnd_657695 := by
    simpa [prefixWord, tailWord_657695, baseEnd_657695] using wordTrace_append hprefix tailTrace_657695
  have hstable : (prefixWord ++ tailWord_657695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657695).length < 2 ^ (prefixWord ++ tailWord_657695).sum := by decide
  have hdescent : baseEnd_657695 < baseStart_657695 := by decide
  rcases family_descends (prefixWord ++ tailWord_657695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657754 : List Nat := [3, 1, 1, 2, 1, 2, 1, 5, 4]
def baseStart_657754 : Nat := 118140960795 + 657754 * 2 ^ 59
def prefixEnd_657754 : Nat := 4983230072969 + 3 ^ 40 * 657754 * 2
def baseEnd_657754 : Nat := 300216848371133127244489

theorem tailTrace_657754 : CollatzResearch.WordTrace tailWord_657754 prefixEnd_657754 300216848371133127244489 := by
  unfold tailWord_657754
  simp only [CollatzResearch.WordTrace]
  refine ⟨5997564814769267071207079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15993506172718045523218877 5997564814769267071207079)
  ·
    refine ⟨8996347222153900606810619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5997564814769267071207079 8996347222153900606810619)
    ·
      refine ⟨13494520833230850910215929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8996347222153900606810619 13494520833230850910215929)
      ·
        refine ⟨10120890624923138182661947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13494520833230850910215929 10120890624923138182661947)
        ·
          refine ⟨15181335937384707273992921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10120890624923138182661947 15181335937384707273992921)
          ·
            refine ⟨11386001953038530455494691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15181335937384707273992921 11386001953038530455494691)
            ·
              refine ⟨17079002929557795683242037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11386001953038530455494691 17079002929557795683242037)
              ·
                refine ⟨1601156524646043345303941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17079002929557795683242037 1601156524646043345303941)
                ·
                  refine ⟨300216848371133127244489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1601156524646043345303941 300216848371133127244489)
                  ·
                    rfl

theorem cell20_657754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_657754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657754 prefixEnd_657754 := by exact prefixLift 657754
  have htrace : WordTrace (prefixWord ++ tailWord_657754) baseStart_657754 baseEnd_657754 := by
    simpa [prefixWord, tailWord_657754, baseEnd_657754] using wordTrace_append hprefix tailTrace_657754
  have hstable : (prefixWord ++ tailWord_657754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657754).length < 2 ^ (prefixWord ++ tailWord_657754).sum := by decide
  have hdescent : baseEnd_657754 < baseStart_657754 := by decide
  rcases family_descends (prefixWord ++ tailWord_657754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657799 : List Nat := [1, 1, 4, 2, 2, 1, 9]
def baseStart_657799 : Nat := 118140960795 + 657799 * 2 ^ 59
def prefixEnd_657799 : Nat := 4983230072969 + 3 ^ 40 * 657799 * 2
def baseEnd_657799 : Nat := 33359709733034774527145

theorem tailTrace_657799 : CollatzResearch.WordTrace tailWord_657799 prefixEnd_657799 33359709733034774527145 := by
  unfold tailWord_657799
  simp only [CollatzResearch.WordTrace]
  refine ⟨23991900543914040970216451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15994600362609360646810967 23991900543914040970216451)
  ·
    refine ⟨35987850815871061455324677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23991900543914040970216451 35987850815871061455324677)
    ·
      refine ⟨6747722027975824022873377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35987850815871061455324677 6747722027975824022873377)
      ·
        refine ⟨5060791520981868017155033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6747722027975824022873377 5060791520981868017155033)
        ·
          refine ⟨3795593640736401012866275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5060791520981868017155033 3795593640736401012866275)
          ·
            refine ⟨5693390461104601519299413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3795593640736401012866275 5693390461104601519299413)
            ·
              refine ⟨33359709733034774527145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5693390461104601519299413 33359709733034774527145)
              ·
                rfl

theorem cell20_657799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 9].length) (baseStart_657799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657799 prefixEnd_657799 := by exact prefixLift 657799
  have htrace : WordTrace (prefixWord ++ tailWord_657799) baseStart_657799 baseEnd_657799 := by
    simpa [prefixWord, tailWord_657799, baseEnd_657799] using wordTrace_append hprefix tailTrace_657799
  have hstable : (prefixWord ++ tailWord_657799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657799).length < 2 ^ (prefixWord ++ tailWord_657799).sum := by decide
  have hdescent : baseEnd_657799 < baseStart_657799 := by decide
  rcases family_descends (prefixWord ++ tailWord_657799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657860 : List Nat := [2, 3, 3, 2, 2, 1, 3, 2, 2]
def baseStart_657860 : Nat := 118140960795 + 657860 * 2 ^ 59
def prefixEnd_657860 : Nat := 4983230072969 + 3 ^ 40 * 657860 * 2
def baseEnd_657860 : Nat := 300265229659467869710723

theorem tailTrace_657860 : CollatzResearch.WordTrace tailWord_657860 prefixEnd_657860 300265229659467869710723 := by
  unfold tailWord_657860
  simp only [CollatzResearch.WordTrace]
  refine ⟨11997062698346524194093517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15996083597795365592124689 11997062698346524194093517)
  ·
    refine ⟨4498898511879946572785069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11997062698346524194093517 4498898511879946572785069)
    ·
      refine ⟨1687086941954979964794401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4498898511879946572785069 1687086941954979964794401)
      ·
        refine ⟨1265315206466234973595801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1687086941954979964794401 1265315206466234973595801)
        ·
          refine ⟨948986404849676230196851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1265315206466234973595801 948986404849676230196851)
          ·
            refine ⟨1423479607274514345295277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948986404849676230196851 1423479607274514345295277)
            ·
              refine ⟨533804852727942879485729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1423479607274514345295277 533804852727942879485729)
              ·
                refine ⟨400353639545957159614297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 533804852727942879485729 400353639545957159614297)
                ·
                  refine ⟨300265229659467869710723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 400353639545957159614297 300265229659467869710723)
                  ·
                    rfl

theorem cell20_657860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_657860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657860 prefixEnd_657860 := by exact prefixLift 657860
  have htrace : WordTrace (prefixWord ++ tailWord_657860) baseStart_657860 baseEnd_657860 := by
    simpa [prefixWord, tailWord_657860, baseEnd_657860] using wordTrace_append hprefix tailTrace_657860
  have hstable : (prefixWord ++ tailWord_657860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657860).length < 2 ^ (prefixWord ++ tailWord_657860).sum := by decide
  have hdescent : baseEnd_657860 < baseStart_657860 := by decide
  rcases family_descends (prefixWord ++ tailWord_657860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657909 : List Nat := [1, 3, 5, 1, 3, 7]
def baseStart_657909 : Nat := 118140960795 + 657909 * 2 ^ 59
def prefixEnd_657909 : Nat := 4983230072969 + 3 ^ 40 * 657909 * 2
def baseEnd_657909 : Nat := 11121762762764499151007

theorem tailTrace_657909 : CollatzResearch.WordTrace tailWord_657909 prefixEnd_657909 11121762762764499151007 := by
  unfold tailWord_657909
  simp only [CollatzResearch.WordTrace]
  refine ⟨23995912573515529756720781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15997275049010353171147187 23995912573515529756720781)
  ·
    refine ⟨8998467215068323658770293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23995912573515529756720781 8998467215068323658770293)
    ·
      refine ⟨843606301412655343009715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8998467215068323658770293 843606301412655343009715)
      ·
        refine ⟨1265409452118983014514573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 843606301412655343009715 1265409452118983014514573)
        ·
          refine ⟨474528544544618630442965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1265409452118983014514573 474528544544618630442965)
          ·
            refine ⟨11121762762764499151007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 474528544544618630442965 11121762762764499151007)
            ·
              rfl

theorem cell20_657909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 7].length) (baseStart_657909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657909 prefixEnd_657909 := by exact prefixLift 657909
  have htrace : WordTrace (prefixWord ++ tailWord_657909) baseStart_657909 baseEnd_657909 := by
    simpa [prefixWord, tailWord_657909, baseEnd_657909] using wordTrace_append hprefix tailTrace_657909
  have hstable : (prefixWord ++ tailWord_657909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657909).length < 2 ^ (prefixWord ++ tailWord_657909).sum := by decide
  have hdescent : baseEnd_657909 < baseStart_657909 := by decide
  rcases family_descends (prefixWord ++ tailWord_657909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657923 : List Nat := [1, 1, 1, 3, 2, 1, 5, 4, 2]
def baseStart_657923 : Nat := 118140960795 + 657923 * 2 ^ 59
def prefixEnd_657923 : Nat := 4983230072969 + 3 ^ 40 * 657923 * 2
def baseEnd_657923 : Nat := 300293984576119650610465

theorem tailTrace_657923 : CollatzResearch.WordTrace tailWord_657923 prefixEnd_657923 300293984576119650610465 := by
  unfold tailWord_657923
  simp only [CollatzResearch.WordTrace]
  refine ⟨23996423195464810147730423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15997615463643206765153615 23996423195464810147730423)
  ·
    refine ⟨35994634793197215221595635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23996423195464810147730423 35994634793197215221595635)
    ·
      refine ⟨53991952189795822832393453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35994634793197215221595635 53991952189795822832393453)
      ·
        refine ⟨20246982071173433562147545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53991952189795822832393453 20246982071173433562147545)
        ·
          refine ⟨15185236553380075171610659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20246982071173433562147545 15185236553380075171610659)
          ·
            refine ⟨22777854830070112757415989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15185236553380075171610659 22777854830070112757415989)
            ·
              refine ⟨2135423890319073071007749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22777854830070112757415989 2135423890319073071007749)
              ·
                refine ⟨400391979434826200813953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2135423890319073071007749 400391979434826200813953)
                ·
                  refine ⟨300293984576119650610465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 400391979434826200813953 300293984576119650610465)
                  ·
                    rfl

theorem cell20_657923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 2].length) (baseStart_657923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657923 prefixEnd_657923 := by exact prefixLift 657923
  have htrace : WordTrace (prefixWord ++ tailWord_657923) baseStart_657923 baseEnd_657923 := by
    simpa [prefixWord, tailWord_657923, baseEnd_657923] using wordTrace_append hprefix tailTrace_657923
  have hstable : (prefixWord ++ tailWord_657923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657923).length < 2 ^ (prefixWord ++ tailWord_657923).sum := by decide
  have hdescent : baseEnd_657923 < baseStart_657923 := by decide
  rcases family_descends (prefixWord ++ tailWord_657923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657940 : List Nat := [2, 4, 3, 1, 1, 2, 1, 2, 4]
def baseStart_657940 : Nat := 118140960795 + 657940 * 2 ^ 59
def prefixEnd_657940 : Nat := 4983230072969 + 3 ^ 40 * 657940 * 2
def baseEnd_657940 : Nat := 300301743839343147043729

theorem tailTrace_657940 : CollatzResearch.WordTrace tailWord_657940 prefixEnd_657940 300301743839343147043729 := by
  unfold tailWord_657940
  simp only [CollatzResearch.WordTrace]
  refine ⟨11998521618201611025549637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15998028824268814700732849 11998521618201611025549637)
  ·
    refine ⟨2249722803412802067290557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11998521618201611025549637 2249722803412802067290557)
    ·
      refine ⟨843646051279800775233959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2249722803412802067290557 843646051279800775233959)
      ·
        refine ⟨1265469076919701162850939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 843646051279800775233959 1265469076919701162850939)
        ·
          refine ⟨1898203615379551744276409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1265469076919701162850939 1898203615379551744276409)
          ·
            refine ⟨1423652711534663808207307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1898203615379551744276409 1423652711534663808207307)
            ·
              refine ⟨2135479067301995712310961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1423652711534663808207307 2135479067301995712310961)
              ·
                refine ⟨1601609300476496784233221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2135479067301995712310961 1601609300476496784233221)
                ·
                  refine ⟨300301743839343147043729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1601609300476496784233221 300301743839343147043729)
                  ·
                    rfl

theorem cell20_657940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_657940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657940 prefixEnd_657940 := by exact prefixLift 657940
  have htrace : WordTrace (prefixWord ++ tailWord_657940) baseStart_657940 baseEnd_657940 := by
    simpa [prefixWord, tailWord_657940, baseEnd_657940] using wordTrace_append hprefix tailTrace_657940
  have hstable : (prefixWord ++ tailWord_657940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657940).length < 2 ^ (prefixWord ++ tailWord_657940).sum := by decide
  have hdescent : baseEnd_657940 < baseStart_657940 := by decide
  rcases family_descends (prefixWord ++ tailWord_657940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657944 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 6]
def baseStart_657944 : Nat := 118140960795 + 657944 * 2 ^ 59
def prefixEnd_657944 : Nat := 4983230072969 + 3 ^ 40 * 657944 * 2
def baseEnd_657944 : Nat := 300303569548336910910379

theorem tailTrace_657944 : CollatzResearch.WordTrace tailWord_657944 prefixEnd_657944 300303569548336910910379 := by
  unfold tailWord_657944
  simp only [CollatzResearch.WordTrace]
  refine ⟨11998594564194365367122443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15998126085592487156163257 11998594564194365367122443)
  ·
    refine ⟨17997891846291548050683665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11998594564194365367122443 17997891846291548050683665)
    ·
      refine ⟨13498418884718661038012749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17997891846291548050683665 13498418884718661038012749)
      ·
        refine ⟨5061907081769497889254781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13498418884718661038012749 5061907081769497889254781)
        ·
          refine ⟨1898215155663561708470543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5061907081769497889254781 1898215155663561708470543)
          ·
            refine ⟨2847322733495342562705815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1898215155663561708470543 2847322733495342562705815)
            ·
              refine ⟨4270984100243013844058723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2847322733495342562705815 4270984100243013844058723)
              ·
                refine ⟨6406476150364520766088085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4270984100243013844058723 6406476150364520766088085)
                ·
                  refine ⟨300303569548336910910379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6406476150364520766088085 300303569548336910910379)
                  ·
                    rfl

theorem cell20_657944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_657944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_657944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_657944 prefixEnd_657944 := by exact prefixLift 657944
  have htrace : WordTrace (prefixWord ++ tailWord_657944) baseStart_657944 baseEnd_657944 := by
    simpa [prefixWord, tailWord_657944, baseEnd_657944] using wordTrace_append hprefix tailTrace_657944
  have hstable : (prefixWord ++ tailWord_657944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657944).length < 2 ^ (prefixWord ++ tailWord_657944).sum := by decide
  have hdescent : baseEnd_657944 < baseStart_657944 := by decide
  rcases family_descends (prefixWord ++ tailWord_657944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658012 : List Nat := [2, 2, 4, 1, 4, 1, 1, 3, 2]
def baseStart_658012 : Nat := 118140960795 + 658012 * 2 ^ 59
def prefixEnd_658012 : Nat := 4983230072969 + 3 ^ 40 * 658012 * 2
def baseEnd_658012 : Nat := 300334606601230896643435

theorem tailTrace_658012 : CollatzResearch.WordTrace tailWord_658012 prefixEnd_658012 300334606601230896643435 := by
  unfold tailWord_658012
  simp only [CollatzResearch.WordTrace]
  refine ⟨11999834646071189173860145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15999779528094918898480193 11999834646071189173860145)
  ·
    refine ⟨8999875984553391880395109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11999834646071189173860145 8999875984553391880395109)
    ·
      refine ⟨1687476747103760977574083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8999875984553391880395109 1687476747103760977574083)
      ·
        refine ⟨2531215120655641466361125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1687476747103760977574083 2531215120655641466361125)
        ·
          refine ⟨474602835122932774942711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2531215120655641466361125 474602835122932774942711)
          ·
            refine ⟨711904252684399162414067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474602835122932774942711 711904252684399162414067)
            ·
              refine ⟨1067856379026598743621101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 711904252684399162414067 1067856379026598743621101)
              ·
                refine ⟨400446142134974528857913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1067856379026598743621101 400446142134974528857913)
                ·
                  refine ⟨300334606601230896643435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 400446142134974528857913 300334606601230896643435)
                  ·
                    rfl

theorem cell20_658012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_658012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658012 prefixEnd_658012 := by exact prefixLift 658012
  have htrace : WordTrace (prefixWord ++ tailWord_658012) baseStart_658012 baseEnd_658012 := by
    simpa [prefixWord, tailWord_658012, baseEnd_658012] using wordTrace_append hprefix tailTrace_658012
  have hstable : (prefixWord ++ tailWord_658012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658012).length < 2 ^ (prefixWord ++ tailWord_658012).sum := by decide
  have hdescent : baseEnd_658012 < baseStart_658012 := by decide
  rcases family_descends (prefixWord ++ tailWord_658012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658120 : List Nat := [2, 1, 3, 1, 2, 4, 3, 4]
def baseStart_658120 : Nat := 118140960795 + 658120 * 2 ^ 59
def prefixEnd_658120 : Nat := 4983230072969 + 3 ^ 40 * 658120 * 2
def baseEnd_658120 : Nat := 100127966914687507014331

theorem tailTrace_658120 : CollatzResearch.WordTrace tailWord_658120 prefixEnd_658120 100127966914687507014331 := by
  unfold tailWord_658120
  simp only [CollatzResearch.WordTrace]
  refine ⟨12001804187875556396325907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16002405583834075195101209 12001804187875556396325907)
  ·
    refine ⟨18002706281813334594488861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12001804187875556396325907 18002706281813334594488861)
    ·
      refine ⟨6751014855680000472933323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18002706281813334594488861 6751014855680000472933323)
      ·
        refine ⟨10126522283520000709399985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6751014855680000472933323 10126522283520000709399985)
        ·
          refine ⟨7594891712640000532049989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10126522283520000709399985 7594891712640000532049989)
          ·
            refine ⟨1424042196120000099759373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7594891712640000532049989 1424042196120000099759373)
            ·
              refine ⟨534015823545000037409765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1424042196120000099759373 534015823545000037409765)
              ·
                refine ⟨100127966914687507014331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 534015823545000037409765 100127966914687507014331)
                ·
                  rfl

theorem cell20_658120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 4].length) (baseStart_658120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658120 prefixEnd_658120 := by exact prefixLift 658120
  have htrace : WordTrace (prefixWord ++ tailWord_658120) baseStart_658120 baseEnd_658120 := by
    simpa [prefixWord, tailWord_658120, baseEnd_658120] using wordTrace_append hprefix tailTrace_658120
  have hstable : (prefixWord ++ tailWord_658120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658120).length < 2 ^ (prefixWord ++ tailWord_658120).sum := by decide
  have hdescent : baseEnd_658120 < baseStart_658120 := by decide
  rcases family_descends (prefixWord ++ tailWord_658120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658172 : List Nat := [2, 2, 2, 1, 3, 2, 2, 2, 4]
def baseStart_658172 : Nat := 118140960795 + 658172 * 2 ^ 59
def prefixEnd_658172 : Nat := 4983230072969 + 3 ^ 40 * 658172 * 2
def baseEnd_658172 : Nat := 300407634960981451309447

theorem tailTrace_658172 : CollatzResearch.WordTrace tailWord_658172 prefixEnd_658172 300407634960981451309447 := by
  unfold tailWord_658172
  simp only [CollatzResearch.WordTrace]
  refine ⟨12002752485781362836772385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16003669981041817115696513 12002752485781362836772385)
  ·
    refine ⟨9002064364336022127579289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12002752485781362836772385 9002064364336022127579289)
    ·
      refine ⟨6751548273252016595684467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9002064364336022127579289 6751548273252016595684467)
      ·
        refine ⟨10127322409878024893526701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6751548273252016595684467 10127322409878024893526701)
        ·
          refine ⟨3797745903704259335072513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10127322409878024893526701 3797745903704259335072513)
          ·
            refine ⟨2848309427778194501304385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3797745903704259335072513 2848309427778194501304385)
            ·
              refine ⟨2136232070833645875978289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2848309427778194501304385 2136232070833645875978289)
              ·
                refine ⟨1602174053125234406983717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2136232070833645875978289 1602174053125234406983717)
                ·
                  refine ⟨300407634960981451309447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1602174053125234406983717 300407634960981451309447)
                  ·
                    rfl

theorem cell20_658172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_658172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658172 prefixEnd_658172 := by exact prefixLift 658172
  have htrace : WordTrace (prefixWord ++ tailWord_658172) baseStart_658172 baseEnd_658172 := by
    simpa [prefixWord, tailWord_658172, baseEnd_658172] using wordTrace_append hprefix tailTrace_658172
  have hstable : (prefixWord ++ tailWord_658172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658172).length < 2 ^ (prefixWord ++ tailWord_658172).sum := by decide
  have hdescent : baseEnd_658172 < baseStart_658172 := by decide
  rcases family_descends (prefixWord ++ tailWord_658172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658186 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 7]
def baseStart_658186 : Nat := 118140960795 + 658186 * 2 ^ 59
def prefixEnd_658186 : Nat := 4983230072969 + 3 ^ 40 * 658186 * 2
def baseEnd_658186 : Nat := 300414024942459624842723

theorem tailTrace_658186 : CollatzResearch.WordTrace tailWord_658186 prefixEnd_658186 300414024942459624842723 := by
  unfold tailWord_658186
  simp only [CollatzResearch.WordTrace]
  refine ⟨6001503898378001516138603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16004010395674670709702941 6001503898378001516138603)
  ·
    refine ⟨9002255847567002274207905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6001503898378001516138603 9002255847567002274207905)
    ·
      refine ⟨6751691885675251705655929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9002255847567002274207905 6751691885675251705655929)
      ·
        refine ⟨5063768914256438779241947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6751691885675251705655929 5063768914256438779241947)
        ·
          refine ⟨7595653371384658168862921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5063768914256438779241947 7595653371384658168862921)
          ·
            refine ⟨5696740028538493626647191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7595653371384658168862921 5696740028538493626647191)
            ·
              refine ⟨8545110042807740439970787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5696740028538493626647191 8545110042807740439970787)
              ·
                refine ⟨12817665064211610659956181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8545110042807740439970787 12817665064211610659956181)
                ·
                  refine ⟨300414024942459624842723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12817665064211610659956181 300414024942459624842723)
                  ·
                    rfl

theorem cell20_658186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_658186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658186 prefixEnd_658186 := by exact prefixLift 658186
  have htrace : WordTrace (prefixWord ++ tailWord_658186) baseStart_658186 baseEnd_658186 := by
    simpa [prefixWord, tailWord_658186, baseEnd_658186] using wordTrace_append hprefix tailTrace_658186
  have hstable : (prefixWord ++ tailWord_658186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658186).length < 2 ^ (prefixWord ++ tailWord_658186).sum := by decide
  have hdescent : baseEnd_658186 < baseStart_658186 := by decide
  rcases family_descends (prefixWord ++ tailWord_658186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658193 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 6]
def baseStart_658193 : Nat := 118140960795 + 658193 * 2 ^ 59
def prefixEnd_658193 : Nat := 4983230072969 + 3 ^ 40 * 658193 * 2
def baseEnd_658193 : Nat := 300417219933198711609361

theorem tailTrace_658193 : CollatzResearch.WordTrace tailWord_658193 prefixEnd_658193 300417219933198711609361 := by
  unfold tailWord_658193
  simp only [CollatzResearch.WordTrace]
  refine ⟨24006270904486646260059233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16004180602991097506706155 24006270904486646260059233)
  ·
    refine ⟨18004703178364984695044425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24006270904486646260059233 18004703178364984695044425)
    ·
      refine ⟨13503527383773738521283319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18004703178364984695044425 13503527383773738521283319)
      ·
        refine ⟨20255291075660607781924979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13503527383773738521283319 20255291075660607781924979)
        ·
          refine ⟨30382936613490911672887469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20255291075660607781924979 30382936613490911672887469)
          ·
            refine ⟨11393601230059091877332801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30382936613490911672887469 11393601230059091877332801)
            ·
              refine ⟨8545200922544318907999601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11393601230059091877332801 8545200922544318907999601)
              ·
                refine ⟨6408900691908239180999701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8545200922544318907999601 6408900691908239180999701)
                ·
                  refine ⟨300417219933198711609361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6408900691908239180999701 300417219933198711609361)
                  ·
                    rfl

theorem cell20_658193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_658193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658193 prefixEnd_658193 := by exact prefixLift 658193
  have htrace : WordTrace (prefixWord ++ tailWord_658193) baseStart_658193 baseEnd_658193 := by
    simpa [prefixWord, tailWord_658193, baseEnd_658193] using wordTrace_append hprefix tailTrace_658193
  have hstable : (prefixWord ++ tailWord_658193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658193).length < 2 ^ (prefixWord ++ tailWord_658193).sum := by decide
  have hdescent : baseEnd_658193 < baseStart_658193 := by decide
  rcases family_descends (prefixWord ++ tailWord_658193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658231 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 6]
def baseStart_658231 : Nat := 118140960795 + 658231 * 2 ^ 59
def prefixEnd_658231 : Nat := 4983230072969 + 3 ^ 40 * 658231 * 2
def baseEnd_658231 : Nat := 300434564168639468342539

theorem tailTrace_658231 : CollatzResearch.WordTrace tailWord_658231 prefixEnd_658231 300434564168639468342539 := by
  unfold tailWord_658231
  simp only [CollatzResearch.WordTrace]
  refine ⟨24007656878348978749942547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16005104585565985833295031 24007656878348978749942547)
  ·
    refine ⟨36011485317523468124913821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24007656878348978749942547 36011485317523468124913821)
    ·
      refine ⟨13504306994071300546842683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36011485317523468124913821 13504306994071300546842683)
      ·
        refine ⟨20256460491106950820264025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13504306994071300546842683 20256460491106950820264025)
        ·
          refine ⟨15192345368330213115198019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20256460491106950820264025 15192345368330213115198019)
          ·
            refine ⟨22788518052495319672797029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15192345368330213115198019 22788518052495319672797029)
            ·
              refine ⟨4272847134842872438649443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22788518052495319672797029 4272847134842872438649443)
              ·
                refine ⟨6409270702264308657974165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4272847134842872438649443 6409270702264308657974165)
                ·
                  refine ⟨300434564168639468342539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6409270702264308657974165 300434564168639468342539)
                  ·
                    rfl

theorem cell20_658231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_658231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658231 prefixEnd_658231 := by exact prefixLift 658231
  have htrace : WordTrace (prefixWord ++ tailWord_658231) baseStart_658231 baseEnd_658231 := by
    simpa [prefixWord, tailWord_658231, baseEnd_658231] using wordTrace_append hprefix tailTrace_658231
  have hstable : (prefixWord ++ tailWord_658231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658231).length < 2 ^ (prefixWord ++ tailWord_658231).sum := by decide
  have hdescent : baseEnd_658231 < baseStart_658231 := by decide
  rcases family_descends (prefixWord ++ tailWord_658231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658265 : List Nat := [1, 2, 1, 2, 2, 5, 1, 4, 2]
def baseStart_658265 : Nat := 118140960795 + 658265 * 2 ^ 59
def prefixEnd_658265 : Nat := 4983230072969 + 3 ^ 40 * 658265 * 2
def baseEnd_658265 : Nat := 300450082695086461209067

theorem tailTrace_658265 : CollatzResearch.WordTrace tailWord_658265 prefixEnd_658265 300450082695086461209067 := by
  unfold tailWord_658265
  simp only [CollatzResearch.WordTrace]
  refine ⟨24008896960225802556680249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16005931306817201704453499 24008896960225802556680249)
  ·
    refine ⟨18006672720169351917510187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24008896960225802556680249 18006672720169351917510187)
    ·
      refine ⟨27010009080254027876265281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18006672720169351917510187 27010009080254027876265281)
      ·
        refine ⟨20257506810190520907198961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27010009080254027876265281 20257506810190520907198961)
        ·
          refine ⟨15193130107642890680399221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20257506810190520907198961 15193130107642890680399221)
          ·
            refine ⟨1424355947591521001287427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15193130107642890680399221 1424355947591521001287427)
            ·
              refine ⟨2136533921387281501931141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1424355947591521001287427 2136533921387281501931141)
              ·
                refine ⟨400600110260115281612089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2136533921387281501931141 400600110260115281612089)
                ·
                  refine ⟨300450082695086461209067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 400600110260115281612089 300450082695086461209067)
                  ·
                    rfl

theorem cell20_658265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 2].length) (baseStart_658265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658265 prefixEnd_658265 := by exact prefixLift 658265
  have htrace : WordTrace (prefixWord ++ tailWord_658265) baseStart_658265 baseEnd_658265 := by
    simpa [prefixWord, tailWord_658265, baseEnd_658265] using wordTrace_append hprefix tailTrace_658265
  have hstable : (prefixWord ++ tailWord_658265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658265).length < 2 ^ (prefixWord ++ tailWord_658265).sum := by decide
  have hdescent : baseEnd_658265 < baseStart_658265 := by decide
  rcases family_descends (prefixWord ++ tailWord_658265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658279 : List Nat := [1, 1, 5, 1, 2, 2, 2, 3, 3]
def baseStart_658279 : Nat := 118140960795 + 658279 * 2 ^ 59
def prefixEnd_658279 : Nat := 4983230072969 + 3 ^ 40 * 658279 * 2
def baseEnd_658279 : Nat := 300456472676564634742343

theorem tailTrace_658279 : CollatzResearch.WordTrace tailWord_658279 prefixEnd_658279 300456472676564634742343 := by
  unfold tailWord_658279
  simp only [CollatzResearch.WordTrace]
  refine ⟨24009407582175082947689891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16006271721450055298459927 24009407582175082947689891)
  ·
    refine ⟨36014111373262624421534837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24009407582175082947689891 36014111373262624421534837)
    ·
      refine ⟨3376322941243371039518891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36014111373262624421534837 3376322941243371039518891)
      ·
        refine ⟨5064484411865056559278337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3376322941243371039518891 5064484411865056559278337)
        ·
          refine ⟨3798363308898792419458753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5064484411865056559278337 3798363308898792419458753)
          ·
            refine ⟨2848772481674094314594065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3798363308898792419458753 2848772481674094314594065)
            ·
              refine ⟨2136579361255570735945549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2848772481674094314594065 2136579361255570735945549)
              ·
                refine ⟨801217260470839025979581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2136579361255570735945549 801217260470839025979581)
                ·
                  refine ⟨300456472676564634742343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 801217260470839025979581 300456472676564634742343)
                  ·
                    rfl

theorem cell20_658279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 3].length) (baseStart_658279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658279 prefixEnd_658279 := by exact prefixLift 658279
  have htrace : WordTrace (prefixWord ++ tailWord_658279) baseStart_658279 baseEnd_658279 := by
    simpa [prefixWord, tailWord_658279, baseEnd_658279] using wordTrace_append hprefix tailTrace_658279
  have hstable : (prefixWord ++ tailWord_658279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658279).length < 2 ^ (prefixWord ++ tailWord_658279).sum := by decide
  have hdescent : baseEnd_658279 < baseStart_658279 := by decide
  rcases family_descends (prefixWord ++ tailWord_658279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658307 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 6]
def baseStart_658307 : Nat := 118140960795 + 658307 * 2 ^ 59
def prefixEnd_658307 : Nat := 4983230072969 + 3 ^ 40 * 658307 * 2
def baseEnd_658307 : Nat := 300469252639520981808895

theorem tailTrace_658307 : CollatzResearch.WordTrace tailWord_658307 prefixEnd_658307 300469252639520981808895 := by
  unfold tailWord_658307
  simp only [CollatzResearch.WordTrace]
  refine ⟨24010428826073643729709175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16006952550715762486472783 24010428826073643729709175)
  ·
    refine ⟨36015643239110465594563763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24010428826073643729709175 36015643239110465594563763)
    ·
      refine ⟨54023464858665698391845645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36015643239110465594563763 54023464858665698391845645)
      ·
        refine ⟨20258799321999636896942117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54023464858665698391845645 20258799321999636896942117)
        ·
          refine ⟨3798524872874931918176647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20258799321999636896942117 3798524872874931918176647)
          ·
            refine ⟨5697787309312397877264971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3798524872874931918176647 5697787309312397877264971)
            ·
              refine ⟨8546680963968596815897457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5697787309312397877264971 8546680963968596815897457)
              ·
                refine ⟨6410010722976447611923093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8546680963968596815897457 6410010722976447611923093)
                ·
                  refine ⟨300469252639520981808895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6410010722976447611923093 300469252639520981808895)
                  ·
                    rfl

theorem cell20_658307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_658307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658307 prefixEnd_658307 := by exact prefixLift 658307
  have htrace : WordTrace (prefixWord ++ tailWord_658307) baseStart_658307 baseEnd_658307 := by
    simpa [prefixWord, tailWord_658307, baseEnd_658307] using wordTrace_append hprefix tailTrace_658307
  have hstable : (prefixWord ++ tailWord_658307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658307).length < 2 ^ (prefixWord ++ tailWord_658307).sum := by decide
  have hdescent : baseEnd_658307 < baseStart_658307 := by decide
  rcases family_descends (prefixWord ++ tailWord_658307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658345 : List Nat := [1, 2, 1, 1, 1, 1, 5, 4, 4]
def baseStart_658345 : Nat := 118140960795 + 658345 * 2 ^ 59
def prefixEnd_658345 : Nat := 4983230072969 + 3 ^ 40 * 658345 * 2
def baseEnd_658345 : Nat := 300486596874961738542073

theorem tailTrace_658345 : CollatzResearch.WordTrace tailWord_658345 prefixEnd_658345 300486596874961738542073 := by
  unfold tailWord_658345
  simp only [CollatzResearch.WordTrace]
  refine ⟨24011814799935976219592489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16007876533290650813061659 24011814799935976219592489)
  ·
    refine ⟨18008861099951982164694367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24011814799935976219592489 18008861099951982164694367)
    ·
      refine ⟨27013291649927973247041551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18008861099951982164694367 27013291649927973247041551)
      ·
        refine ⟨40519937474891959870562327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27013291649927973247041551 40519937474891959870562327)
        ·
          refine ⟨60779906212337939805843491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40519937474891959870562327 60779906212337939805843491)
          ·
            refine ⟨91169859318506909708765237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60779906212337939805843491 91169859318506909708765237)
            ·
              refine ⟨8547174311110022785196741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91169859318506909708765237 8547174311110022785196741)
              ·
                refine ⟨1602595183333129272224389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8547174311110022785196741 1602595183333129272224389)
                ·
                  refine ⟨300486596874961738542073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1602595183333129272224389 300486596874961738542073)
                  ·
                    rfl

theorem cell20_658345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_658345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658345 prefixEnd_658345 := by exact prefixLift 658345
  have htrace : WordTrace (prefixWord ++ tailWord_658345) baseStart_658345 baseEnd_658345 := by
    simpa [prefixWord, tailWord_658345, baseEnd_658345] using wordTrace_append hprefix tailTrace_658345
  have hstable : (prefixWord ++ tailWord_658345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658345).length < 2 ^ (prefixWord ++ tailWord_658345).sum := by decide
  have hdescent : baseEnd_658345 < baseStart_658345 := by decide
  rcases family_descends (prefixWord ++ tailWord_658345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658386 : List Nat := [3, 2, 2, 3, 1, 2, 2, 5]
def baseStart_658386 : Nat := 118140960795 + 658386 * 2 ^ 59
def prefixEnd_658386 : Nat := 4983230072969 + 3 ^ 40 * 658386 * 2
def baseEnd_658386 : Nat := 100168436797382606058413

theorem tailTrace_658386 : CollatzResearch.WordTrace tailWord_658386 prefixEnd_658386 100168436797382606058413 := by
  unfold tailWord_658386
  simp only [CollatzResearch.WordTrace]
  refine ⟨6003327548196860055458753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16008873461858293481223341 6003327548196860055458753)
  ·
    refine ⟨4502495661147645041594065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6003327548196860055458753 4502495661147645041594065)
    ·
      refine ⟨3376871745860733781195549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4502495661147645041594065 3376871745860733781195549)
      ·
        refine ⟨1266326904697775167948331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3376871745860733781195549 1266326904697775167948331)
        ·
          refine ⟨1899490357046662751922497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1266326904697775167948331 1899490357046662751922497)
          ·
            refine ⟨1424617767784997063941873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1899490357046662751922497 1424617767784997063941873)
            ·
              refine ⟨1068463325838747797956405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1424617767784997063941873 1068463325838747797956405)
              ·
                refine ⟨100168436797382606058413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1068463325838747797956405 100168436797382606058413)
                ·
                  rfl

theorem cell20_658386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_658386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658386 prefixEnd_658386 := by exact prefixLift 658386
  have htrace : WordTrace (prefixWord ++ tailWord_658386) baseStart_658386 baseEnd_658386 := by
    simpa [prefixWord, tailWord_658386, baseEnd_658386] using wordTrace_append hprefix tailTrace_658386
  have hstable : (prefixWord ++ tailWord_658386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658386).length < 2 ^ (prefixWord ++ tailWord_658386).sum := by decide
  have hdescent : baseEnd_658386 < baseStart_658386 := by decide
  rcases family_descends (prefixWord ++ tailWord_658386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658389 : List Nat := [1, 3, 2, 3, 3, 2, 2, 1, 3]
def baseStart_658389 : Nat := 118140960795 + 658389 * 2 ^ 59
def prefixEnd_658389 : Nat := 4983230072969 + 3 ^ 40 * 658389 * 2
def baseEnd_658389 : Nat := 300506679673893141075227

theorem tailTrace_658389 : CollatzResearch.WordTrace tailWord_658389 prefixEnd_658389 300506679673893141075227 := by
  unfold tailWord_658389
  simp only [CollatzResearch.WordTrace]
  refine ⟨24013419611776571734194221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16008946407851047822796147 24013419611776571734194221)
  ·
    refine ⟨9005032354416214400322833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24013419611776571734194221 9005032354416214400322833)
    ·
      refine ⟨6753774265812160800242125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9005032354416214400322833 6753774265812160800242125)
      ·
        refine ⟨2532665349679560300090797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6753774265812160800242125 2532665349679560300090797)
        ·
          refine ⟨949749506129835112534049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2532665349679560300090797 949749506129835112534049)
          ·
            refine ⟨712312129597376334400537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 949749506129835112534049 712312129597376334400537)
            ·
              refine ⟨534234097198032250800403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 712312129597376334400537 534234097198032250800403)
              ·
                refine ⟨801351145797048376200605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534234097198032250800403 801351145797048376200605)
                ·
                  refine ⟨300506679673893141075227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 801351145797048376200605 300506679673893141075227)
                  ·
                    rfl

theorem cell20_658389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_658389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658389 prefixEnd_658389 := by exact prefixLift 658389
  have htrace : WordTrace (prefixWord ++ tailWord_658389) baseStart_658389 baseEnd_658389 := by
    simpa [prefixWord, tailWord_658389, baseEnd_658389] using wordTrace_append hprefix tailTrace_658389
  have hstable : (prefixWord ++ tailWord_658389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658389).length < 2 ^ (prefixWord ++ tailWord_658389).sum := by decide
  have hdescent : baseEnd_658389 < baseStart_658389 := by decide
  rcases family_descends (prefixWord ++ tailWord_658389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658393 : List Nat := [1, 2, 1, 2, 5, 2, 1, 3, 3]
def baseStart_658393 : Nat := 118140960795 + 658393 * 2 ^ 59
def prefixEnd_658393 : Nat := 4983230072969 + 3 ^ 40 * 658393 * 2
def baseEnd_658393 : Nat := 300508505382886904941877

theorem tailTrace_658393 : CollatzResearch.WordTrace tailWord_658393 prefixEnd_658393 300508505382886904941877 := by
  unfold tailWord_658393
  simp only [CollatzResearch.WordTrace]
  refine ⟨24013565503762080417339833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16009043669174720278226555 24013565503762080417339833)
  ·
    refine ⟨18010174127821560313004875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24013565503762080417339833 18010174127821560313004875)
    ·
      refine ⟨27015261191732340469507313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18010174127821560313004875 27015261191732340469507313)
      ·
        refine ⟨20261445893799255352130485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27015261191732340469507313 20261445893799255352130485)
        ·
          refine ⟨1899510552543680189262233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20261445893799255352130485 1899510552543680189262233)
          ·
            refine ⟨1424632914407760141946675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1899510552543680189262233 1424632914407760141946675)
            ·
              refine ⟨2136949371611640212920013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1424632914407760141946675 2136949371611640212920013)
              ·
                refine ⟨801356014354365079845005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2136949371611640212920013 801356014354365079845005)
                ·
                  refine ⟨300508505382886904941877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 801356014354365079845005 300508505382886904941877)
                  ·
                    rfl

theorem cell20_658393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_658393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658393 prefixEnd_658393 := by exact prefixLift 658393
  have htrace : WordTrace (prefixWord ++ tailWord_658393) baseStart_658393 baseEnd_658393 := by
    simpa [prefixWord, tailWord_658393, baseEnd_658393] using wordTrace_append hprefix tailTrace_658393
  have hstable : (prefixWord ++ tailWord_658393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658393).length < 2 ^ (prefixWord ++ tailWord_658393).sum := by decide
  have hdescent : baseEnd_658393 < baseStart_658393 := by decide
  rcases family_descends (prefixWord ++ tailWord_658393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658407 : List Nat := [1, 1, 5, 2, 2, 1, 2, 6]
def baseStart_658407 : Nat := 118140960795 + 658407 * 2 ^ 59
def prefixEnd_658407 : Nat := 4983230072969 + 3 ^ 40 * 658407 * 2
def baseEnd_658407 : Nat := 100171631788121692825051

theorem tailTrace_658407 : CollatzResearch.WordTrace tailWord_658407 prefixEnd_658407 100171631788121692825051 := by
  unfold tailWord_658407
  simp only [CollatzResearch.WordTrace]
  refine ⟨24014076125711360808349475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16009384083807573872232983 24014076125711360808349475)
  ·
    refine ⟨36021114188567041212524213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24014076125711360808349475 36021114188567041212524213)
    ·
      refine ⟨3376979455178160113674145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36021114188567041212524213 3376979455178160113674145)
      ·
        refine ⟨2532734591383620085255609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3376979455178160113674145 2532734591383620085255609)
        ·
          refine ⟨1899550943537715063941707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2532734591383620085255609 1899550943537715063941707)
          ·
            refine ⟨2849326415306572595912561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1899550943537715063941707 2849326415306572595912561)
            ·
              refine ⟨2136994811479929446934421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2849326415306572595912561 2136994811479929446934421)
              ·
                refine ⟨100171631788121692825051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2136994811479929446934421 100171631788121692825051)
                ·
                  rfl

theorem cell20_658407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 6].length) (baseStart_658407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658407 prefixEnd_658407 := by exact prefixLift 658407
  have htrace : WordTrace (prefixWord ++ tailWord_658407) baseStart_658407 baseEnd_658407 := by
    simpa [prefixWord, tailWord_658407, baseEnd_658407] using wordTrace_append hprefix tailTrace_658407
  have hstable : (prefixWord ++ tailWord_658407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658407).length < 2 ^ (prefixWord ++ tailWord_658407).sum := by decide
  have hdescent : baseEnd_658407 < baseStart_658407 := by decide
  rcases family_descends (prefixWord ++ tailWord_658407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658420 : List Nat := [2, 6, 2, 1, 1, 8]
def baseStart_658420 : Nat := 118140960795 + 658420 * 2 ^ 59
def prefixEnd_658420 : Nat := 4983230072969 + 3 ^ 40 * 658420 * 2
def baseEnd_658420 : Nat := 11130401071059067075621

theorem tailTrace_658420 : CollatzResearch.WordTrace tailWord_658420 prefixEnd_658420 11130401071059067075621 := by
  unfold tailWord_658420
  simp only [CollatzResearch.WordTrace]
  refine ⟨12007275137332132014286357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16009700183109509352381809 12007275137332132014286357)
  ·
    refine ⟨562841022062443688169673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12007275137332132014286357 562841022062443688169673)
    ·
      refine ⟨422130766546832766127255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 562841022062443688169673 422130766546832766127255)
      ·
        refine ⟨633196149820249149190883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422130766546832766127255 633196149820249149190883)
        ·
          refine ⟨949794224730373723786325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633196149820249149190883 949794224730373723786325)
          ·
            refine ⟨11130401071059067075621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 949794224730373723786325 11130401071059067075621)
            ·
              rfl

theorem cell20_658420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 8].length) (baseStart_658420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658420 prefixEnd_658420 := by exact prefixLift 658420
  have htrace : WordTrace (prefixWord ++ tailWord_658420) baseStart_658420 baseEnd_658420 := by
    simpa [prefixWord, tailWord_658420, baseEnd_658420] using wordTrace_append hprefix tailTrace_658420
  have hstable : (prefixWord ++ tailWord_658420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658420).length < 2 ^ (prefixWord ++ tailWord_658420).sum := by decide
  have hdescent : baseEnd_658420 < baseStart_658420 := by decide
  rcases family_descends (prefixWord ++ tailWord_658420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658428 : List Nat := [2, 2, 2, 1, 2, 11]
def baseStart_658428 : Nat := 118140960795 + 658428 * 2 ^ 59
def prefixEnd_658428 : Nat := 4983230072969 + 3 ^ 40 * 658428 * 2
def baseEnd_658428 : Nat := 11130536308762308843521

theorem tailTrace_658428 : CollatzResearch.WordTrace tailWord_658428 prefixEnd_658428 11130536308762308843521 := by
  unfold tailWord_658428
  simp only [CollatzResearch.WordTrace]
  refine ⟨12007421029317640697431969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16009894705756854263242625 12007421029317640697431969)
  ·
    refine ⟨9005565771988230523073977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12007421029317640697431969 9005565771988230523073977)
    ·
      refine ⟨6754174328991172892305483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9005565771988230523073977 6754174328991172892305483)
      ·
        refine ⟨10131261493486759338458225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6754174328991172892305483 10131261493486759338458225)
        ·
          refine ⟨7598446120115069503843669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10131261493486759338458225 7598446120115069503843669)
          ·
            refine ⟨11130536308762308843521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7598446120115069503843669 11130536308762308843521)
            ·
              rfl

theorem cell20_658428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 11].length) (baseStart_658428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658428 prefixEnd_658428 := by exact prefixLift 658428
  have htrace : WordTrace (prefixWord ++ tailWord_658428) baseStart_658428 baseEnd_658428 := by
    simpa [prefixWord, tailWord_658428, baseEnd_658428] using wordTrace_append hprefix tailTrace_658428
  have hstable : (prefixWord ++ tailWord_658428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658428).length < 2 ^ (prefixWord ++ tailWord_658428).sum := by decide
  have hdescent : baseEnd_658428 < baseStart_658428 := by decide
  rcases family_descends (prefixWord ++ tailWord_658428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658430 : List Nat := [4, 2, 2, 2, 2, 2, 2, 2, 2]
def baseStart_658430 : Nat := 118140960795 + 658430 * 2 ^ 59
def prefixEnd_658430 : Nat := 4983230072969 + 3 ^ 40 * 658430 * 2
def baseEnd_658430 : Nat := 300525393191079220708393

theorem tailTrace_658430 : CollatzResearch.WordTrace tailWord_658430 prefixEnd_658430 300525393191079220708393 := by
  unfold tailWord_658430
  simp only [CollatzResearch.WordTrace]
  refine ⟨3001864375578504467054593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16009943336418690490957829 3001864375578504467054593)
  ·
    refine ⟨2251398281683878350290945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3001864375578504467054593 2251398281683878350290945)
    ·
      refine ⟨1688548711262908762718209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2251398281683878350290945 1688548711262908762718209)
      ·
        refine ⟨1266411533447181572038657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1688548711262908762718209 1266411533447181572038657)
        ·
          refine ⟨949808650085386179028993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1266411533447181572038657 949808650085386179028993)
          ·
            refine ⟨712356487564039634271745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 949808650085386179028993 712356487564039634271745)
            ·
              refine ⟨534267365673029725703809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 712356487564039634271745 534267365673029725703809)
              ·
                refine ⟨400700524254772294277857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 534267365673029725703809 400700524254772294277857)
                ·
                  refine ⟨300525393191079220708393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 400700524254772294277857 300525393191079220708393)
                  ·
                    rfl

theorem cell20_658430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_658430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658430 prefixEnd_658430 := by exact prefixLift 658430
  have htrace : WordTrace (prefixWord ++ tailWord_658430) baseStart_658430 baseEnd_658430 := by
    simpa [prefixWord, tailWord_658430, baseEnd_658430] using wordTrace_append hprefix tailTrace_658430
  have hstable : (prefixWord ++ tailWord_658430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658430).length < 2 ^ (prefixWord ++ tailWord_658430).sum := by decide
  have hdescent : baseEnd_658430 < baseStart_658430 := by decide
  rcases family_descends (prefixWord ++ tailWord_658430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658486 : List Nat := [5, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_658486 : Nat := 118140960795 + 658486 * 2 ^ 59
def prefixEnd_658486 : Nat := 4983230072969 + 3 ^ 40 * 658486 * 2
def baseEnd_658486 : Nat := 300550953116991914841497

theorem tailTrace_658486 : CollatzResearch.WordTrace tailWord_658486 prefixEnd_658486 300550953116991914841497 := by
  unfold tailWord_658486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1501059843276572331279707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16011304994950104866983541 1501059843276572331279707)
  ·
    refine ⟨2251589764914858496919561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1501059843276572331279707 2251589764914858496919561)
    ·
      refine ⟨1688692323686143872689671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2251589764914858496919561 1688692323686143872689671)
      ·
        refine ⟨2533038485529215809034507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1688692323686143872689671 2533038485529215809034507)
        ·
          refine ⟨3799557728293823713551761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2533038485529215809034507 3799557728293823713551761)
          ·
            refine ⟨2849668296220367785163821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3799557728293823713551761 2849668296220367785163821)
            ·
              refine ⟨1068625611082637919436433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2849668296220367785163821 1068625611082637919436433)
              ·
                refine ⟨801469208311978439577325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1068625611082637919436433 801469208311978439577325)
                ·
                  refine ⟨300550953116991914841497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 801469208311978439577325 300550953116991914841497)
                  ·
                    rfl

theorem cell20_658486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_658486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658486 prefixEnd_658486 := by exact prefixLift 658486
  have htrace : WordTrace (prefixWord ++ tailWord_658486) baseStart_658486 baseEnd_658486 := by
    simpa [prefixWord, tailWord_658486, baseEnd_658486] using wordTrace_append hprefix tailTrace_658486
  have hstable : (prefixWord ++ tailWord_658486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658486).length < 2 ^ (prefixWord ++ tailWord_658486).sum := by decide
  have hdescent : baseEnd_658486 < baseStart_658486 := by decide
  rcases family_descends (prefixWord ++ tailWord_658486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658493 : List Nat := [1, 4, 1, 3, 1, 2, 2, 4, 2]
def baseStart_658493 : Nat := 118140960795 + 658493 * 2 ^ 59
def prefixEnd_658493 : Nat := 4983230072969 + 3 ^ 40 * 658493 * 2
def baseEnd_658493 : Nat := 300554148107731001608135

theorem tailTrace_658493 : CollatzResearch.WordTrace tailWord_658493 prefixEnd_658493 300554148107731001608135 := by
  unfold tailWord_658493
  simp only [CollatzResearch.WordTrace]
  refine ⟨24017212803399797495980133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16011475202266531663986755 24017212803399797495980133)
  ·
    refine ⟨4503227400637462030496275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24017212803399797495980133 4503227400637462030496275)
    ·
      refine ⟨6754841100956193045744413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4503227400637462030496275 6754841100956193045744413)
      ·
        refine ⟨2533065412858572392154155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6754841100956193045744413 2533065412858572392154155)
        ·
          refine ⟨3799598119287858588231233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2533065412858572392154155 3799598119287858588231233)
          ·
            refine ⟨2849698589465893941173425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3799598119287858588231233 2849698589465893941173425)
            ·
              refine ⟨2137273942099420455880069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2849698589465893941173425 2137273942099420455880069)
              ·
                refine ⟨400738864143641335477513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2137273942099420455880069 400738864143641335477513)
                ·
                  refine ⟨300554148107731001608135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 400738864143641335477513 300554148107731001608135)
                  ·
                    rfl

theorem cell20_658493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 2].length) (baseStart_658493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658493 prefixEnd_658493 := by exact prefixLift 658493
  have htrace : WordTrace (prefixWord ++ tailWord_658493) baseStart_658493 baseEnd_658493 := by
    simpa [prefixWord, tailWord_658493, baseEnd_658493] using wordTrace_append hprefix tailTrace_658493
  have hstable : (prefixWord ++ tailWord_658493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658493).length < 2 ^ (prefixWord ++ tailWord_658493).sum := by decide
  have hdescent : baseEnd_658493 < baseStart_658493 := by decide
  rcases family_descends (prefixWord ++ tailWord_658493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658504 : List Nat := [2, 1, 3, 1, 1, 1, 4, 7]
def baseStart_658504 : Nat := 118140960795 + 658504 * 2 ^ 59
def prefixEnd_658504 : Nat := 4983230072969 + 3 ^ 40 * 658504 * 2
def baseEnd_658504 : Nat := 100186389602487950747141

theorem tailTrace_658504 : CollatzResearch.WordTrace tailWord_658504 prefixEnd_658504 100186389602487950747141 := by
  unfold tailWord_658504
  simp only [CollatzResearch.WordTrace]
  refine ⟨12008807003179973187315283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16011742670906630916420377 12008807003179973187315283)
  ·
    refine ⟨18013210504769959780972925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12008807003179973187315283 18013210504769959780972925)
    ·
      refine ⟨6754953939288734917864847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18013210504769959780972925 6754953939288734917864847)
      ·
        refine ⟨10132430908933102376797271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6754953939288734917864847 10132430908933102376797271)
        ·
          refine ⟨15198646363399653565195907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10132430908933102376797271 15198646363399653565195907)
          ·
            refine ⟨22797969545099480347793861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15198646363399653565195907 22797969545099480347793861)
            ·
              refine ⟨4274619289706152565211349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22797969545099480347793861 4274619289706152565211349)
              ·
                refine ⟨100186389602487950747141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4274619289706152565211349 100186389602487950747141)
                ·
                  rfl

theorem cell20_658504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_658504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658504 prefixEnd_658504 := by exact prefixLift 658504
  have htrace : WordTrace (prefixWord ++ tailWord_658504) baseStart_658504 baseEnd_658504 := by
    simpa [prefixWord, tailWord_658504, baseEnd_658504] using wordTrace_append hprefix tailTrace_658504
  have hstable : (prefixWord ++ tailWord_658504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658504).length < 2 ^ (prefixWord ++ tailWord_658504).sum := by decide
  have hdescent : baseEnd_658504 < baseStart_658504 := by decide
  rcases family_descends (prefixWord ++ tailWord_658504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658511 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 9]
def baseStart_658511 : Nat := 118140960795 + 658511 * 2 ^ 59
def prefixEnd_658511 : Nat := 4983230072969 + 3 ^ 40 * 658511 * 2
def baseEnd_658511 : Nat := 300562363798202939008061

theorem tailTrace_658511 : CollatzResearch.WordTrace tailWord_658511 prefixEnd_658511 300562363798202939008061 := by
  unfold tailWord_658511
  simp only [CollatzResearch.WordTrace]
  refine ⟨24017869317334586570135387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16011912878223057713423591 24017869317334586570135387)
  ·
    refine ⟨36026803976001879855203081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24017869317334586570135387 36026803976001879855203081)
    ·
      refine ⟨27020102982001409891402311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36026803976001879855203081 27020102982001409891402311)
      ·
        refine ⟨40530154473002114837103467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27020102982001409891402311 40530154473002114837103467)
        ·
          refine ⟨60795231709503172255655201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40530154473002114837103467 60795231709503172255655201)
          ·
            refine ⟨45596423782127379191741401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60795231709503172255655201 45596423782127379191741401)
            ·
              refine ⟨34197317836595534393806051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45596423782127379191741401 34197317836595534393806051)
              ·
                refine ⟨51295976754893301590709077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34197317836595534393806051 51295976754893301590709077)
                ·
                  refine ⟨300562363798202939008061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 51295976754893301590709077 300562363798202939008061)
                  ·
                    rfl

theorem cell20_658511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_658511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658511 prefixEnd_658511 := by exact prefixLift 658511
  have htrace : WordTrace (prefixWord ++ tailWord_658511) baseStart_658511 baseEnd_658511 := by
    simpa [prefixWord, tailWord_658511, baseEnd_658511] using wordTrace_append hprefix tailTrace_658511
  have hstable : (prefixWord ++ tailWord_658511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658511).length < 2 ^ (prefixWord ++ tailWord_658511).sum := by decide
  have hdescent : baseEnd_658511 < baseStart_658511 := by decide
  rcases family_descends (prefixWord ++ tailWord_658511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658514 : List Nat := [3, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_658514 : Nat := 118140960795 + 658514 * 2 ^ 59
def prefixEnd_658514 : Nat := 4983230072969 + 3 ^ 40 * 658514 * 2
def baseEnd_658514 : Nat := 300563733079948261908049

theorem tailTrace_658514 : CollatzResearch.WordTrace tailWord_658514 prefixEnd_658514 300563733079948261908049 := by
  unfold tailWord_658514
  simp only [CollatzResearch.WordTrace]
  refine ⟨6004494684080929520623649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16011985824215812054996397 6004494684080929520623649)
  ·
    refine ⟨4503371013060697140467737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6004494684080929520623649 4503371013060697140467737)
    ·
      refine ⟨3377528259795522855350803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4503371013060697140467737 3377528259795522855350803)
      ·
        refine ⟨5066292389693284283026205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3377528259795522855350803 5066292389693284283026205)
        ·
          refine ⟨1899859646134981606134827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5066292389693284283026205 1899859646134981606134827)
          ·
            refine ⟨2849789469202472409202241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1899859646134981606134827 2849789469202472409202241)
            ·
              refine ⟨2137342101901854306901681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2849789469202472409202241 2137342101901854306901681)
              ·
                refine ⟨1603006576426390730176261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2137342101901854306901681 1603006576426390730176261)
                ·
                  refine ⟨300563733079948261908049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1603006576426390730176261 300563733079948261908049)
                  ·
                    rfl

theorem cell20_658514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_658514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658514 prefixEnd_658514 := by exact prefixLift 658514
  have htrace : WordTrace (prefixWord ++ tailWord_658514) baseStart_658514 baseEnd_658514 := by
    simpa [prefixWord, tailWord_658514, baseEnd_658514] using wordTrace_append hprefix tailTrace_658514
  have hstable : (prefixWord ++ tailWord_658514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658514).length < 2 ^ (prefixWord ++ tailWord_658514).sum := by decide
  have hdescent : baseEnd_658514 < baseStart_658514 := by decide
  rcases family_descends (prefixWord ++ tailWord_658514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658552 : List Nat := [2, 1, 2, 1, 1, 1, 4, 6, 2]
def baseStart_658552 : Nat := 118140960795 + 658552 * 2 ^ 59
def prefixEnd_658552 : Nat := 4983230072969 + 3 ^ 40 * 658552 * 2
def baseEnd_658552 : Nat := 300581077315389018641227

theorem tailTrace_658552 : CollatzResearch.WordTrace tailWord_658552 prefixEnd_658552 300581077315389018641227 := by
  unfold tailWord_658552
  simp only [CollatzResearch.WordTrace]
  refine ⟨12009682355093025286188955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16012909806790700381585273 12009682355093025286188955)
  ·
    refine ⟨18014523532639537929283433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12009682355093025286188955 18014523532639537929283433)
    ·
      refine ⟨13510892649479653446962575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18014523532639537929283433 13510892649479653446962575)
      ·
        refine ⟨20266338974219480170443863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13510892649479653446962575 20266338974219480170443863)
        ·
          refine ⟨30399508461329220255665795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20266338974219480170443863 30399508461329220255665795)
          ·
            refine ⟨45599262691993830383498693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30399508461329220255665795 45599262691993830383498693)
            ·
              refine ⟨8549861754748843196906005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45599262691993830383498693 8549861754748843196906005)
              ·
                refine ⟨400774769753852024854969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8549861754748843196906005 400774769753852024854969)
                ·
                  refine ⟨300581077315389018641227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 400774769753852024854969 300581077315389018641227)
                  ·
                    rfl

theorem cell20_658552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 2].length) (baseStart_658552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658552 prefixEnd_658552 := by exact prefixLift 658552
  have htrace : WordTrace (prefixWord ++ tailWord_658552) baseStart_658552 baseEnd_658552 := by
    simpa [prefixWord, tailWord_658552, baseEnd_658552] using wordTrace_append hprefix tailTrace_658552
  have hstable : (prefixWord ++ tailWord_658552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658552).length < 2 ^ (prefixWord ++ tailWord_658552).sum := by decide
  have hdescent : baseEnd_658552 < baseStart_658552 := by decide
  rcases family_descends (prefixWord ++ tailWord_658552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658558 : List Nat := [4, 2, 4, 1, 1, 1, 1, 3, 3]
def baseStart_658558 : Nat := 118140960795 + 658558 * 2 ^ 59
def prefixEnd_658558 : Nat := 4983230072969 + 3 ^ 40 * 658558 * 2
def baseEnd_658558 : Nat := 300583815878879664441203

theorem tailTrace_658558 : CollatzResearch.WordTrace tailWord_658558 prefixEnd_658558 300583815878879664441203 := by
  unfold tailWord_658558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3002447943520539199637041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16013055698776209064730885 3002447943520539199637041)
  ·
    refine ⟨2251835957640404399727781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3002447943520539199637041 2251835957640404399727781)
    ·
      refine ⟨422219242057575824948959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2251835957640404399727781 422219242057575824948959)
      ·
        refine ⟨633328863086363737423439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422219242057575824948959 633328863086363737423439)
        ·
          refine ⟨949993294629545606135159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633328863086363737423439 949993294629545606135159)
          ·
            refine ⟨1424989941944318409202739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 949993294629545606135159 1424989941944318409202739)
            ·
              refine ⟨2137484912916477613804109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1424989941944318409202739 2137484912916477613804109)
              ·
                refine ⟨801556842343679105176541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2137484912916477613804109 801556842343679105176541)
                ·
                  refine ⟨300583815878879664441203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 801556842343679105176541 300583815878879664441203)
                  ·
                    rfl

theorem cell20_658558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_658558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658558 prefixEnd_658558 := by exact prefixLift 658558
  have htrace : WordTrace (prefixWord ++ tailWord_658558) baseStart_658558 baseEnd_658558 := by
    simpa [prefixWord, tailWord_658558, baseEnd_658558] using wordTrace_append hprefix tailTrace_658558
  have hstable : (prefixWord ++ tailWord_658558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658558).length < 2 ^ (prefixWord ++ tailWord_658558).sum := by decide
  have hdescent : baseEnd_658558 < baseStart_658558 := by decide
  rcases family_descends (prefixWord ++ tailWord_658558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658607 : List Nat := [1, 1, 2, 1, 2, 3, 6, 2, 2]
def baseStart_658607 : Nat := 118140960795 + 658607 * 2 ^ 59
def prefixEnd_658607 : Nat := 4983230072969 + 3 ^ 40 * 658607 * 2
def baseEnd_658607 : Nat := 300606180814053271807669

theorem tailTrace_658607 : CollatzResearch.WordTrace tailWord_658607 prefixEnd_658607 300606180814053271807669 := by
  unfold tailWord_658607
  simp only [CollatzResearch.WordTrace]
  refine ⟨24021370724986794965630075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16014247149991196643753383 24021370724986794965630075)
  ·
    refine ⟨36032056087480192448445113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24021370724986794965630075 36032056087480192448445113)
    ·
      refine ⟨27024042065610144336333835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36032056087480192448445113 27024042065610144336333835)
      ·
        refine ⟨40536063098415216504500753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27024042065610144336333835 40536063098415216504500753)
        ·
          refine ⟨30402047323811412378375565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40536063098415216504500753 30402047323811412378375565)
          ·
            refine ⟨11400767746429279641890837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30402047323811412378375565 11400767746429279641890837)
            ·
              refine ⟨534410988113872483213633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11400767746429279641890837 534410988113872483213633)
              ·
                refine ⟨400808241085404362410225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 534410988113872483213633 400808241085404362410225)
                ·
                  refine ⟨300606180814053271807669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 400808241085404362410225 300606180814053271807669)
                  ·
                    rfl

theorem cell20_658607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 2].length) (baseStart_658607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658607 prefixEnd_658607 := by exact prefixLift 658607
  have htrace : WordTrace (prefixWord ++ tailWord_658607) baseStart_658607 baseEnd_658607 := by
    simpa [prefixWord, tailWord_658607, baseEnd_658607] using wordTrace_append hprefix tailTrace_658607
  have hstable : (prefixWord ++ tailWord_658607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658607).length < 2 ^ (prefixWord ++ tailWord_658607).sum := by decide
  have hdescent : baseEnd_658607 < baseStart_658607 := by decide
  rcases family_descends (prefixWord ++ tailWord_658607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658642 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_658642 : Nat := 118140960795 + 658642 * 2 ^ 59
def prefixEnd_658642 : Nat := 4983230072969 + 3 ^ 40 * 658642 * 2
def baseEnd_658642 : Nat := 300622155767748705640859

theorem tailTrace_658642 : CollatzResearch.WordTrace tailWord_658642 prefixEnd_658642 300622155767748705640859 := by
  unfold tailWord_658642
  simp only [CollatzResearch.WordTrace]
  refine ⟨6005661819964998985788545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16015098186573330628769453 6005661819964998985788545)
  ·
    refine ⟨4504246364973749239341409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6005661819964998985788545 4504246364973749239341409)
    ·
      refine ⟨3378184773730311929506057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4504246364973749239341409 3378184773730311929506057)
      ·
        refine ⟨2533638580297733947129543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3378184773730311929506057 2533638580297733947129543)
        ·
          refine ⟨3800457870446600920694315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2533638580297733947129543 3800457870446600920694315)
          ·
            refine ⟨5700686805669901381041473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3800457870446600920694315 5700686805669901381041473)
            ·
              refine ⟨4275515104252426035781105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5700686805669901381041473 4275515104252426035781105)
              ·
                refine ⟨3206636328189319526835829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4275515104252426035781105 3206636328189319526835829)
                ·
                  refine ⟨300622155767748705640859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3206636328189319526835829 300622155767748705640859)
                  ·
                    rfl

theorem cell20_658642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_658642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658642 prefixEnd_658642 := by exact prefixLift 658642
  have htrace : WordTrace (prefixWord ++ tailWord_658642) baseStart_658642 baseEnd_658642 := by
    simpa [prefixWord, tailWord_658642, baseEnd_658642] using wordTrace_append hprefix tailTrace_658642
  have hstable : (prefixWord ++ tailWord_658642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658642).length < 2 ^ (prefixWord ++ tailWord_658642).sum := by decide
  have hdescent : baseEnd_658642 < baseStart_658642 := by decide
  rcases family_descends (prefixWord ++ tailWord_658642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658645 : List Nat := [1, 3, 2, 4, 1, 1, 1, 5, 2]
def baseStart_658645 : Nat := 118140960795 + 658645 * 2 ^ 59
def prefixEnd_658645 : Nat := 4983230072969 + 3 ^ 40 * 658645 * 2
def baseEnd_658645 : Nat := 300623525049494028540847

theorem tailTrace_658645 : CollatzResearch.WordTrace tailWord_658645 prefixEnd_658645 300623525049494028540847 := by
  unfold tailWord_658645
  simp only [CollatzResearch.WordTrace]
  refine ⟨24022756698849127455513389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16015171132566084970342259 24022756698849127455513389)
  ·
    refine ⟨9008533762068422795817521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24022756698849127455513389 9008533762068422795817521)
    ·
      refine ⟨6756400321551317096863141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9008533762068422795817521 6756400321551317096863141)
      ·
        refine ⟨1266825060290871955661839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6756400321551317096863141 1266825060290871955661839)
        ·
          refine ⟨1900237590436307933492759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1266825060290871955661839 1900237590436307933492759)
          ·
            refine ⟨2850356385654461900239139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1900237590436307933492759 2850356385654461900239139)
            ·
              refine ⟨4275534578481692850358709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2850356385654461900239139 4275534578481692850358709)
              ·
                refine ⟨400831366732658704721129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4275534578481692850358709 400831366732658704721129)
                ·
                  refine ⟨300623525049494028540847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 400831366732658704721129 300623525049494028540847)
                  ·
                    rfl

theorem cell20_658645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_658645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658645 prefixEnd_658645 := by exact prefixLift 658645
  have htrace : WordTrace (prefixWord ++ tailWord_658645) baseStart_658645 baseEnd_658645 := by
    simpa [prefixWord, tailWord_658645, baseEnd_658645] using wordTrace_append hprefix tailTrace_658645
  have hstable : (prefixWord ++ tailWord_658645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658645).length < 2 ^ (prefixWord ++ tailWord_658645).sum := by decide
  have hdescent : baseEnd_658645 < baseStart_658645 := by decide
  rcases family_descends (prefixWord ++ tailWord_658645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658656 : List Nat := [2, 1, 1, 3, 1, 5, 7]
def baseStart_658656 : Nat := 118140960795 + 658656 * 2 ^ 59
def prefixEnd_658656 : Nat := 4983230072969 + 3 ^ 40 * 658656 * 2
def baseEnd_658656 : Nat := 33403171749914097686015

theorem tailTrace_658656 : CollatzResearch.WordTrace tailWord_658656 prefixEnd_658656 33403171749914097686015 := by
  unfold tailWord_658656
  simp only [CollatzResearch.WordTrace]
  refine ⟨12011578950904638167081911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16015438601206184222775881 12011578950904638167081911)
  ·
    refine ⟨18017368426356957250622867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12011578950904638167081911 18017368426356957250622867)
    ·
      refine ⟨27026052639535435875934301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18017368426356957250622867 27026052639535435875934301)
      ·
        refine ⟨10134769739825788453475363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27026052639535435875934301 10134769739825788453475363)
        ·
          refine ⟨15202154609738682680213045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10134769739825788453475363 15202154609738682680213045)
          ·
            refine ⟨1425201994663001501269973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15202154609738682680213045 1425201994663001501269973)
            ·
              refine ⟨33403171749914097686015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1425201994663001501269973 33403171749914097686015)
              ·
                rfl

theorem cell20_658656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 7].length) (baseStart_658656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658656 prefixEnd_658656 := by exact prefixLift 658656
  have htrace : WordTrace (prefixWord ++ tailWord_658656) baseStart_658656 baseEnd_658656 := by
    simpa [prefixWord, tailWord_658656, baseEnd_658656] using wordTrace_append hprefix tailTrace_658656
  have hstable : (prefixWord ++ tailWord_658656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658656).length < 2 ^ (prefixWord ++ tailWord_658656).sum := by decide
  have hdescent : baseEnd_658656 < baseStart_658656 := by decide
  rcases family_descends (prefixWord ++ tailWord_658656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658666 : List Nat := [3, 1, 3, 1, 1, 4, 2, 1, 4]
def baseStart_658666 : Nat := 118140960795 + 658666 * 2 ^ 59
def prefixEnd_658666 : Nat := 4983230072969 + 3 ^ 40 * 658666 * 2
def baseEnd_658666 : Nat := 300633110021711288840761

theorem tailTrace_658666 : CollatzResearch.WordTrace tailWord_658666 prefixEnd_658666 300633110021711288840761 := by
  unfold tailWord_658666
  simp only [CollatzResearch.WordTrace]
  refine ⟨6005880657943262010506963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16015681754515365361351901 6005880657943262010506963)
  ·
    refine ⟨9008820986914893015760445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6005880657943262010506963 9008820986914893015760445)
    ·
      refine ⟨3378307870093084880910167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9008820986914893015760445 3378307870093084880910167)
      ·
        refine ⟨5067461805139627321365251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3378307870093084880910167 5067461805139627321365251)
        ·
          refine ⟨7601192707709440982047877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5067461805139627321365251 7601192707709440982047877)
          ·
            refine ⟨1425223632695520184133977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7601192707709440982047877 1425223632695520184133977)
            ·
              refine ⟨1068917724521640138100483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1425223632695520184133977 1068917724521640138100483)
              ·
                refine ⟨1603376586782460207150725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1068917724521640138100483 1603376586782460207150725)
                ·
                  refine ⟨300633110021711288840761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1603376586782460207150725 300633110021711288840761)
                  ·
                    rfl

theorem cell20_658666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_658666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658666 prefixEnd_658666 := by exact prefixLift 658666
  have htrace : WordTrace (prefixWord ++ tailWord_658666) baseStart_658666 baseEnd_658666 := by
    simpa [prefixWord, tailWord_658666, baseEnd_658666] using wordTrace_append hprefix tailTrace_658666
  have hstable : (prefixWord ++ tailWord_658666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658666).length < 2 ^ (prefixWord ++ tailWord_658666).sum := by decide
  have hdescent : baseEnd_658666 < baseStart_658666 := by decide
  rcases family_descends (prefixWord ++ tailWord_658666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658687 : List Nat := [1, 1, 2, 2, 1, 5, 2, 2, 4]
def baseStart_658687 : Nat := 118140960795 + 658687 * 2 ^ 59
def prefixEnd_658687 : Nat := 4983230072969 + 3 ^ 40 * 658687 * 2
def baseEnd_658687 : Nat := 300642694993928549140675

theorem tailTrace_658687 : CollatzResearch.WordTrace tailWord_658687 prefixEnd_658687 300642694993928549140675 := by
  unfold tailWord_658687
  simp only [CollatzResearch.WordTrace]
  refine ⟨24024288564696968628542315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16016192376464645752361543 24024288564696968628542315)
  ·
    refine ⟨36036432847045452942813473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24024288564696968628542315 36036432847045452942813473)
    ·
      refine ⟨27027324635284089707110105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36036432847045452942813473 27027324635284089707110105)
      ·
        refine ⟨20270493476463067280332579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27027324635284089707110105 20270493476463067280332579)
        ·
          refine ⟨30405740214694600920498869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20270493476463067280332579 30405740214694600920498869)
          ·
            refine ⟨2850538145127618836296769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30405740214694600920498869 2850538145127618836296769)
            ·
              refine ⟨2137903608845714127222577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2850538145127618836296769 2137903608845714127222577)
              ·
                refine ⟨1603427706634285595416933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2137903608845714127222577 1603427706634285595416933)
                ·
                  refine ⟨300642694993928549140675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1603427706634285595416933 300642694993928549140675)
                  ·
                    rfl

theorem cell20_658687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 4].length) (baseStart_658687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658687 prefixEnd_658687 := by exact prefixLift 658687
  have htrace : WordTrace (prefixWord ++ tailWord_658687) baseStart_658687 baseEnd_658687 := by
    simpa [prefixWord, tailWord_658687, baseEnd_658687] using wordTrace_append hprefix tailTrace_658687
  have hstable : (prefixWord ++ tailWord_658687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658687).length < 2 ^ (prefixWord ++ tailWord_658687).sum := by decide
  have hdescent : baseEnd_658687 < baseStart_658687 := by decide
  rcases family_descends (prefixWord ++ tailWord_658687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658690 : List Nat := [3, 4, 1, 1, 3, 1, 1, 6]
def baseStart_658690 : Nat := 118140960795 + 658690 * 2 ^ 59
def prefixEnd_658690 : Nat := 4983230072969 + 3 ^ 40 * 658690 * 2
def baseEnd_658690 : Nat := 100214688091891290680221

theorem tailTrace_658690 : CollatzResearch.WordTrace tailWord_658690 prefixEnd_658690 100214688091891290680221 := by
  unfold tailWord_658690
  simp only [CollatzResearch.WordTrace]
  refine ⟨6006099495921525035225381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16016265322457400093934349 6006099495921525035225381)
  ·
    refine ⟨1126143655485285944104759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6006099495921525035225381 1126143655485285944104759)
    ·
      refine ⟨1689215483227928916157139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1126143655485285944104759 1689215483227928916157139)
      ·
        refine ⟨2533823224841893374235709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1689215483227928916157139 2533823224841893374235709)
        ·
          refine ⟨950183709315710015338391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2533823224841893374235709 950183709315710015338391)
          ·
            refine ⟨1425275563973565023007587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950183709315710015338391 1425275563973565023007587)
            ·
              refine ⟨2137913345960347534511381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1425275563973565023007587 2137913345960347534511381)
              ·
                refine ⟨100214688091891290680221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2137913345960347534511381 100214688091891290680221)
                ·
                  rfl

theorem cell20_658690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 6].length) (baseStart_658690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658690 prefixEnd_658690 := by exact prefixLift 658690
  have htrace : WordTrace (prefixWord ++ tailWord_658690) baseStart_658690 baseEnd_658690 := by
    simpa [prefixWord, tailWord_658690, baseEnd_658690] using wordTrace_append hprefix tailTrace_658690
  have hstable : (prefixWord ++ tailWord_658690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658690).length < 2 ^ (prefixWord ++ tailWord_658690).sum := by decide
  have hdescent : baseEnd_658690 < baseStart_658690 := by decide
  rcases family_descends (prefixWord ++ tailWord_658690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658773 : List Nat := [1, 3, 2, 2, 3, 2, 2, 2, 3]
def baseStart_658773 : Nat := 118140960795 + 658773 * 2 ^ 59
def prefixEnd_658773 : Nat := 4983230072969 + 3 ^ 40 * 658773 * 2
def baseEnd_658773 : Nat := 300681947737294472273657

theorem tailTrace_658773 : CollatzResearch.WordTrace tailWord_658773 prefixEnd_658773 300681947737294472273657 := by
  unfold tailWord_658773
  simp only [CollatzResearch.WordTrace]
  refine ⟨24027425242385405316172973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16018283494923603544115315 24027425242385405316172973)
  ·
    refine ⟨9010284465894526993564865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24027425242385405316172973 9010284465894526993564865)
    ·
      refine ⟨6757713349420895245173649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9010284465894526993564865 6757713349420895245173649)
      ·
        refine ⟨5068285012065671433880237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6757713349420895245173649 5068285012065671433880237)
        ·
          refine ⟨1900606879524626787705089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5068285012065671433880237 1900606879524626787705089)
          ·
            refine ⟨1425455159643470090778817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1900606879524626787705089 1425455159643470090778817)
            ·
              refine ⟨1069091369732602568084113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1425455159643470090778817 1069091369732602568084113)
              ·
                refine ⟨801818527299451926063085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1069091369732602568084113 801818527299451926063085)
                ·
                  refine ⟨300681947737294472273657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 801818527299451926063085 300681947737294472273657)
                  ·
                    rfl

theorem cell20_658773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 3].length) (baseStart_658773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658773 prefixEnd_658773 := by exact prefixLift 658773
  have htrace : WordTrace (prefixWord ++ tailWord_658773) baseStart_658773 baseEnd_658773 := by
    simpa [prefixWord, tailWord_658773, baseEnd_658773] using wordTrace_append hprefix tailTrace_658773
  have hstable : (prefixWord ++ tailWord_658773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658773).length < 2 ^ (prefixWord ++ tailWord_658773).sum := by decide
  have hdescent : baseEnd_658773 < baseStart_658773 := by decide
  rcases family_descends (prefixWord ++ tailWord_658773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658777 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 5]
def baseStart_658777 : Nat := 118140960795 + 658777 * 2 ^ 59
def prefixEnd_658777 : Nat := 4983230072969 + 3 ^ 40 * 658777 * 2
def baseEnd_658777 : Nat := 300683773446288236140307

theorem tailTrace_658777 : CollatzResearch.WordTrace tailWord_658777 prefixEnd_658777 300683773446288236140307 := by
  unfold tailWord_658777
  simp only [CollatzResearch.WordTrace]
  refine ⟨24027571134370913999318585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16018380756247275999545723 24027571134370913999318585)
  ·
    refine ⟨18020678350778185499488939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24027571134370913999318585 18020678350778185499488939)
    ·
      refine ⟨27031017526167278249233409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18020678350778185499488939 27031017526167278249233409)
      ·
        refine ⟨20273263144625458686925057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27031017526167278249233409 20273263144625458686925057)
        ·
          refine ⟨15204947358469094015193793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20273263144625458686925057 15204947358469094015193793)
          ·
            refine ⟨11403710518851820511395345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15204947358469094015193793 11403710518851820511395345)
            ·
              refine ⟨8552782889138865383546509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11403710518851820511395345 8552782889138865383546509)
              ·
                refine ⟨3207293583427074518829941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8552782889138865383546509 3207293583427074518829941)
                ·
                  refine ⟨300683773446288236140307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3207293583427074518829941 300683773446288236140307)
                  ·
                    rfl

theorem cell20_658777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_658777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658777 prefixEnd_658777 := by exact prefixLift 658777
  have htrace : WordTrace (prefixWord ++ tailWord_658777) baseStart_658777 baseEnd_658777 := by
    simpa [prefixWord, tailWord_658777, baseEnd_658777] using wordTrace_append hprefix tailTrace_658777
  have hstable : (prefixWord ++ tailWord_658777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658777).length < 2 ^ (prefixWord ++ tailWord_658777).sum := by decide
  have hdescent : baseEnd_658777 < baseStart_658777 := by decide
  rcases family_descends (prefixWord ++ tailWord_658777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658787 : List Nat := [1, 1, 1, 5, 2, 4, 1, 5]
def baseStart_658787 : Nat := 118140960795 + 658787 * 2 ^ 59
def prefixEnd_658787 : Nat := 4983230072969 + 3 ^ 40 * 658787 * 2
def baseEnd_658787 : Nat := 100229445906257548602311

theorem tailTrace_658787 : CollatzResearch.WordTrace tailWord_658787 prefixEnd_658787 100229445906257548602311 := by
  unfold tailWord_658787
  simp only [CollatzResearch.WordTrace]
  refine ⟨24027935864334685707182615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16018623909556457138121743 24027935864334685707182615)
  ·
    refine ⟨36041903796502028560773923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24027935864334685707182615 36041903796502028560773923)
    ·
      refine ⟨54062855694753042841160885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36041903796502028560773923 54062855694753042841160885)
      ·
        refine ⟨5068392721383097766358833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54062855694753042841160885 5068392721383097766358833)
        ·
          refine ⟨3801294541037323324769125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5068392721383097766358833 3801294541037323324769125)
          ·
            refine ⟨712742726444498123394211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3801294541037323324769125 712742726444498123394211)
            ·
              refine ⟨1069114089666747185091317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712742726444498123394211 1069114089666747185091317)
              ·
                refine ⟨100229445906257548602311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1069114089666747185091317 100229445906257548602311)
                ·
                  rfl

theorem cell20_658787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 5].length) (baseStart_658787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658787 prefixEnd_658787 := by exact prefixLift 658787
  have htrace : WordTrace (prefixWord ++ tailWord_658787) baseStart_658787 baseEnd_658787 := by
    simpa [prefixWord, tailWord_658787, baseEnd_658787] using wordTrace_append hprefix tailTrace_658787
  have hstable : (prefixWord ++ tailWord_658787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658787).length < 2 ^ (prefixWord ++ tailWord_658787).sum := by decide
  have hdescent : baseEnd_658787 < baseStart_658787 := by decide
  rcases family_descends (prefixWord ++ tailWord_658787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658891 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 5]
def baseStart_658891 : Nat := 118140960795 + 658891 * 2 ^ 59
def prefixEnd_658891 : Nat := 4983230072969 + 3 ^ 40 * 658891 * 2
def baseEnd_658891 : Nat := 300735806152610506339841

theorem tailTrace_658891 : CollatzResearch.WordTrace tailWord_658891 prefixEnd_658891 300735806152610506339841 := by
  unfold tailWord_658891
  simp only [CollatzResearch.WordTrace]
  refine ⟨24031729055957911468968527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16021152703971940979312351 24031729055957911468968527)
  ·
    refine ⟨36047593583936867203452791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24031729055957911468968527 36047593583936867203452791)
    ·
      refine ⟨54071390375905300805179187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36047593583936867203452791 54071390375905300805179187)
      ·
        refine ⟨81107085563857951207768781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54071390375905300805179187 81107085563857951207768781)
        ·
          refine ⟨30415157086446731702913293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81107085563857951207768781 30415157086446731702913293)
          ·
            refine ⟨11405683907417524388592485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30415157086446731702913293 11405683907417524388592485)
            ·
              refine ⟨2138565732640785822861091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11405683907417524388592485 2138565732640785822861091)
              ·
                refine ⟨3207848598961178734291637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2138565732640785822861091 3207848598961178734291637)
                ·
                  refine ⟨300735806152610506339841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3207848598961178734291637 300735806152610506339841)
                  ·
                    rfl

theorem cell20_658891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 5].length) (baseStart_658891 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658891 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658891 prefixEnd_658891 := by exact prefixLift 658891
  have htrace : WordTrace (prefixWord ++ tailWord_658891) baseStart_658891 baseEnd_658891 := by
    simpa [prefixWord, tailWord_658891, baseEnd_658891] using wordTrace_append hprefix tailTrace_658891
  have hstable : (prefixWord ++ tailWord_658891).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658891).length < 2 ^ (prefixWord ++ tailWord_658891).sum := by decide
  have hdescent : baseEnd_658891 < baseStart_658891 := by decide
  rcases family_descends (prefixWord ++ tailWord_658891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658894 : List Nat := [4, 1, 1, 1, 2, 1, 2, 6, 2]
def baseStart_658894 : Nat := 118140960795 + 658894 * 2 ^ 59
def prefixEnd_658894 : Nat := 4983230072969 + 3 ^ 40 * 658894 * 2
def baseEnd_658894 : Nat := 300737175434355829239829

theorem tailTrace_658894 : CollatzResearch.WordTrace tailWord_658894 prefixEnd_658894 300737175434355829239829 := by
  unfold tailWord_658894
  simp only [CollatzResearch.WordTrace]
  refine ⟨3003979809368380372665967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16021225649964695320885157 3003979809368380372665967)
  ·
    refine ⟨4505969714052570558998951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3003979809368380372665967 4505969714052570558998951)
    ·
      refine ⟨6758954571078855838498427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4505969714052570558998951 6758954571078855838498427)
      ·
        refine ⟨10138431856618283757747641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6758954571078855838498427 10138431856618283757747641)
        ·
          refine ⟨7603823892463712818310731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10138431856618283757747641 7603823892463712818310731)
          ·
            refine ⟨11405735838695569227466097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7603823892463712818310731 11405735838695569227466097)
            ·
              refine ⟨8554301879021676920599573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11405735838695569227466097 8554301879021676920599573)
              ·
                refine ⟨400982900579141105653105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8554301879021676920599573 400982900579141105653105)
                ·
                  refine ⟨300737175434355829239829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 400982900579141105653105 300737175434355829239829)
                  ·
                    rfl

theorem cell20_658894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_658894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658894 prefixEnd_658894 := by exact prefixLift 658894
  have htrace : WordTrace (prefixWord ++ tailWord_658894) baseStart_658894 baseEnd_658894 := by
    simpa [prefixWord, tailWord_658894, baseEnd_658894] using wordTrace_append hprefix tailTrace_658894
  have hstable : (prefixWord ++ tailWord_658894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658894).length < 2 ^ (prefixWord ++ tailWord_658894).sum := by decide
  have hdescent : baseEnd_658894 < baseStart_658894 := by decide
  rcases family_descends (prefixWord ++ tailWord_658894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658945 : List Nat := [1, 2, 4, 1, 5, 1, 2, 2, 2]
def baseStart_658945 : Nat := 118140960795 + 658945 * 2 ^ 59
def prefixEnd_658945 : Nat := 4983230072969 + 3 ^ 40 * 658945 * 2
def baseEnd_658945 : Nat := 300760453224026318539621

theorem tailTrace_658945 : CollatzResearch.WordTrace tailWord_658945 prefixEnd_658945 300760453224026318539621 := by
  unfold tailWord_658945
  simp only [CollatzResearch.WordTrace]
  refine ⟨24033698597762278691434289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16022465731841519127622859 24033698597762278691434289)
  ·
    refine ⟨18025273948321709018575717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24033698597762278691434289 18025273948321709018575717)
    ·
      refine ⟨3379738865310320440982947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18025273948321709018575717 3379738865310320440982947)
      ·
        refine ⟨5069608297965480661474421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3379738865310320440982947 5069608297965480661474421)
        ·
          refine ⟨475275777934263812013227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5069608297965480661474421 475275777934263812013227)
          ·
            refine ⟨712913666901395718019841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475275777934263812013227 712913666901395718019841)
            ·
              refine ⟨534685250176046788514881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 712913666901395718019841 534685250176046788514881)
              ·
                refine ⟨401013937632035091386161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 534685250176046788514881 401013937632035091386161)
                ·
                  refine ⟨300760453224026318539621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401013937632035091386161 300760453224026318539621)
                  ·
                    rfl

theorem cell20_658945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 2].length) (baseStart_658945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658945 prefixEnd_658945 := by exact prefixLift 658945
  have htrace : WordTrace (prefixWord ++ tailWord_658945) baseStart_658945 baseEnd_658945 := by
    simpa [prefixWord, tailWord_658945, baseEnd_658945] using wordTrace_append hprefix tailTrace_658945
  have hstable : (prefixWord ++ tailWord_658945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658945).length < 2 ^ (prefixWord ++ tailWord_658945).sum := by decide
  have hdescent : baseEnd_658945 < baseStart_658945 := by decide
  rcases family_descends (prefixWord ++ tailWord_658945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658956 : List Nat := [2, 2, 1, 2, 6, 1, 1, 5]
def baseStart_658956 : Nat := 118140960795 + 658956 * 2 ^ 59
def prefixEnd_658956 : Nat := 4983230072969 + 3 ^ 40 * 658956 * 2
def baseEnd_658956 : Nat := 100255157974586389724303

theorem tailTrace_658956 : CollatzResearch.WordTrace tailWord_658956 prefixEnd_658956 100255157974586389724303 := by
  unfold tailWord_658956
  simp only [CollatzResearch.WordTrace]
  refine ⟨12017049900361213785042361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16022733200481618380056481 12017049900361213785042361)
  ·
    refine ⟨9012787425270910338781771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12017049900361213785042361 9012787425270910338781771)
    ·
      refine ⟨13519181137906365508172657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9012787425270910338781771 13519181137906365508172657)
      ·
        refine ⟨10139385853429774131129493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13519181137906365508172657 10139385853429774131129493)
        ·
          refine ⟨475283711879520662396695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10139385853429774131129493 475283711879520662396695)
          ·
            refine ⟨712925567819280993595043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475283711879520662396695 712925567819280993595043)
            ·
              refine ⟨1069388351728921490392565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712925567819280993595043 1069388351728921490392565)
              ·
                refine ⟨100255157974586389724303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1069388351728921490392565 100255157974586389724303)
                ·
                  rfl

theorem cell20_658956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 5].length) (baseStart_658956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658956 prefixEnd_658956 := by exact prefixLift 658956
  have htrace : WordTrace (prefixWord ++ tailWord_658956) baseStart_658956 baseEnd_658956 := by
    simpa [prefixWord, tailWord_658956, baseEnd_658956] using wordTrace_append hprefix tailTrace_658956
  have hstable : (prefixWord ++ tailWord_658956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658956).length < 2 ^ (prefixWord ++ tailWord_658956).sum := by decide
  have hdescent : baseEnd_658956 < baseStart_658956 := by decide
  rcases family_descends (prefixWord ++ tailWord_658956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658977 : List Nat := [1, 2, 3, 2, 2, 3, 3, 4]
def baseStart_658977 : Nat := 118140960795 + 658977 * 2 ^ 59
def prefixEnd_658977 : Nat := 4983230072969 + 3 ^ 40 * 658977 * 2
def baseEnd_658977 : Nat := 100258352965325476490941

theorem tailTrace_658977 : CollatzResearch.WordTrace tailWord_658977 prefixEnd_658977 100258352965325476490941 := by
  unfold tailWord_658977
  simp only [CollatzResearch.WordTrace]
  refine ⟨24034865733646348156599185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16023243822430898771066123 24034865733646348156599185)
  ·
    refine ⟨18026149300234761117449389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24034865733646348156599185 18026149300234761117449389)
    ·
      refine ⟨6759805987588035419043521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18026149300234761117449389 6759805987588035419043521)
      ·
        refine ⟨5069854490691026564282641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6759805987588035419043521 5069854490691026564282641)
        ·
          refine ⟨3802390868018269923211981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5069854490691026564282641 3802390868018269923211981)
          ·
            refine ⟨1425896575506851221204493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3802390868018269923211981 1425896575506851221204493)
            ·
              refine ⟨534711215815069207951685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1425896575506851221204493 534711215815069207951685)
              ·
                refine ⟨100258352965325476490941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 534711215815069207951685 100258352965325476490941)
                ·
                  rfl

theorem cell20_658977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 4].length) (baseStart_658977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_658977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_658977 prefixEnd_658977 := by exact prefixLift 658977
  have htrace : WordTrace (prefixWord ++ tailWord_658977) baseStart_658977 baseEnd_658977 := by
    simpa [prefixWord, tailWord_658977, baseEnd_658977] using wordTrace_append hprefix tailTrace_658977
  have hstable : (prefixWord ++ tailWord_658977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658977).length < 2 ^ (prefixWord ++ tailWord_658977).sum := by decide
  have hdescent : baseEnd_658977 < baseStart_658977 := by decide
  rcases family_descends (prefixWord ++ tailWord_658977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659001 : List Nat := [1, 2, 1, 5, 1, 4, 1, 2, 3]
def baseStart_659001 : Nat := 118140960795 + 659001 * 2 ^ 59
def prefixEnd_659001 : Nat := 4983230072969 + 3 ^ 40 * 659001 * 2
def baseEnd_659001 : Nat := 300786013149939012672725

theorem tailTrace_659001 : CollatzResearch.WordTrace tailWord_659001 prefixEnd_659001 300786013149939012672725 := by
  unfold tailWord_659001
  simp only [CollatzResearch.WordTrace]
  refine ⟨24035741085559400255472857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16023827390372933503648571 24035741085559400255472857)
  ·
    refine ⟨18026805814169550191604643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24035741085559400255472857 18026805814169550191604643)
    ·
      refine ⟨27040208721254325287406965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18026805814169550191604643 27040208721254325287406965)
      ·
        refine ⟨2535019567617592995694403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27040208721254325287406965 2535019567617592995694403)
        ·
          refine ⟨3802529351426389493541605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2535019567617592995694403 3802529351426389493541605)
          ·
            refine ⟨712974253392448030039051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3802529351426389493541605 712974253392448030039051)
            ·
              refine ⟨1069461380088672045058577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712974253392448030039051 1069461380088672045058577)
              ·
                refine ⟨802096035066504033793933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1069461380088672045058577 802096035066504033793933)
                ·
                  refine ⟨300786013149939012672725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 802096035066504033793933 300786013149939012672725)
                  ·
                    rfl

theorem cell20_659001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 3].length) (baseStart_659001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659001 prefixEnd_659001 := by exact prefixLift 659001
  have htrace : WordTrace (prefixWord ++ tailWord_659001) baseStart_659001 baseEnd_659001 := by
    simpa [prefixWord, tailWord_659001, baseEnd_659001] using wordTrace_append hprefix tailTrace_659001
  have hstable : (prefixWord ++ tailWord_659001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659001).length < 2 ^ (prefixWord ++ tailWord_659001).sum := by decide
  have hdescent : baseEnd_659001 < baseStart_659001 := by decide
  rcases family_descends (prefixWord ++ tailWord_659001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659019 : List Nat := [1, 1, 1, 1, 3, 1, 3, 9]
def baseStart_659019 : Nat := 118140960795 + 659019 * 2 ^ 59
def prefixEnd_659019 : Nat := 4983230072969 + 3 ^ 40 * 659019 * 2
def baseEnd_659019 : Nat := 100264742946803650024217

theorem tailTrace_659019 : CollatzResearch.WordTrace tailWord_659019 prefixEnd_659019 100264742946803650024217 := by
  unfold tailWord_659019
  simp only [CollatzResearch.WordTrace]
  refine ⟨24036397599494189329628111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16024265066329459553085407 24036397599494189329628111)
  ·
    refine ⟨36054596399241283994442167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24036397599494189329628111 36054596399241283994442167)
    ·
      refine ⟨54081894598861925991663251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36054596399241283994442167 54081894598861925991663251)
      ·
        refine ⟨81122841898292888987494877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54081894598861925991663251 81122841898292888987494877)
        ·
          refine ⟨30421065711859833370310579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81122841898292888987494877 30421065711859833370310579)
          ·
            refine ⟨45631598567789750055465869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30421065711859833370310579 45631598567789750055465869)
            ·
              refine ⟨17111849462921156270799701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45631598567789750055465869 17111849462921156270799701)
              ·
                refine ⟨100264742946803650024217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17111849462921156270799701 100264742946803650024217)
                ·
                  rfl

theorem cell20_659019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 9].length) (baseStart_659019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659019 prefixEnd_659019 := by exact prefixLift 659019
  have htrace : WordTrace (prefixWord ++ tailWord_659019) baseStart_659019 baseEnd_659019 := by
    simpa [prefixWord, tailWord_659019, baseEnd_659019] using wordTrace_append hprefix tailTrace_659019
  have hstable : (prefixWord ++ tailWord_659019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659019).length < 2 ^ (prefixWord ++ tailWord_659019).sum := by decide
  have hdescent : baseEnd_659019 < baseStart_659019 := by decide
  rcases family_descends (prefixWord ++ tailWord_659019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659043 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 5]
def baseStart_659043 : Nat := 118140960795 + 659043 * 2 ^ 59
def prefixEnd_659043 : Nat := 4983230072969 + 3 ^ 40 * 659043 * 2
def baseEnd_659043 : Nat := 300805183094373533272553

theorem tailTrace_659043 : CollatzResearch.WordTrace tailWord_659043 prefixEnd_659043 300805183094373533272553 := by
  unfold tailWord_659043
  simp only [CollatzResearch.WordTrace]
  refine ⟨24037272951407241428501783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16024848634271494285667855 24037272951407241428501783)
  ·
    refine ⟨36055909427110862142752675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24037272951407241428501783 36055909427110862142752675)
    ·
      refine ⟨54083864140666293214129013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36055909427110862142752675 54083864140666293214129013)
      ·
        refine ⟨5070362263187464988824595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54083864140666293214129013 5070362263187464988824595)
        ·
          refine ⟨7605543394781197483236893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5070362263187464988824595 7605543394781197483236893)
          ·
            refine ⟨2852078773042949056213835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7605543394781197483236893 2852078773042949056213835)
            ·
              refine ⟨4278118159564423584320753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2852078773042949056213835 4278118159564423584320753)
              ·
                refine ⟨3208588619673317688240565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4278118159564423584320753 3208588619673317688240565)
                ·
                  refine ⟨300805183094373533272553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3208588619673317688240565 300805183094373533272553)
                  ·
                    rfl

theorem cell20_659043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 5].length) (baseStart_659043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659043 prefixEnd_659043 := by exact prefixLift 659043
  have htrace : WordTrace (prefixWord ++ tailWord_659043) baseStart_659043 baseEnd_659043 := by
    simpa [prefixWord, tailWord_659043, baseEnd_659043] using wordTrace_append hprefix tailTrace_659043
  have hstable : (prefixWord ++ tailWord_659043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659043).length < 2 ^ (prefixWord ++ tailWord_659043).sum := by decide
  have hdescent : baseEnd_659043 < baseStart_659043 := by decide
  rcases family_descends (prefixWord ++ tailWord_659043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659053 : List Nat := [1, 5, 1, 1, 4, 2, 6]
def baseStart_659053 : Nat := 118140960795 + 659053 * 2 ^ 59
def prefixEnd_659053 : Nat := 4983230072969 + 3 ^ 40 * 659053 * 2
def baseEnd_659053 : Nat := 33423305262984215882131

theorem tailTrace_659053 : CollatzResearch.WordTrace tailWord_659053 prefixEnd_659053 33423305262984215882131 := by
  unfold tailWord_659053
  simp only [CollatzResearch.WordTrace]
  refine ⟨24037637681371013136365813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16025091787580675424243875 24037637681371013136365813)
  ·
    refine ⟨2253528532628532481534295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24037637681371013136365813 2253528532628532481534295)
    ·
      refine ⟨3380292798942798722301443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2253528532628532481534295 3380292798942798722301443)
      ·
        refine ⟨5070439198414198083452165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3380292798942798722301443 5070439198414198083452165)
        ·
          refine ⟨950707349702662140647281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5070439198414198083452165 950707349702662140647281)
          ·
            refine ⟨713030512276996605485461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 950707349702662140647281 713030512276996605485461)
            ·
              refine ⟨33423305262984215882131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 713030512276996605485461 33423305262984215882131)
              ·
                rfl

theorem cell20_659053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 6].length) (baseStart_659053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659053 prefixEnd_659053 := by exact prefixLift 659053
  have htrace : WordTrace (prefixWord ++ tailWord_659053) baseStart_659053 baseEnd_659053 := by
    simpa [prefixWord, tailWord_659053, baseEnd_659053] using wordTrace_append hprefix tailTrace_659053
  have hstable : (prefixWord ++ tailWord_659053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659053).length < 2 ^ (prefixWord ++ tailWord_659053).sum := by decide
  have hdescent : baseEnd_659053 < baseStart_659053 := by decide
  rcases family_descends (prefixWord ++ tailWord_659053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659088 : List Nat := [2, 1, 1, 1, 1, 1, 3, 6, 4]
def baseStart_659088 : Nat := 118140960795 + 659088 * 2 ^ 59
def prefixEnd_659088 : Nat := 4983230072969 + 3 ^ 40 * 659088 * 2
def baseEnd_659088 : Nat := 300825722320553376772369

theorem tailTrace_659088 : CollatzResearch.WordTrace tailWord_659088 prefixEnd_659088 300825722320553376772369 := by
  unfold tailWord_659088
  simp only [CollatzResearch.WordTrace]
  refine ⟨12019457118122107056944959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16025942824162809409259945 12019457118122107056944959)
  ·
    refine ⟨18029185677183160585417439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12019457118122107056944959 18029185677183160585417439)
    ·
      refine ⟨27043778515774740878126159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18029185677183160585417439 27043778515774740878126159)
      ·
        refine ⟨40565667773662111317189239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27043778515774740878126159 40565667773662111317189239)
        ·
          refine ⟨60848501660493166975783859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40565667773662111317189239 60848501660493166975783859)
          ·
            refine ⟨91272752490739750463675789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60848501660493166975783859 91272752490739750463675789)
            ·
              refine ⟨34227282184027406423878421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91272752490739750463675789 34227282184027406423878421)
              ·
                refine ⟨1604403852376284676119301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 34227282184027406423878421 1604403852376284676119301)
                ·
                  refine ⟨300825722320553376772369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1604403852376284676119301 300825722320553376772369)
                  ·
                    rfl

theorem cell20_659088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_659088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659088 prefixEnd_659088 := by exact prefixLift 659088
  have htrace : WordTrace (prefixWord ++ tailWord_659088) baseStart_659088 baseEnd_659088 := by
    simpa [prefixWord, tailWord_659088, baseEnd_659088] using wordTrace_append hprefix tailTrace_659088
  have hstable : (prefixWord ++ tailWord_659088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659088).length < 2 ^ (prefixWord ++ tailWord_659088).sum := by decide
  have hdescent : baseEnd_659088 < baseStart_659088 := by decide
  rcases family_descends (prefixWord ++ tailWord_659088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659118 : List Nat := [4, 1, 4, 1, 2, 1, 1, 4, 2]
def baseStart_659118 : Nat := 118140960795 + 659118 * 2 ^ 59
def prefixEnd_659118 : Nat := 4983230072969 + 3 ^ 40 * 659118 * 2
def baseEnd_659118 : Nat := 300839415138006605772247

theorem tailTrace_659118 : CollatzResearch.WordTrace tailWord_659118 prefixEnd_659118 300839415138006605772247 := by
  unfold tailWord_659118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3005001053266941154685251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16026672284090352824988005 3005001053266941154685251)
  ·
    refine ⟨4507501579900411732027877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3005001053266941154685251 4507501579900411732027877)
    ·
      refine ⟨845156546231327199755227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4507501579900411732027877 845156546231327199755227)
      ·
        refine ⟨1267734819346990799632841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 845156546231327199755227 1267734819346990799632841)
        ·
          refine ⟨950801114510243099724631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1267734819346990799632841 950801114510243099724631)
          ·
            refine ⟨1426201671765364649586947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950801114510243099724631 1426201671765364649586947)
            ·
              refine ⟨2139302507648046974380421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1426201671765364649586947 2139302507648046974380421)
              ·
                refine ⟨401119220184008807696329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2139302507648046974380421 401119220184008807696329)
                ·
                  refine ⟨300839415138006605772247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401119220184008807696329 300839415138006605772247)
                  ·
                    rfl

theorem cell20_659118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_659118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659118 prefixEnd_659118 := by exact prefixLift 659118
  have htrace : WordTrace (prefixWord ++ tailWord_659118) baseStart_659118 baseEnd_659118 := by
    simpa [prefixWord, tailWord_659118, baseEnd_659118] using wordTrace_append hprefix tailTrace_659118
  have hstable : (prefixWord ++ tailWord_659118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659118).length < 2 ^ (prefixWord ++ tailWord_659118).sum := by decide
  have hdescent : baseEnd_659118 < baseStart_659118 := by decide
  rcases family_descends (prefixWord ++ tailWord_659118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659160 : List Nat := [2, 1, 2, 2, 3, 1, 4, 3, 2]
def baseStart_659160 : Nat := 118140960795 + 659160 * 2 ^ 59
def prefixEnd_659160 : Nat := 4983230072969 + 3 ^ 40 * 659160 * 2
def baseEnd_659160 : Nat := 300858585082441126372075

theorem tailTrace_659160 : CollatzResearch.WordTrace tailWord_659160 prefixEnd_659160 300858585082441126372075 := by
  unfold tailWord_659160
  simp only [CollatzResearch.WordTrace]
  refine ⟨12020770145991685205255467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16027693527988913607007289 12020770145991685205255467)
  ·
    refine ⟨18031155218987527807883201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12020770145991685205255467 18031155218987527807883201)
    ·
      refine ⟨13523366414240645855912401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18031155218987527807883201 13523366414240645855912401)
      ·
        refine ⟨10142524810680484391934301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13523366414240645855912401 10142524810680484391934301)
        ·
          refine ⟨3803446804005181646975363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10142524810680484391934301 3803446804005181646975363)
          ·
            refine ⟨5705170206007772470463045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3803446804005181646975363 5705170206007772470463045)
            ·
              refine ⟨1069719413626457338211821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5705170206007772470463045 1069719413626457338211821)
              ·
                refine ⟨401144780109921501829433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1069719413626457338211821 401144780109921501829433)
                ·
                  refine ⟨300858585082441126372075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401144780109921501829433 300858585082441126372075)
                  ·
                    rfl

theorem cell20_659160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 2].length) (baseStart_659160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659160 prefixEnd_659160 := by exact prefixLift 659160
  have htrace : WordTrace (prefixWord ++ tailWord_659160) baseStart_659160 baseEnd_659160 := by
    simpa [prefixWord, tailWord_659160, baseEnd_659160] using wordTrace_append hprefix tailTrace_659160
  have hstable : (prefixWord ++ tailWord_659160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659160).length < 2 ^ (prefixWord ++ tailWord_659160).sum := by decide
  have hdescent : baseEnd_659160 < baseStart_659160 := by decide
  rcases family_descends (prefixWord ++ tailWord_659160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659181 : List Nat := [1, 5, 1, 2, 1, 2, 1, 3, 4]
def baseStart_659181 : Nat := 118140960795 + 659181 * 2 ^ 59
def prefixEnd_659181 : Nat := 4983230072969 + 3 ^ 40 * 659181 * 2
def baseEnd_659181 : Nat := 300868170054658386671989

theorem tailTrace_659181 : CollatzResearch.WordTrace tailWord_659181 prefixEnd_659181 300868170054658386671989 := by
  unfold tailWord_659181
  simp only [CollatzResearch.WordTrace]
  refine ⟨24042306224907290997025397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16028204149938193998016931 24042306224907290997025397)
  ·
    refine ⟨2253966208585058530971131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24042306224907290997025397 2253966208585058530971131)
    ·
      refine ⟨3380949312877587796456697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2253966208585058530971131 3380949312877587796456697)
      ·
        refine ⟨2535711984658190847342523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3380949312877587796456697 2535711984658190847342523)
        ·
          refine ⟨3803567976987286271013785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2535711984658190847342523 3803567976987286271013785)
          ·
            refine ⟨2852675982740464703260339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3803567976987286271013785 2852675982740464703260339)
            ·
              refine ⟨4279013974110697054890509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2852675982740464703260339 4279013974110697054890509)
              ·
                refine ⟨1604630240291511395583941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4279013974110697054890509 1604630240291511395583941)
                ·
                  refine ⟨300868170054658386671989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1604630240291511395583941 300868170054658386671989)
                  ·
                    rfl

theorem cell20_659181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_659181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659181 prefixEnd_659181 := by exact prefixLift 659181
  have htrace : WordTrace (prefixWord ++ tailWord_659181) baseStart_659181 baseEnd_659181 := by
    simpa [prefixWord, tailWord_659181, baseEnd_659181] using wordTrace_append hprefix tailTrace_659181
  have hstable : (prefixWord ++ tailWord_659181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659181).length < 2 ^ (prefixWord ++ tailWord_659181).sum := by decide
  have hdescent : baseEnd_659181 < baseStart_659181 := by decide
  rcases family_descends (prefixWord ++ tailWord_659181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659219 : List Nat := [1, 1, 1, 2, 1, 3, 2, 7, 2]
def baseStart_659219 : Nat := 118140960795 + 659219 * 2 ^ 59
def prefixEnd_659219 : Nat := 4983230072969 + 3 ^ 40 * 659219 * 2
def baseEnd_659219 : Nat := 300885514290099143405167

theorem tailTrace_659219 : CollatzResearch.WordTrace tailWord_659219 prefixEnd_659219 300885514290099143405167 := by
  unfold tailWord_659219
  simp only [CollatzResearch.WordTrace]
  refine ⟨24043692198769623486908711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16029128132513082324605807 24043692198769623486908711)
  ·
    refine ⟨36065538298154435230363067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24043692198769623486908711 36065538298154435230363067)
    ·
      refine ⟨54098307447231652845544601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36065538298154435230363067 54098307447231652845544601)
      ·
        refine ⟨40573730585423739634158451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54098307447231652845544601 40573730585423739634158451)
        ·
          refine ⟨60860595878135609451237677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40573730585423739634158451 60860595878135609451237677)
          ·
            refine ⟨22822723454300853544214129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60860595878135609451237677 22822723454300853544214129)
            ·
              refine ⟨17117042590725640158160597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22822723454300853544214129 17117042590725640158160597)
              ·
                refine ⟨401180685720132191206889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 17117042590725640158160597 401180685720132191206889)
                ·
                  refine ⟨300885514290099143405167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401180685720132191206889 300885514290099143405167)
                  ·
                    rfl

theorem cell20_659219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 2].length) (baseStart_659219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659219 prefixEnd_659219 := by exact prefixLift 659219
  have htrace : WordTrace (prefixWord ++ tailWord_659219) baseStart_659219 baseEnd_659219 := by
    simpa [prefixWord, tailWord_659219, baseEnd_659219] using wordTrace_append hprefix tailTrace_659219
  have hstable : (prefixWord ++ tailWord_659219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659219).length < 2 ^ (prefixWord ++ tailWord_659219).sum := by decide
  have hdescent : baseEnd_659219 < baseStart_659219 := by decide
  rcases family_descends (prefixWord ++ tailWord_659219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659226 : List Nat := [3, 1, 1, 3, 2, 4, 6]
def baseStart_659226 : Nat := 118140960795 + 659226 * 2 ^ 59
def prefixEnd_659226 : Nat := 4983230072969 + 3 ^ 40 * 659226 * 2
def baseEnd_659226 : Nat := 33432078808982025574645

theorem tailTrace_659226 : CollatzResearch.WordTrace tailWord_659226 prefixEnd_659226 33432078808982025574645 := by
  unfold tailWord_659226
  simp only [CollatzResearch.WordTrace]
  refine ⟨6010986877436065920603383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16029298339829509121609021 6010986877436065920603383)
  ·
    refine ⟨9016480316154098880905075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6010986877436065920603383 9016480316154098880905075)
    ·
      refine ⟨13524720474231148321357613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9016480316154098880905075 13524720474231148321357613)
      ·
        refine ⟨5071770177836680620509105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13524720474231148321357613 5071770177836680620509105)
        ·
          refine ⟨3803827633377510465381829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5071770177836680620509105 3803827633377510465381829)
          ·
            refine ⟨713217681258283212259093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3803827633377510465381829 713217681258283212259093)
            ·
              refine ⟨33432078808982025574645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 713217681258283212259093 33432078808982025574645)
              ·
                rfl

theorem cell20_659226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 6].length) (baseStart_659226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659226 prefixEnd_659226 := by exact prefixLift 659226
  have htrace : WordTrace (prefixWord ++ tailWord_659226) baseStart_659226 baseEnd_659226 := by
    simpa [prefixWord, tailWord_659226, baseEnd_659226] using wordTrace_append hprefix tailTrace_659226
  have hstable : (prefixWord ++ tailWord_659226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659226).length < 2 ^ (prefixWord ++ tailWord_659226).sum := by decide
  have hdescent : baseEnd_659226 < baseStart_659226 := by decide
  rcases family_descends (prefixWord ++ tailWord_659226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659233 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 5]
def baseStart_659233 : Nat := 118140960795 + 659233 * 2 ^ 59
def prefixEnd_659233 : Nat := 4983230072969 + 3 ^ 40 * 659233 * 2
def baseEnd_659233 : Nat := 300891904271577316938443

theorem tailTrace_659233 : CollatzResearch.WordTrace tailWord_659233 prefixEnd_659233 300891904271577316938443 := by
  unfold tailWord_659233
  simp only [CollatzResearch.WordTrace]
  refine ⟨24044202820718903877918353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16029468547145935918612235 24044202820718903877918353)
  ·
    refine ⟨18033152115539177908438765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24044202820718903877918353 18033152115539177908438765)
    ·
      refine ⟨6762432043327191715664537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18033152115539177908438765 6762432043327191715664537)
      ·
        refine ⟨5071824032495393786748403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6762432043327191715664537 5071824032495393786748403)
        ·
          refine ⟨7607736048743090680122605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5071824032495393786748403 7607736048743090680122605)
          ·
            refine ⟨2852901018278659005045977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7607736048743090680122605 2852901018278659005045977)
            ·
              refine ⟨2139675763708994253784483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2852901018278659005045977 2139675763708994253784483)
              ·
                refine ⟨3209513645563491380676725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2139675763708994253784483 3209513645563491380676725)
                ·
                  refine ⟨300891904271577316938443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3209513645563491380676725 300891904271577316938443)
                  ·
                    rfl

theorem cell20_659233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_659233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659233 prefixEnd_659233 := by exact prefixLift 659233
  have htrace : WordTrace (prefixWord ++ tailWord_659233) baseStart_659233 baseEnd_659233 := by
    simpa [prefixWord, tailWord_659233, baseEnd_659233] using wordTrace_append hprefix tailTrace_659233
  have hstable : (prefixWord ++ tailWord_659233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659233).length < 2 ^ (prefixWord ++ tailWord_659233).sum := by decide
  have hdescent : baseEnd_659233 < baseStart_659233 := by decide
  rcases family_descends (prefixWord ++ tailWord_659233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659236 : List Nat := [2, 3, 1, 3, 2, 3, 1, 1, 4]
def baseStart_659236 : Nat := 118140960795 + 659236 * 2 ^ 59
def prefixEnd_659236 : Nat := 4983230072969 + 3 ^ 40 * 659236 * 2
def baseEnd_659236 : Nat := 300893273553322639838431

theorem tailTrace_659236 : CollatzResearch.WordTrace tailWord_659236 prefixEnd_659236 300893273553322639838431 := by
  unfold tailWord_659236
  simp only [CollatzResearch.WordTrace]
  refine ⟨12022156119854017695138781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16029541493138690260185041 12022156119854017695138781)
  ·
    refine ⟨4508308544945256635677043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12022156119854017695138781 4508308544945256635677043)
    ·
      refine ⟨6762462817417884953515565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4508308544945256635677043 6762462817417884953515565)
      ·
        refine ⟨2535923556531706857568337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6762462817417884953515565 2535923556531706857568337)
        ·
          refine ⟨1901942667398780143176253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2535923556531706857568337 1901942667398780143176253)
          ·
            refine ⟨713228500274542553691095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1901942667398780143176253 713228500274542553691095)
            ·
              refine ⟨1069842750411813830536643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713228500274542553691095 1069842750411813830536643)
              ·
                refine ⟨1604764125617720745804965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069842750411813830536643 1604764125617720745804965)
                ·
                  refine ⟨300893273553322639838431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1604764125617720745804965 300893273553322639838431)
                  ·
                    rfl

theorem cell20_659236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_659236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659236 prefixEnd_659236 := by exact prefixLift 659236
  have htrace : WordTrace (prefixWord ++ tailWord_659236) baseStart_659236 baseEnd_659236 := by
    simpa [prefixWord, tailWord_659236, baseEnd_659236] using wordTrace_append hprefix tailTrace_659236
  have hstable : (prefixWord ++ tailWord_659236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659236).length < 2 ^ (prefixWord ++ tailWord_659236).sum := by decide
  have hdescent : baseEnd_659236 < baseStart_659236 := by decide
  rcases family_descends (prefixWord ++ tailWord_659236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659250 : List Nat := [3, 2, 1, 1, 3, 3, 1, 3, 3]
def baseStart_659250 : Nat := 118140960795 + 659250 * 2 ^ 59
def prefixEnd_659250 : Nat := 4983230072969 + 3 ^ 40 * 659250 * 2
def baseEnd_659250 : Nat := 300899663534800813371707

theorem tailTrace_659250 : CollatzResearch.WordTrace tailWord_659250 prefixEnd_659250 300899663534800813371707 := by
  unfold tailWord_659250
  simp only [CollatzResearch.WordTrace]
  refine ⟨6011205715414328945321801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16029881907771543854191469 6011205715414328945321801)
  ·
    refine ⟨4508404286560746708991351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6011205715414328945321801 4508404286560746708991351)
    ·
      refine ⟨6762606429841120063487027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4508404286560746708991351 6762606429841120063487027)
      ·
        refine ⟨10143909644761680095230541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6762606429841120063487027 10143909644761680095230541)
        ·
          refine ⟨3803966116785630035711453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10143909644761680095230541 3803966116785630035711453)
          ·
            refine ⟨1426487293794611263391795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3803966116785630035711453 1426487293794611263391795)
            ·
              refine ⟨2139730940691916895087693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1426487293794611263391795 2139730940691916895087693)
              ·
                refine ⟨802399102759468835657885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2139730940691916895087693 802399102759468835657885)
                ·
                  refine ⟨300899663534800813371707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 802399102759468835657885 300899663534800813371707)
                  ·
                    rfl

theorem cell20_659250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_659250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659250 prefixEnd_659250 := by exact prefixLift 659250
  have htrace : WordTrace (prefixWord ++ tailWord_659250) baseStart_659250 baseEnd_659250 := by
    simpa [prefixWord, tailWord_659250, baseEnd_659250] using wordTrace_append hprefix tailTrace_659250
  have hstable : (prefixWord ++ tailWord_659250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659250).length < 2 ^ (prefixWord ++ tailWord_659250).sum := by decide
  have hdescent : baseEnd_659250 < baseStart_659250 := by decide
  rcases family_descends (prefixWord ++ tailWord_659250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659285 : List Nat := [1, 3, 2, 2, 2, 10]
def baseStart_659285 : Nat := 118140960795 + 659285 * 2 ^ 59
def prefixEnd_659285 : Nat := 4983230072969 + 3 ^ 40 * 659285 * 2
def baseEnd_659285 : Nat := 11145023647722083229811

theorem tailTrace_659285 : CollatzResearch.WordTrace tailWord_659285 prefixEnd_659285 11145023647722083229811 := by
  unfold tailWord_659285
  simp only [CollatzResearch.WordTrace]
  refine ⟨24046099416530516758811309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16030732944353677839207539 24046099416530516758811309)
  ·
    refine ⟨9017287281198943784554241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24046099416530516758811309 9017287281198943784554241)
    ·
      refine ⟨6762965460899207838415681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9017287281198943784554241 6762965460899207838415681)
      ·
        refine ⟨5072224095674405878811761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6762965460899207838415681 5072224095674405878811761)
        ·
          refine ⟨3804168071755804409108821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5072224095674405878811761 3804168071755804409108821)
          ·
            refine ⟨11145023647722083229811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3804168071755804409108821 11145023647722083229811)
            ·
              rfl

theorem cell20_659285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 10].length) (baseStart_659285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659285 prefixEnd_659285 := by exact prefixLift 659285
  have htrace : WordTrace (prefixWord ++ tailWord_659285) baseStart_659285 baseEnd_659285 := by
    simpa [prefixWord, tailWord_659285, baseEnd_659285] using wordTrace_append hprefix tailTrace_659285
  have hstable : (prefixWord ++ tailWord_659285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659285).length < 2 ^ (prefixWord ++ tailWord_659285).sum := by decide
  have hdescent : baseEnd_659285 < baseStart_659285 := by decide
  rcases family_descends (prefixWord ++ tailWord_659285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659454 : List Nat := [4, 2, 2, 2, 1, 9]
def baseStart_659454 : Nat := 118140960795 + 659454 * 2 ^ 59
def prefixEnd_659454 : Nat := 4983230072969 + 3 ^ 40 * 659454 * 2
def baseEnd_659454 : Nat := 11147880544203065576699

theorem tailTrace_659454 : CollatzResearch.WordTrace tailWord_659454 prefixEnd_659454 11147880544203065576699 := by
  unfold tailWord_659454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3006532919114782327714177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16034842235278839081142277 3006532919114782327714177)
  ·
    refine ⟨2254899689336086745785633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3006532919114782327714177 2254899689336086745785633)
    ·
      refine ⟨1691174767002065059339225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2254899689336086745785633 1691174767002065059339225)
      ·
        refine ⟨1268381075251548794504419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1691174767002065059339225 1268381075251548794504419)
        ·
          refine ⟨1902571612877323191756629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1268381075251548794504419 1902571612877323191756629)
          ·
            refine ⟨11147880544203065576699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1902571612877323191756629 11147880544203065576699)
            ·
              rfl

theorem cell20_659454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 9].length) (baseStart_659454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659454 prefixEnd_659454 := by exact prefixLift 659454
  have htrace : WordTrace (prefixWord ++ tailWord_659454) baseStart_659454 baseEnd_659454 := by
    simpa [prefixWord, tailWord_659454, baseEnd_659454] using wordTrace_append hprefix tailTrace_659454
  have hstable : (prefixWord ++ tailWord_659454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659454).length < 2 ^ (prefixWord ++ tailWord_659454).sum := by decide
  have hdescent : baseEnd_659454 < baseStart_659454 := by decide
  rcases family_descends (prefixWord ++ tailWord_659454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659461 : List Nat := [1, 3, 1, 1, 2, 4, 1, 4, 3]
def baseStart_659461 : Nat := 118140960795 + 659461 * 2 ^ 59
def prefixEnd_659461 : Nat := 4983230072969 + 3 ^ 40 * 659461 * 2
def baseEnd_659461 : Nat := 300995969684221857337511

theorem tailTrace_659461 : CollatzResearch.WordTrace tailWord_659461 prefixEnd_659461 300995969684221857337511 := by
  unfold tailWord_659461
  simp only [CollatzResearch.WordTrace]
  refine ⟨24052518663892898817218237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16035012442595265878145491 24052518663892898817218237)
  ·
    refine ⟨9019694498959837056456839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24052518663892898817218237 9019694498959837056456839)
    ·
      refine ⟨13529541748439755584685259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9019694498959837056456839 13529541748439755584685259)
      ·
        refine ⟨20294312622659633377027889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13529541748439755584685259 20294312622659633377027889)
        ·
          refine ⟨15220734466994725032770917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20294312622659633377027889 15220734466994725032770917)
          ·
            refine ⟨2853887712561510943644547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15220734466994725032770917 2853887712561510943644547)
            ·
              refine ⟨4280831568842266415466821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2853887712561510943644547 4280831568842266415466821)
              ·
                refine ⟨802655919157924952900029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4280831568842266415466821 802655919157924952900029)
                ·
                  refine ⟨300995969684221857337511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 802655919157924952900029 300995969684221857337511)
                  ·
                    rfl

theorem cell20_659461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_659461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659461 prefixEnd_659461 := by exact prefixLift 659461
  have htrace : WordTrace (prefixWord ++ tailWord_659461) baseStart_659461 baseEnd_659461 := by
    simpa [prefixWord, tailWord_659461, baseEnd_659461] using wordTrace_append hprefix tailTrace_659461
  have hstable : (prefixWord ++ tailWord_659461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659461).length < 2 ^ (prefixWord ++ tailWord_659461).sum := by decide
  have hdescent : baseEnd_659461 < baseStart_659461 := by decide
  rcases family_descends (prefixWord ++ tailWord_659461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659468 : List Nat := [2, 2, 1, 2, 3, 1, 2, 3, 4]
def baseStart_659468 : Nat := 118140960795 + 659468 * 2 ^ 59
def prefixEnd_659468 : Nat := 4983230072969 + 3 ^ 40 * 659468 * 2
def baseEnd_659468 : Nat := 300999164674960944104149

theorem tailTrace_659468 : CollatzResearch.WordTrace tailWord_659468 prefixEnd_659468 300999164674960944104149 := by
  unfold tailWord_659468
  simp only [CollatzResearch.WordTrace]
  refine ⟨12026386987433769506361529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16035182649911692675148705 12026386987433769506361529)
  ·
    refine ⟨9019790240575327129771147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12026386987433769506361529 9019790240575327129771147)
    ·
      refine ⟨13529685360862990694656721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9019790240575327129771147 13529685360862990694656721)
      ·
        refine ⟨10147264020647243020992541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13529685360862990694656721 10147264020647243020992541)
        ·
          refine ⟨3805224007742716132872203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10147264020647243020992541 3805224007742716132872203)
          ·
            refine ⟨5707836011614074199308305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3805224007742716132872203 5707836011614074199308305)
            ·
              refine ⟨4280877008710555649481229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5707836011614074199308305 4280877008710555649481229)
              ·
                refine ⟨1605328878266458368555461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4280877008710555649481229 1605328878266458368555461)
                ·
                  refine ⟨300999164674960944104149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1605328878266458368555461 300999164674960944104149)
                  ·
                    rfl

theorem cell20_659468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_659468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659468 prefixEnd_659468 := by exact prefixLift 659468
  have htrace : WordTrace (prefixWord ++ tailWord_659468) baseStart_659468 baseEnd_659468 := by
    simpa [prefixWord, tailWord_659468, baseEnd_659468] using wordTrace_append hprefix tailTrace_659468
  have hstable : (prefixWord ++ tailWord_659468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659468).length < 2 ^ (prefixWord ++ tailWord_659468).sum := by decide
  have hdescent : baseEnd_659468 < baseStart_659468 := by decide
  rcases family_descends (prefixWord ++ tailWord_659468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659475 : List Nat := [1, 1, 1, 2, 1, 4, 5, 5]
def baseStart_659475 : Nat := 118140960795 + 659475 * 2 ^ 59
def prefixEnd_659475 : Nat := 4983230072969 + 3 ^ 40 * 659475 * 2
def baseEnd_659475 : Nat := 100334119888566676956929

theorem tailTrace_659475 : CollatzResearch.WordTrace tailWord_659475 prefixEnd_659475 100334119888566676956929 := by
  unfold tailWord_659475
  simp only [CollatzResearch.WordTrace]
  refine ⟨24053029285842179208227879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16035352857228119472151919 24053029285842179208227879)
  ·
    refine ⟨36079543928763268812341819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24053029285842179208227879 36079543928763268812341819)
    ·
      refine ⟨54119315893144903218512729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36079543928763268812341819 54119315893144903218512729)
      ·
        refine ⟨40589486919858677413884547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54119315893144903218512729 40589486919858677413884547)
        ·
          refine ⟨60884230379788016120826821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40589486919858677413884547 60884230379788016120826821)
          ·
            refine ⟨11415793196210253022655029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60884230379788016120826821 11415793196210253022655029)
            ·
              refine ⟨1070230612144711220873909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11415793196210253022655029 1070230612144711220873909)
              ·
                refine ⟨100334119888566676956929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1070230612144711220873909 100334119888566676956929)
                ·
                  rfl

theorem cell20_659475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 5].length) (baseStart_659475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659475 prefixEnd_659475 := by exact prefixLift 659475
  have htrace : WordTrace (prefixWord ++ tailWord_659475) baseStart_659475 baseEnd_659475 := by
    simpa [prefixWord, tailWord_659475, baseEnd_659475] using wordTrace_append hprefix tailTrace_659475
  have hstable : (prefixWord ++ tailWord_659475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659475).length < 2 ^ (prefixWord ++ tailWord_659475).sum := by decide
  have hdescent : baseEnd_659475 < baseStart_659475 := by decide
  rcases family_descends (prefixWord ++ tailWord_659475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659485 : List Nat := [1, 4, 2, 2, 2, 2, 1, 2, 4]
def baseStart_659485 : Nat := 118140960795 + 659485 * 2 ^ 59
def prefixEnd_659485 : Nat := 4983230072969 + 3 ^ 40 * 659485 * 2
def baseEnd_659485 : Nat := 301006923938184440537413

theorem tailTrace_659485 : CollatzResearch.WordTrace tailWord_659485 prefixEnd_659485 301006923938184440537413 := by
  unfold tailWord_659485
  simp only [CollatzResearch.WordTrace]
  refine ⟨24053394015805950916091909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16035596010537300610727939 24053394015805950916091909)
  ·
    refine ⟨4510011377963615796767233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24053394015805950916091909 4510011377963615796767233)
    ·
      refine ⟨3382508533472711847575425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4510011377963615796767233 3382508533472711847575425)
      ·
        refine ⟨2536881400104533885681569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3382508533472711847575425 2536881400104533885681569)
        ·
          refine ⟨1902661050078400414261177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2536881400104533885681569 1902661050078400414261177)
          ·
            refine ⟨1426995787558800310695883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1902661050078400414261177 1426995787558800310695883)
            ·
              refine ⟨2140493681338200466043825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1426995787558800310695883 2140493681338200466043825)
              ·
                refine ⟨1605370261003650349532869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2140493681338200466043825 1605370261003650349532869)
                ·
                  refine ⟨301006923938184440537413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1605370261003650349532869 301006923938184440537413)
                  ·
                    rfl

theorem cell20_659485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_659485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659485 prefixEnd_659485 := by exact prefixLift 659485
  have htrace : WordTrace (prefixWord ++ tailWord_659485) baseStart_659485 baseEnd_659485 := by
    simpa [prefixWord, tailWord_659485, baseEnd_659485] using wordTrace_append hprefix tailTrace_659485
  have hstable : (prefixWord ++ tailWord_659485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659485).length < 2 ^ (prefixWord ++ tailWord_659485).sum := by decide
  have hdescent : baseEnd_659485 < baseStart_659485 := by decide
  rcases family_descends (prefixWord ++ tailWord_659485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659502 : List Nat := [4, 1, 3, 1, 1, 2, 1, 5, 2]
def baseStart_659502 : Nat := 118140960795 + 659502 * 2 ^ 59
def prefixEnd_659502 : Nat := 4983230072969 + 3 ^ 40 * 659502 * 2
def baseEnd_659502 : Nat := 301014683201407936970677

theorem tailTrace_659502 : CollatzResearch.WordTrace tailWord_659502 prefixEnd_659502 301014683201407936970677 := by
  unfold tailWord_659502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3006751757093045352432595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16036009371162908546307173 3006751757093045352432595)
  ·
    refine ⟨4510127635639568028648893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3006751757093045352432595 4510127635639568028648893)
    ·
      refine ⟨1691297863364838010743335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4510127635639568028648893 1691297863364838010743335)
      ·
        refine ⟨2536946795047257016115003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1691297863364838010743335 2536946795047257016115003)
        ·
          refine ⟨3805420192570885524172505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2536946795047257016115003 3805420192570885524172505)
          ·
            refine ⟨2854065144428164143129379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3805420192570885524172505 2854065144428164143129379)
            ·
              refine ⟨4281097716642246214694069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2854065144428164143129379 4281097716642246214694069)
              ·
                refine ⟨401352910935210582627569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4281097716642246214694069 401352910935210582627569)
                ·
                  refine ⟨301014683201407936970677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401352910935210582627569 301014683201407936970677)
                  ·
                    rfl

theorem cell20_659502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_659502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659502 prefixEnd_659502 := by exact prefixLift 659502
  have htrace : WordTrace (prefixWord ++ tailWord_659502) baseStart_659502 baseEnd_659502 := by
    simpa [prefixWord, tailWord_659502, baseEnd_659502] using wordTrace_append hprefix tailTrace_659502
  have hstable : (prefixWord ++ tailWord_659502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659502).length < 2 ^ (prefixWord ++ tailWord_659502).sum := by decide
  have hdescent : baseEnd_659502 < baseStart_659502 := by decide
  rcases family_descends (prefixWord ++ tailWord_659502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659533 : List Nat := [1, 6, 1, 1, 1, 1, 5, 1, 3]
def baseStart_659533 : Nat := 118140960795 + 659533 * 2 ^ 59
def prefixEnd_659533 : Nat := 4983230072969 + 3 ^ 40 * 659533 * 2
def baseEnd_659533 : Nat := 301028832446109606937217

theorem tailTrace_659533 : CollatzResearch.WordTrace tailWord_659533 prefixEnd_659533 301028832446109606937217 := by
  unfold tailWord_659533
  simp only [CollatzResearch.WordTrace]
  refine ⟨24055144719632055113839253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16036763146421370075892835 24055144719632055113839253)
  ·
    refine ⟨1127584908732752583461215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24055144719632055113839253 1127584908732752583461215)
    ·
      refine ⟨1691377363099128875191823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1127584908732752583461215 1691377363099128875191823)
      ·
        refine ⟨2537066044648693312787735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1691377363099128875191823 2537066044648693312787735)
        ·
          refine ⟨3805599066973039969181603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2537066044648693312787735 3805599066973039969181603)
          ·
            refine ⟨5708398600459559953772405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3805599066973039969181603 5708398600459559953772405)
            ·
              refine ⟨535162368793083745666163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5708398600459559953772405 535162368793083745666163)
              ·
                refine ⟨802743553189625618499245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535162368793083745666163 802743553189625618499245)
                ·
                  refine ⟨301028832446109606937217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 802743553189625618499245 301028832446109606937217)
                  ·
                    rfl

theorem cell20_659533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_659533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659533 prefixEnd_659533 := by exact prefixLift 659533
  have htrace : WordTrace (prefixWord ++ tailWord_659533) baseStart_659533 baseEnd_659533 := by
    simpa [prefixWord, tailWord_659533, baseEnd_659533] using wordTrace_append hprefix tailTrace_659533
  have hstable : (prefixWord ++ tailWord_659533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659533).length < 2 ^ (prefixWord ++ tailWord_659533).sum := by decide
  have hdescent : baseEnd_659533 < baseStart_659533 := by decide
  rcases family_descends (prefixWord ++ tailWord_659533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659544 : List Nat := [2, 1, 2, 2, 1, 4, 2, 2, 4]
def baseStart_659544 : Nat := 118140960795 + 659544 * 2 ^ 59
def prefixEnd_659544 : Nat := 4983230072969 + 3 ^ 40 * 659544 * 2
def baseEnd_659544 : Nat := 301033853145842457570505

theorem tailTrace_659544 : CollatzResearch.WordTrace tailWord_659544 prefixEnd_659544 301033853145842457570505 := by
  unfold tailWord_659544
  simp only [CollatzResearch.WordTrace]
  refine ⟨12027772961296101996244843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16037030615061469328326457 12027772961296101996244843)
  ·
    refine ⟨18041659441944152994367265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12027772961296101996244843 18041659441944152994367265)
    ·
      refine ⟨13531244581458114745775449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18041659441944152994367265 13531244581458114745775449)
      ·
        refine ⟨10148433436093586059331587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13531244581458114745775449 10148433436093586059331587)
        ·
          refine ⟨15222650154140379088997381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10148433436093586059331587 15222650154140379088997381)
          ·
            refine ⟨2854246903901321079187009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15222650154140379088997381 2854246903901321079187009)
            ·
              refine ⟨2140685177925990809390257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2854246903901321079187009 2140685177925990809390257)
              ·
                refine ⟨1605513883444493107042693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2140685177925990809390257 1605513883444493107042693)
                ·
                  refine ⟨301033853145842457570505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1605513883444493107042693 301033853145842457570505)
                  ·
                    rfl

theorem cell20_659544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_659544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659544 prefixEnd_659544 := by exact prefixLift 659544
  have htrace : WordTrace (prefixWord ++ tailWord_659544) baseStart_659544 baseEnd_659544 := by
    simpa [prefixWord, tailWord_659544, baseEnd_659544] using wordTrace_append hprefix tailTrace_659544
  have hstable : (prefixWord ++ tailWord_659544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659544).length < 2 ^ (prefixWord ++ tailWord_659544).sum := by decide
  have hdescent : baseEnd_659544 < baseStart_659544 := by decide
  rcases family_descends (prefixWord ++ tailWord_659544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659589 : List Nat := [1, 3, 1, 1, 5, 1, 1, 7]
def baseStart_659589 : Nat := 118140960795 + 659589 * 2 ^ 59
def prefixEnd_659589 : Nat := 4983230072969 + 3 ^ 40 * 659589 * 2
def baseEnd_659589 : Nat := 100351464124007433690107

theorem tailTrace_659589 : CollatzResearch.WordTrace tailWord_659589 prefixEnd_659589 100351464124007433690107 := by
  unfold tailWord_659589
  simp only [CollatzResearch.WordTrace]
  refine ⟨24057187207429176677877821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16038124804952784451918547 24057187207429176677877821)
  ·
    refine ⟨9021445202785941254204183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24057187207429176677877821 9021445202785941254204183)
    ·
      refine ⟨13532167804178911881306275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9021445202785941254204183 13532167804178911881306275)
      ·
        refine ⟨20298251706268367821959413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13532167804178911881306275 20298251706268367821959413)
        ·
          refine ⟨1902961097462659483308695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20298251706268367821959413 1902961097462659483308695)
          ·
            refine ⟨2854441646193989224963043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1902961097462659483308695 2854441646193989224963043)
            ·
              refine ⟨4281662469290983837444565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2854441646193989224963043 4281662469290983837444565)
              ·
                refine ⟨100351464124007433690107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4281662469290983837444565 100351464124007433690107)
                ·
                  rfl

theorem cell20_659589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 7].length) (baseStart_659589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659589 prefixEnd_659589 := by exact prefixLift 659589
  have htrace : WordTrace (prefixWord ++ tailWord_659589) baseStart_659589 baseEnd_659589 := by
    simpa [prefixWord, tailWord_659589, baseEnd_659589] using wordTrace_append hprefix tailTrace_659589
  have hstable : (prefixWord ++ tailWord_659589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659589).length < 2 ^ (prefixWord ++ tailWord_659589).sum := by decide
  have hdescent : baseEnd_659589 < baseStart_659589 := by decide
  rcases family_descends (prefixWord ++ tailWord_659589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659592 : List Nat := [2, 1, 3, 4, 1, 2, 1, 3, 3]
def baseStart_659592 : Nat := 118140960795 + 659592 * 2 ^ 59
def prefixEnd_659592 : Nat := 4983230072969 + 3 ^ 40 * 659592 * 2
def baseEnd_659592 : Nat := 301055761653767623970309

theorem tailTrace_659592 : CollatzResearch.WordTrace tailWord_659592 prefixEnd_659592 301055761653767623970309 := by
  unfold tailWord_659592
  simp only [CollatzResearch.WordTrace]
  refine ⟨12028648313209154095118515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16038197750945538793491353 12028648313209154095118515)
  ·
    refine ⟨18042972469813731142677773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12028648313209154095118515 18042972469813731142677773)
    ·
      refine ⟨6766114676180149178504165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18042972469813731142677773 6766114676180149178504165)
      ·
        refine ⟨1268646501783777970969531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6766114676180149178504165 1268646501783777970969531)
        ·
          refine ⟨1902969752675666956454297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1268646501783777970969531 1902969752675666956454297)
          ·
            refine ⟨1427227314506750217340723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1902969752675666956454297 1427227314506750217340723)
            ·
              refine ⟨2140840971760125326011085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1427227314506750217340723 2140840971760125326011085)
              ·
                refine ⟨802815364410046997254157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2140840971760125326011085 802815364410046997254157)
                ·
                  refine ⟨301055761653767623970309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 802815364410046997254157 301055761653767623970309)
                  ·
                    rfl

theorem cell20_659592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_659592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659592 prefixEnd_659592 := by exact prefixLift 659592
  have htrace : WordTrace (prefixWord ++ tailWord_659592) baseStart_659592 baseEnd_659592 := by
    simpa [prefixWord, tailWord_659592, baseEnd_659592] using wordTrace_append hprefix tailTrace_659592
  have hstable : (prefixWord ++ tailWord_659592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659592).length < 2 ^ (prefixWord ++ tailWord_659592).sum := by decide
  have hdescent : baseEnd_659592 < baseStart_659592 := by decide
  rcases family_descends (prefixWord ++ tailWord_659592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659603 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 6]
def baseStart_659603 : Nat := 118140960795 + 659603 * 2 ^ 59
def prefixEnd_659603 : Nat := 4983230072969 + 3 ^ 40 * 659603 * 2
def baseEnd_659603 : Nat := 301060782353500474603597

theorem tailTrace_659603 : CollatzResearch.WordTrace tailWord_659603 prefixEnd_659603 301060782353500474603597 := by
  unfold tailWord_659603
  simp only [CollatzResearch.WordTrace]
  refine ⟨24057697829378457068887463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16038465219585638045924975 24057697829378457068887463)
  ·
    refine ⟨36086546744067685603331195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24057697829378457068887463 36086546744067685603331195)
    ·
      refine ⟨54129820116101528404996793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36086546744067685603331195 54129820116101528404996793)
      ·
        refine ⟨40597365087076146303747595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54129820116101528404996793 40597365087076146303747595)
        ·
          refine ⟨60896047630614219455621393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40597365087076146303747595 60896047630614219455621393)
          ·
            refine ⟨45672035722960664591716045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60896047630614219455621393 45672035722960664591716045)
            ·
              refine ⟨17127013396110249221893517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45672035722960664591716045 17127013396110249221893517)
              ·
                refine ⟨6422630023541343458210069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17127013396110249221893517 6422630023541343458210069)
                ·
                  refine ⟨301060782353500474603597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6422630023541343458210069 301060782353500474603597)
                  ·
                    rfl

theorem cell20_659603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_659603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659603 prefixEnd_659603 := by exact prefixLift 659603
  have htrace : WordTrace (prefixWord ++ tailWord_659603) baseStart_659603 baseEnd_659603 := by
    simpa [prefixWord, tailWord_659603, baseEnd_659603] using wordTrace_append hprefix tailTrace_659603
  have hstable : (prefixWord ++ tailWord_659603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659603).length < 2 ^ (prefixWord ++ tailWord_659603).sum := by decide
  have hdescent : baseEnd_659603 < baseStart_659603 := by decide
  rcases family_descends (prefixWord ++ tailWord_659603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659636 : List Nat := [2, 5, 3, 1, 2, 1, 1, 5]
def baseStart_659636 : Nat := 118140960795 + 659636 * 2 ^ 59
def prefixEnd_659636 : Nat := 4983230072969 + 3 ^ 40 * 659636 * 2
def baseEnd_659636 : Nat := 100358614817566342167821

theorem tailTrace_659636 : CollatzResearch.WordTrace tailWord_659636 prefixEnd_659636 100358614817566342167821 := by
  unfold tailWord_659636
  simp only [CollatzResearch.WordTrace]
  refine ⟨12029450719129451852419381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16039267625505935803225841 12029450719129451852419381)
  ·
    refine ⟨1127761004918386111164317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12029450719129451852419381 1127761004918386111164317)
    ·
      refine ⟨422910376844394791686619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1127761004918386111164317 422910376844394791686619)
      ·
        refine ⟨634365565266592187529929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422910376844394791686619 634365565266592187529929)
        ·
          refine ⟨475774173949944140647447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 634365565266592187529929 475774173949944140647447)
          ·
            refine ⟨713661260924916210971171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475774173949944140647447 713661260924916210971171)
            ·
              refine ⟨1070491891387374316456757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713661260924916210971171 1070491891387374316456757)
              ·
                refine ⟨100358614817566342167821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1070491891387374316456757 100358614817566342167821)
                ·
                  rfl

theorem cell20_659636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 5].length) (baseStart_659636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659636 prefixEnd_659636 := by exact prefixLift 659636
  have htrace : WordTrace (prefixWord ++ tailWord_659636) baseStart_659636 baseEnd_659636 := by
    simpa [prefixWord, tailWord_659636, baseEnd_659636] using wordTrace_append hprefix tailTrace_659636
  have hstable : (prefixWord ++ tailWord_659636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659636).length < 2 ^ (prefixWord ++ tailWord_659636).sum := by decide
  have hdescent : baseEnd_659636 < baseStart_659636 := by decide
  rcases family_descends (prefixWord ++ tailWord_659636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659658 : List Nat := [3, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_659658 : Nat := 118140960795 + 659658 * 2 ^ 59
def prefixEnd_659658 : Nat := 4983230072969 + 3 ^ 40 * 659658 * 2
def baseEnd_659658 : Nat := 301085885852164727770039

theorem tailTrace_659658 : CollatzResearch.WordTrace tailWord_659658 prefixEnd_659658 301085885852164727770039 := by
  unfold tailWord_659658
  simp only [CollatzResearch.WordTrace]
  refine ⟨6014925961044800365534907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16039802562786134308093085 6014925961044800365534907)
  ·
    refine ⟨9022388941567200548302361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6014925961044800365534907 9022388941567200548302361)
    ·
      refine ⟨6766791706175400411226771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9022388941567200548302361 6766791706175400411226771)
      ·
        refine ⟨10150187559263100616840157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6766791706175400411226771 10150187559263100616840157)
        ·
          refine ⟨3806320334723662731315059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10150187559263100616840157 3806320334723662731315059)
          ·
            refine ⟨5709480502085494096972589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3806320334723662731315059 5709480502085494096972589)
            ·
              refine ⟨2141055188282060286364721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5709480502085494096972589 2141055188282060286364721)
              ·
                refine ⟨1605791391211545214773541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2141055188282060286364721 1605791391211545214773541)
                ·
                  refine ⟨301085885852164727770039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1605791391211545214773541 301085885852164727770039)
                  ·
                    rfl

theorem cell20_659658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_659658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659658 prefixEnd_659658 := by exact prefixLift 659658
  have htrace : WordTrace (prefixWord ++ tailWord_659658) baseStart_659658 baseEnd_659658 := by
    simpa [prefixWord, tailWord_659658, baseEnd_659658] using wordTrace_append hprefix tailTrace_659658
  have hstable : (prefixWord ++ tailWord_659658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659658).length < 2 ^ (prefixWord ++ tailWord_659658).sum := by decide
  have hdescent : baseEnd_659658 < baseStart_659658 := by decide
  rcases family_descends (prefixWord ++ tailWord_659658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659679 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 8]
def baseStart_659679 : Nat := 118140960795 + 659679 * 2 ^ 59
def prefixEnd_659679 : Nat := 4983230072969 + 3 ^ 40 * 659679 * 2
def baseEnd_659679 : Nat := 301095470824381988069953

theorem tailTrace_659679 : CollatzResearch.WordTrace tailWord_659679 prefixEnd_659679 301095470824381988069953 := by
  unfold tailWord_659679
  simp only [CollatzResearch.WordTrace]
  refine ⟨24060469777103122048654091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16040313184735414699102727 24060469777103122048654091)
  ·
    refine ⟨36090704665654683072981137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24060469777103122048654091 36090704665654683072981137)
    ·
      refine ⟨27068028499241012304735853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36090704665654683072981137 27068028499241012304735853)
      ·
        refine ⟨10150510687215379614275945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27068028499241012304735853 10150510687215379614275945)
        ·
          refine ⟨7612883015411534710706959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10150510687215379614275945 7612883015411534710706959)
          ·
            refine ⟨11419324523117302066060439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7612883015411534710706959 11419324523117302066060439)
            ·
              refine ⟨17128986784675953099090659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11419324523117302066060439 17128986784675953099090659)
              ·
                refine ⟨25693480177013929648635989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17128986784675953099090659 25693480177013929648635989)
                ·
                  refine ⟨301095470824381988069953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25693480177013929648635989 301095470824381988069953)
                  ·
                    rfl

theorem cell20_659679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_659679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659679 prefixEnd_659679 := by exact prefixLift 659679
  have htrace : WordTrace (prefixWord ++ tailWord_659679) baseStart_659679 baseEnd_659679 := by
    simpa [prefixWord, tailWord_659679, baseEnd_659679] using wordTrace_append hprefix tailTrace_659679
  have hstable : (prefixWord ++ tailWord_659679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659679).length < 2 ^ (prefixWord ++ tailWord_659679).sum := by decide
  have hdescent : baseEnd_659679 < baseStart_659679 := by decide
  rcases family_descends (prefixWord ++ tailWord_659679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659706 : List Nat := [3, 1, 1, 1, 1, 6, 3, 1, 3]
def baseStart_659706 : Nat := 118140960795 + 659706 * 2 ^ 59
def prefixEnd_659706 : Nat := 4983230072969 + 3 ^ 40 * 659706 * 2
def baseEnd_659706 : Nat := 301107794360089894169843

theorem tailTrace_659706 : CollatzResearch.WordTrace tailWord_659706 prefixEnd_659706 301107794360089894169843 := by
  unfold tailWord_659706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6015363637001326414971743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16040969698670203773257981 6015363637001326414971743)
  ·
    refine ⟨9023045455501989622457615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6015363637001326414971743 9023045455501989622457615)
    ·
      refine ⟨13534568183252984433686423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9023045455501989622457615 13534568183252984433686423)
      ·
        refine ⟨20301852274879476650529635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13534568183252984433686423 20301852274879476650529635)
        ·
          refine ⟨30452778412319214975794453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20301852274879476650529635 30452778412319214975794453)
          ·
            refine ⟨1427473988077463201990365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30452778412319214975794453 1427473988077463201990365)
            ·
              refine ⟨535302745529048700746387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1427473988077463201990365 535302745529048700746387)
              ·
                refine ⟨802954118293573051119581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535302745529048700746387 802954118293573051119581)
                ·
                  refine ⟨301107794360089894169843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 802954118293573051119581 301107794360089894169843)
                  ·
                    rfl

theorem cell20_659706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_659706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659706 prefixEnd_659706 := by exact prefixLift 659706
  have htrace : WordTrace (prefixWord ++ tailWord_659706) baseStart_659706 baseEnd_659706 := by
    simpa [prefixWord, tailWord_659706, baseEnd_659706] using wordTrace_append hprefix tailTrace_659706
  have hstable : (prefixWord ++ tailWord_659706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659706).length < 2 ^ (prefixWord ++ tailWord_659706).sum := by decide
  have hdescent : baseEnd_659706 < baseStart_659706 := by decide
  rcases family_descends (prefixWord ++ tailWord_659706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659716 : List Nat := [2, 3, 2, 2, 4, 1, 2, 4]
def baseStart_659716 : Nat := 118140960795 + 659716 * 2 ^ 59
def prefixEnd_659716 : Nat := 4983230072969 + 3 ^ 40 * 659716 * 2
def baseEnd_659716 : Nat := 100370786210858101278823

theorem tailTrace_659716 : CollatzResearch.WordTrace tailWord_659716 prefixEnd_659716 100370786210858101278823 := by
  unfold tailWord_659716
  simp only [CollatzResearch.WordTrace]
  refine ⟨12030909638984538683875501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16041212851979384911834001 12030909638984538683875501)
  ·
    refine ⟨4511591114619202006453313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12030909638984538683875501 4511591114619202006453313)
    ·
      refine ⟨3383693335964401504839985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4511591114619202006453313 3383693335964401504839985)
      ·
        refine ⟨2537770001973301128629989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3383693335964401504839985 2537770001973301128629989)
        ·
          refine ⟨475831875369993961618123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2537770001973301128629989 475831875369993961618123)
          ·
            refine ⟨713747813054990942427185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475831875369993961618123 713747813054990942427185)
            ·
              refine ⟨535310859791243206820389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 713747813054990942427185 535310859791243206820389)
              ·
                refine ⟨100370786210858101278823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 535310859791243206820389 100370786210858101278823)
                ·
                  rfl

theorem cell20_659716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 4].length) (baseStart_659716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659716 prefixEnd_659716 := by exact prefixLift 659716
  have htrace : WordTrace (prefixWord ++ tailWord_659716) baseStart_659716 baseEnd_659716 := by
    simpa [prefixWord, tailWord_659716, baseEnd_659716] using wordTrace_append hprefix tailTrace_659716
  have hstable : (prefixWord ++ tailWord_659716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659716).length < 2 ^ (prefixWord ++ tailWord_659716).sum := by decide
  have hdescent : baseEnd_659716 < baseStart_659716 := by decide
  rcases family_descends (prefixWord ++ tailWord_659716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659717 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 6]
def baseStart_659717 : Nat := 118140960795 + 659717 * 2 ^ 59
def prefixEnd_659717 : Nat := 4983230072969 + 3 ^ 40 * 659717 * 2
def baseEnd_659717 : Nat := 301112815059822744803131

theorem tailTrace_659717 : CollatzResearch.WordTrace tailWord_659717 prefixEnd_659717 301112815059822744803131 := by
  unfold tailWord_659717
  simp only [CollatzResearch.WordTrace]
  refine ⟨24061855750965454538537405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16041237167310303025691603 24061855750965454538537405)
  ·
    refine ⟨9023195906612045451951527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24061855750965454538537405 9023195906612045451951527)
    ·
      refine ⟨13534793859918068177927291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9023195906612045451951527 13534793859918068177927291)
      ·
        refine ⟨20302190789877102266890937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13534793859918068177927291 20302190789877102266890937)
        ·
          refine ⟨15226643092407826700168203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20302190789877102266890937 15226643092407826700168203)
          ·
            refine ⟨22839964638611740050252305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15226643092407826700168203 22839964638611740050252305)
            ·
              refine ⟨17129973478958805037689229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22839964638611740050252305 17129973478958805037689229)
              ·
                refine ⟨6423740054609551889133461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17129973478958805037689229 6423740054609551889133461)
                ·
                  refine ⟨301112815059822744803131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6423740054609551889133461 301112815059822744803131)
                  ·
                    rfl

theorem cell20_659717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_659717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659717 prefixEnd_659717 := by exact prefixLift 659717
  have htrace : WordTrace (prefixWord ++ tailWord_659717) baseStart_659717 baseEnd_659717 := by
    simpa [prefixWord, tailWord_659717, baseEnd_659717] using wordTrace_append hprefix tailTrace_659717
  have hstable : (prefixWord ++ tailWord_659717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659717).length < 2 ^ (prefixWord ++ tailWord_659717).sum := by decide
  have hdescent : baseEnd_659717 < baseStart_659717 := by decide
  rcases family_descends (prefixWord ++ tailWord_659717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659720 : List Nat := [2, 1, 3, 2, 3, 1, 4, 4]
def baseStart_659720 : Nat := 118140960795 + 659720 * 2 ^ 59
def prefixEnd_659720 : Nat := 4983230072969 + 3 ^ 40 * 659720 * 2
def baseEnd_659720 : Nat := 100371394780522689234373

theorem tailTrace_659720 : CollatzResearch.WordTrace tailWord_659720 prefixEnd_659720 100371394780522689234373 := by
  unfold tailWord_659720
  simp only [CollatzResearch.WordTrace]
  refine ⟨12030982584977293025448307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16041310113303057367264409 12030982584977293025448307)
  ·
    refine ⟨18046473877465939538172461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12030982584977293025448307 18046473877465939538172461)
    ·
      refine ⟨6767427704049727326814673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18046473877465939538172461 6767427704049727326814673)
      ·
        refine ⟨5075570778037295495111005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6767427704049727326814673 5075570778037295495111005)
        ·
          refine ⟨1903339041763985810666627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5075570778037295495111005 1903339041763985810666627)
          ·
            refine ⟨2855008562645978715999941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1903339041763985810666627 2855008562645978715999941)
            ·
              refine ⟨535314105496121009249989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2855008562645978715999941 535314105496121009249989)
              ·
                refine ⟨100371394780522689234373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 535314105496121009249989 100371394780522689234373)
                ·
                  rfl

theorem cell20_659720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 4].length) (baseStart_659720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659720 prefixEnd_659720 := by exact prefixLift 659720
  have htrace : WordTrace (prefixWord ++ tailWord_659720) baseStart_659720 baseEnd_659720 := by
    simpa [prefixWord, tailWord_659720, baseEnd_659720] using wordTrace_append hprefix tailTrace_659720
  have hstable : (prefixWord ++ tailWord_659720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659720).length < 2 ^ (prefixWord ++ tailWord_659720).sum := by decide
  have hdescent : baseEnd_659720 < baseStart_659720 := by decide
  rcases family_descends (prefixWord ++ tailWord_659720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659757 : List Nat := [1, 5, 3, 1, 3, 1, 2, 1, 3]
def baseStart_659757 : Nat := 118140960795 + 659757 * 2 ^ 59
def prefixEnd_659757 : Nat := 4983230072969 + 3 ^ 40 * 659757 * 2
def baseEnd_659757 : Nat := 301131072149760383469635

theorem tailTrace_659757 : CollatzResearch.WordTrace tailWord_659757 prefixEnd_659757 301131072149760383469635 := by
  unfold tailWord_659757
  simp only [CollatzResearch.WordTrace]
  refine ⟨24063314670820541369993525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16042209780547027579995683 24063314670820541369993525)
  ·
    refine ⟨2255935750389425753436893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24063314670820541369993525 2255935750389425753436893)
    ·
      refine ⟨845975906396034657538835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2255935750389425753436893 845975906396034657538835)
      ·
        refine ⟨1268963859594051986308253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 845975906396034657538835 1268963859594051986308253)
        ·
          refine ⟨475861447347769494865595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1268963859594051986308253 475861447347769494865595)
          ·
            refine ⟨713792171021654242298393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475861447347769494865595 713792171021654242298393)
            ·
              refine ⟨535344128266240681723795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 713792171021654242298393 535344128266240681723795)
              ·
                refine ⟨803016192399361022585693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535344128266240681723795 803016192399361022585693)
                ·
                  refine ⟨301131072149760383469635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 803016192399361022585693 301131072149760383469635)
                  ·
                    rfl

theorem cell20_659757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_659757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659757 prefixEnd_659757 := by exact prefixLift 659757
  have htrace : WordTrace (prefixWord ++ tailWord_659757) baseStart_659757 baseEnd_659757 := by
    simpa [prefixWord, tailWord_659757, baseEnd_659757] using wordTrace_append hprefix tailTrace_659757
  have hstable : (prefixWord ++ tailWord_659757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659757).length < 2 ^ (prefixWord ++ tailWord_659757).sum := by decide
  have hdescent : baseEnd_659757 < baseStart_659757 := by decide
  rcases family_descends (prefixWord ++ tailWord_659757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659761 : List Nat := [1, 2, 2, 3, 4, 2, 2, 1, 3]
def baseStart_659761 : Nat := 118140960795 + 659761 * 2 ^ 59
def prefixEnd_659761 : Nat := 4983230072969 + 3 ^ 40 * 659761 * 2
def baseEnd_659761 : Nat := 301132897858754147336285

theorem tailTrace_659761 : CollatzResearch.WordTrace tailWord_659761 prefixEnd_659761 301132897858754147336285 := by
  unfold tailWord_659761
  simp only [CollatzResearch.WordTrace]
  refine ⟨24063460562806050053139137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16042307041870700035426091 24063460562806050053139137)
  ·
    refine ⟨18047595422104537539854353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24063460562806050053139137 18047595422104537539854353)
    ·
      refine ⟨13535696566578403154890765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18047595422104537539854353 13535696566578403154890765)
      ·
        refine ⟨5075886212466901183084037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13535696566578403154890765 5075886212466901183084037)
        ·
          refine ⟨951728664837543971828257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5075886212466901183084037 951728664837543971828257)
          ·
            refine ⟨713796498628157978871193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 951728664837543971828257 713796498628157978871193)
            ·
              refine ⟨535347373971118484153395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 713796498628157978871193 535347373971118484153395)
              ·
                refine ⟨803021060956677726230093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535347373971118484153395 803021060956677726230093)
                ·
                  refine ⟨301132897858754147336285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 803021060956677726230093 301132897858754147336285)
                  ·
                    rfl

theorem cell20_659761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 3].length) (baseStart_659761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659761 prefixEnd_659761 := by exact prefixLift 659761
  have htrace : WordTrace (prefixWord ++ tailWord_659761) baseStart_659761 baseEnd_659761 := by
    simpa [prefixWord, tailWord_659761, baseEnd_659761] using wordTrace_append hprefix tailTrace_659761
  have hstable : (prefixWord ++ tailWord_659761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659761).length < 2 ^ (prefixWord ++ tailWord_659761).sum := by decide
  have hdescent : baseEnd_659761 < baseStart_659761 := by decide
  rcases family_descends (prefixWord ++ tailWord_659761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659765 : List Nat := [1, 3, 3, 1, 2, 1, 3, 3, 3]
def baseStart_659765 : Nat := 118140960795 + 659765 * 2 ^ 59
def prefixEnd_659765 : Nat := 4983230072969 + 3 ^ 40 * 659765 * 2
def baseEnd_659765 : Nat := 301134723567747911202935

theorem tailTrace_659765 : CollatzResearch.WordTrace tailWord_659765 prefixEnd_659765 301134723567747911202935 := by
  unfold tailWord_659765
  simp only [CollatzResearch.WordTrace]
  refine ⟨24063606454791558736284749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16042404303194372490856499 24063606454791558736284749)
  ·
    refine ⟨9023852420546834526106781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24063606454791558736284749 9023852420546834526106781)
    ·
      refine ⟨3383944657705062947290043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9023852420546834526106781 3383944657705062947290043)
      ·
        refine ⟨5075916986557594420935065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3383944657705062947290043 5075916986557594420935065)
        ·
          refine ⟨3806937739918195815701299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5075916986557594420935065 3806937739918195815701299)
          ·
            refine ⟨5710406609877293723551949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3806937739918195815701299 5710406609877293723551949)
            ·
              refine ⟨2141402478703985146331981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5710406609877293723551949 2141402478703985146331981)
              ·
                refine ⟨803025929513994429874493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2141402478703985146331981 803025929513994429874493)
                ·
                  refine ⟨301134723567747911202935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 803025929513994429874493 301134723567747911202935)
                  ·
                    rfl

theorem cell20_659765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_659765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659765 prefixEnd_659765 := by exact prefixLift 659765
  have htrace : WordTrace (prefixWord ++ tailWord_659765) baseStart_659765 baseEnd_659765 := by
    simpa [prefixWord, tailWord_659765, baseEnd_659765] using wordTrace_append hprefix tailTrace_659765
  have hstable : (prefixWord ++ tailWord_659765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659765).length < 2 ^ (prefixWord ++ tailWord_659765).sum := by decide
  have hdescent : baseEnd_659765 < baseStart_659765 := by decide
  rcases family_descends (prefixWord ++ tailWord_659765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659830 : List Nat := [5, 1, 1, 4, 1, 1, 3, 4]
def baseStart_659830 : Nat := 118140960795 + 659830 * 2 ^ 59
def prefixEnd_659830 : Nat := 4983230072969 + 3 ^ 40 * 659830 * 2
def baseEnd_659830 : Nat := 100388130446298858012001

theorem tailTrace_659830 : CollatzResearch.WordTrace tailWord_659830 prefixEnd_659830 100388130446298858012001 := by
  unfold tailWord_659830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1504123574972254677337559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16043984799704049891600629 1504123574972254677337559)
  ·
    refine ⟨2256185362458382016006339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1504123574972254677337559 2256185362458382016006339)
    ·
      refine ⟨3384278043687573024009509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2256185362458382016006339 3384278043687573024009509)
      ·
        refine ⟨634552133191419942001783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3384278043687573024009509 634552133191419942001783)
        ·
          refine ⟨951828199787129913002675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634552133191419942001783 951828199787129913002675)
          ·
            refine ⟨1427742299680694869504013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 951828199787129913002675 1427742299680694869504013)
            ·
              refine ⟨535403362380260576064005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1427742299680694869504013 535403362380260576064005)
              ·
                refine ⟨100388130446298858012001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 535403362380260576064005 100388130446298858012001)
                ·
                  rfl

theorem cell20_659830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_659830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659830 prefixEnd_659830 := by exact prefixLift 659830
  have htrace : WordTrace (prefixWord ++ tailWord_659830) baseStart_659830 baseEnd_659830 := by
    simpa [prefixWord, tailWord_659830, baseEnd_659830] using wordTrace_append hprefix tailTrace_659830
  have hstable : (prefixWord ++ tailWord_659830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659830).length < 2 ^ (prefixWord ++ tailWord_659830).sum := by decide
  have hdescent : baseEnd_659830 < baseStart_659830 := by decide
  rcases family_descends (prefixWord ++ tailWord_659830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659952 : List Nat := [2, 1, 1, 1, 3, 3, 1, 8]
def baseStart_659952 : Nat := 118140960795 + 659952 * 2 ^ 59
def prefixEnd_659952 : Nat := 4983230072969 + 3 ^ 40 * 659952 * 2
def baseEnd_659952 : Nat := 100406691821068790656279

theorem tailTrace_659952 : CollatzResearch.WordTrace tailWord_659952 prefixEnd_659952 100406691821068790656279 := by
  unfold tailWord_659952
  simp only [CollatzResearch.WordTrace]
  refine ⟨12035213452557044836671055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16046951270076059782228073 12035213452557044836671055)
  ·
    refine ⟨18052820178835567255006583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12035213452557044836671055 18052820178835567255006583)
    ·
      refine ⟨27079230268253350882509875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18052820178835567255006583 27079230268253350882509875)
      ·
        refine ⟨40618845402380026323764813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27079230268253350882509875 40618845402380026323764813)
        ·
          refine ⟨15232067025892509871411805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40618845402380026323764813 15232067025892509871411805)
          ·
            refine ⟨5712025134709691201779427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15232067025892509871411805 5712025134709691201779427)
            ·
              refine ⟨8568037702064536802669141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5712025134709691201779427 8568037702064536802669141)
              ·
                refine ⟨100406691821068790656279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8568037702064536802669141 100406691821068790656279)
                ·
                  rfl

theorem cell20_659952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_659952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659952 prefixEnd_659952 := by exact prefixLift 659952
  have htrace : WordTrace (prefixWord ++ tailWord_659952) baseStart_659952 baseEnd_659952 := by
    simpa [prefixWord, tailWord_659952, baseEnd_659952] using wordTrace_append hprefix tailTrace_659952
  have hstable : (prefixWord ++ tailWord_659952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659952).length < 2 ^ (prefixWord ++ tailWord_659952).sum := by decide
  have hdescent : baseEnd_659952 < baseStart_659952 := by decide
  rcases family_descends (prefixWord ++ tailWord_659952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659972 : List Nat := [2, 3, 2, 3, 1, 2, 2, 2, 3]
def baseStart_659972 : Nat := 118140960795 + 659972 * 2 ^ 59
def prefixEnd_659972 : Nat := 4983230072969 + 3 ^ 40 * 659972 * 2
def baseEnd_659972 : Nat := 301229204008175191302089

theorem tailTrace_659972 : CollatzResearch.WordTrace tailWord_659972 prefixEnd_659972 301229204008175191302089 := by
  unfold tailWord_659972
  simp only [CollatzResearch.WordTrace]
  refine ⟨12035578182520816544535085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16047437576694422059380113 12035578182520816544535085)
  ·
    refine ⟨4513341818445306204200657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12035578182520816544535085 4513341818445306204200657)
    ·
      refine ⟨3385006363833979653150493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4513341818445306204200657 3385006363833979653150493)
      ·
        refine ⟨1269377386437742369931435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3385006363833979653150493 1269377386437742369931435)
        ·
          refine ⟨1904066079656613554897153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1269377386437742369931435 1904066079656613554897153)
          ·
            refine ⟨1428049559742460166172865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1904066079656613554897153 1428049559742460166172865)
            ·
              refine ⟨1071037169806845124629649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1428049559742460166172865 1071037169806845124629649)
              ·
                refine ⟨803277877355133843472237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1071037169806845124629649 803277877355133843472237)
                ·
                  refine ⟨301229204008175191302089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 803277877355133843472237 301229204008175191302089)
                  ·
                    rfl

theorem cell20_659972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_659972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659972 prefixEnd_659972 := by exact prefixLift 659972
  have htrace : WordTrace (prefixWord ++ tailWord_659972) baseStart_659972 baseEnd_659972 := by
    simpa [prefixWord, tailWord_659972, baseEnd_659972] using wordTrace_append hprefix tailTrace_659972
  have hstable : (prefixWord ++ tailWord_659972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659972).length < 2 ^ (prefixWord ++ tailWord_659972).sum := by decide
  have hdescent : baseEnd_659972 < baseStart_659972 := by decide
  rcases family_descends (prefixWord ++ tailWord_659972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659975 : List Nat := [1, 1, 4, 3, 3, 2, 2, 2, 2]
def baseStart_659975 : Nat := 118140960795 + 659975 * 2 ^ 59
def prefixEnd_659975 : Nat := 4983230072969 + 3 ^ 40 * 659975 * 2
def baseEnd_659975 : Nat := 301230573289920514202077

theorem tailTrace_659975 : CollatzResearch.WordTrace tailWord_659975 prefixEnd_659975 301230573289920514202077 := by
  unfold tailWord_659975
  simp only [CollatzResearch.WordTrace]
  refine ⟨24071265784030764601429379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16047510522687176400952919 24071265784030764601429379)
  ·
    refine ⟨36106898676046146902144069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24071265784030764601429379 36106898676046146902144069)
    ·
      refine ⟨6770043501758652544152013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36106898676046146902144069 6770043501758652544152013)
      ·
        refine ⟨2538766313159494704057005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6770043501758652544152013 2538766313159494704057005)
        ·
          refine ⟨952037367434810514021377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2538766313159494704057005 952037367434810514021377)
          ·
            refine ⟨714028025576107885516033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 952037367434810514021377 714028025576107885516033)
            ·
              refine ⟨535521019182080914137025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 714028025576107885516033 535521019182080914137025)
              ·
                refine ⟨401640764386560685602769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 535521019182080914137025 401640764386560685602769)
                ·
                  refine ⟨301230573289920514202077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401640764386560685602769 301230573289920514202077)
                  ·
                    rfl

theorem cell20_659975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 2].length) (baseStart_659975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659975 prefixEnd_659975 := by exact prefixLift 659975
  have htrace : WordTrace (prefixWord ++ tailWord_659975) baseStart_659975 baseEnd_659975 := by
    simpa [prefixWord, tailWord_659975, baseEnd_659975] using wordTrace_append hprefix tailTrace_659975
  have hstable : (prefixWord ++ tailWord_659975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659975).length < 2 ^ (prefixWord ++ tailWord_659975).sum := by decide
  have hdescent : baseEnd_659975 < baseStart_659975 := by decide
  rcases family_descends (prefixWord ++ tailWord_659975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659979 : List Nat := [1, 1, 1, 1, 7, 2, 1, 4, 2]
def baseStart_659979 : Nat := 118140960795 + 659979 * 2 ^ 59
def prefixEnd_659979 : Nat := 4983230072969 + 3 ^ 40 * 659979 * 2
def baseEnd_659979 : Nat := 301232398998914278068727

theorem tailTrace_659979 : CollatzResearch.WordTrace tailWord_659979 prefixEnd_659979 301232398998914278068727 := by
  unfold tailWord_659979
  simp only [CollatzResearch.WordTrace]
  refine ⟨24071411676016273284574991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16047607784010848856383327 24071411676016273284574991)
  ·
    refine ⟨36107117514024409926862487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24071411676016273284574991 36107117514024409926862487)
    ·
      refine ⟨54160676271036614890293731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36107117514024409926862487 54160676271036614890293731)
      ·
        refine ⟨81241014406554922335440597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54160676271036614890293731 81241014406554922335440597)
        ·
          refine ⟨1904086275153630992236889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 81241014406554922335440597 1904086275153630992236889)
          ·
            refine ⟨1428064706365223244177667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1904086275153630992236889 1428064706365223244177667)
            ·
              refine ⟨2142097059547834866266501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1428064706365223244177667 2142097059547834866266501)
              ·
                refine ⟨401643198665219037424969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2142097059547834866266501 401643198665219037424969)
                ·
                  refine ⟨301232398998914278068727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401643198665219037424969 301232398998914278068727)
                  ·
                    rfl

theorem cell20_659979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 2].length) (baseStart_659979 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_659979 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_659979 prefixEnd_659979 := by exact prefixLift 659979
  have htrace : WordTrace (prefixWord ++ tailWord_659979) baseStart_659979 baseEnd_659979 := by
    simpa [prefixWord, tailWord_659979, baseEnd_659979] using wordTrace_append hprefix tailTrace_659979
  have hstable : (prefixWord ++ tailWord_659979).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659979).length < 2 ^ (prefixWord ++ tailWord_659979).sum := by decide
  have hdescent : baseEnd_659979 < baseStart_659979 := by decide
  rcases family_descends (prefixWord ++ tailWord_659979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660021 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 6]
def baseStart_660021 : Nat := 118140960795 + 660021 * 2 ^ 59
def prefixEnd_660021 : Nat := 4983230072969 + 3 ^ 40 * 660021 * 2
def baseEnd_660021 : Nat := 301251568943348798668555

theorem tailTrace_660021 : CollatzResearch.WordTrace tailWord_660021 prefixEnd_660021 301251568943348798668555 := by
  unfold tailWord_660021
  simp only [CollatzResearch.WordTrace]
  refine ⟨24072943541864114457603917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16048629027909409638402611 24072943541864114457603917)
  ·
    refine ⟨9027353828199042921601469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24072943541864114457603917 9027353828199042921601469)
    ·
      refine ⟨3385257685574641095600551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9027353828199042921601469 3385257685574641095600551)
      ·
        refine ⟨5077886528361961643400827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3385257685574641095600551 5077886528361961643400827)
        ·
          refine ⟨7616829792542942465101241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5077886528361961643400827 7616829792542942465101241)
          ·
            refine ⟨5712622344407206848825931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7616829792542942465101241 5712622344407206848825931)
            ·
              refine ⟨8568933516610810273238897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5712622344407206848825931 8568933516610810273238897)
              ·
                refine ⟨6426700137458107704929173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8568933516610810273238897 6426700137458107704929173)
                ·
                  refine ⟨301251568943348798668555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6426700137458107704929173 301251568943348798668555)
                  ·
                    rfl

theorem cell20_660021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_660021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660021 prefixEnd_660021 := by exact prefixLift 660021
  have htrace : WordTrace (prefixWord ++ tailWord_660021) baseStart_660021 baseEnd_660021 := by
    simpa [prefixWord, tailWord_660021, baseEnd_660021] using wordTrace_append hprefix tailTrace_660021
  have hstable : (prefixWord ++ tailWord_660021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660021).length < 2 ^ (prefixWord ++ tailWord_660021).sum := by decide
  have hdescent : baseEnd_660021 < baseStart_660021 := by decide
  rcases family_descends (prefixWord ++ tailWord_660021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660093 : List Nat := [1, 4, 1, 1, 5, 2, 1, 1, 4]
def baseStart_660093 : Nat := 118140960795 + 660093 * 2 ^ 59
def prefixEnd_660093 : Nat := 4983230072969 + 3 ^ 40 * 660093 * 2
def baseEnd_660093 : Nat := 301284431705236548268261

theorem tailTrace_660093 : CollatzResearch.WordTrace tailWord_660093 prefixEnd_660093 301284431705236548268261 := by
  unfold tailWord_660093
  simp only [CollatzResearch.WordTrace]
  refine ⟨24075569597603270754224933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16050379731735513836149955 24075569597603270754224933)
  ·
    refine ⟨4514169299550613266417175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24075569597603270754224933 4514169299550613266417175)
    ·
      refine ⟨6771253949325919899625763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4514169299550613266417175 6771253949325919899625763)
      ·
        refine ⟨10156880923988879849438645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6771253949325919899625763 10156880923988879849438645)
        ·
          refine ⟨952207586623957485884873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10156880923988879849438645 952207586623957485884873)
          ·
            refine ⟨714155689967968114413655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 952207586623957485884873 714155689967968114413655)
            ·
              refine ⟨1071233534951952171620483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714155689967968114413655 1071233534951952171620483)
              ·
                refine ⟨1606850302427928257430725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1071233534951952171620483 1606850302427928257430725)
                ·
                  refine ⟨301284431705236548268261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1606850302427928257430725 301284431705236548268261)
                  ·
                    rfl

theorem cell20_660093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_660093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660093 prefixEnd_660093 := by exact prefixLift 660093
  have htrace : WordTrace (prefixWord ++ tailWord_660093) baseStart_660093 baseEnd_660093 := by
    simpa [prefixWord, tailWord_660093, baseEnd_660093] using wordTrace_append hprefix tailTrace_660093
  have hstable : (prefixWord ++ tailWord_660093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660093).length < 2 ^ (prefixWord ++ tailWord_660093).sum := by decide
  have hdescent : baseEnd_660093 < baseStart_660093 := by decide
  rcases family_descends (prefixWord ++ tailWord_660093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660138 : List Nat := [3, 1, 5, 2, 1, 8]
def baseStart_660138 : Nat := 118140960795 + 660138 * 2 ^ 59
def prefixEnd_660138 : Nat := 4983230072969 + 3 ^ 40 * 660138 * 2
def baseEnd_660138 : Nat := 11159443367830236732151

theorem tailTrace_660138 : CollatzResearch.WordTrace tailWord_660138 prefixEnd_660138 11159443367830236732151 := by
  unfold tailWord_660138
  simp only [CollatzResearch.WordTrace]
  refine ⟨6019302720610060859903267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16051473921626828959742045 6019302720610060859903267)
  ·
    refine ⟨9028954080915091289854901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6019302720610060859903267 9028954080915091289854901)
    ·
      refine ⟨846464445085789808423897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9028954080915091289854901 846464445085789808423897)
      ·
        refine ⟨634848333814342356317923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 846464445085789808423897 634848333814342356317923)
        ·
          refine ⟨952272500721513534476885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634848333814342356317923 952272500721513534476885)
          ·
            refine ⟨11159443367830236732151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 952272500721513534476885 11159443367830236732151)
            ·
              rfl

theorem cell20_660138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 8].length) (baseStart_660138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660138 prefixEnd_660138 := by exact prefixLift 660138
  have htrace : WordTrace (prefixWord ++ tailWord_660138) baseStart_660138 baseEnd_660138 := by
    simpa [prefixWord, tailWord_660138, baseEnd_660138] using wordTrace_append hprefix tailTrace_660138
  have hstable : (prefixWord ++ tailWord_660138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660138).length < 2 ^ (prefixWord ++ tailWord_660138).sum := by decide
  have hdescent : baseEnd_660138 < baseStart_660138 := by decide
  rcases family_descends (prefixWord ++ tailWord_660138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660159 : List Nat := [1, 1, 2, 2, 2, 6, 1, 5]
def baseStart_660159 : Nat := 118140960795 + 660159 * 2 ^ 59
def prefixEnd_660159 : Nat := 4983230072969 + 3 ^ 40 * 660159 * 2
def baseEnd_660159 : Nat := 100438185301211217355997

theorem tailTrace_660159 : CollatzResearch.WordTrace tailWord_660159 prefixEnd_660159 100438185301211217355997 := by
  unfold tailWord_660159
  simp only [CollatzResearch.WordTrace]
  refine ⟨24077976815364164026127531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16051984543576109350751687 24077976815364164026127531)
  ·
    refine ⟨36116965223046246039191297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24077976815364164026127531 36116965223046246039191297)
    ·
      refine ⟨27087723917284684529393473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36116965223046246039191297 27087723917284684529393473)
      ·
        refine ⟨20315792937963513397045105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27087723917284684529393473 20315792937963513397045105)
        ·
          refine ⟨15236844703472635047783829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20315792937963513397045105 15236844703472635047783829)
          ·
            refine ⟨714227095475279767864867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15236844703472635047783829 714227095475279767864867)
            ·
              refine ⟨1071340643212919651797301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714227095475279767864867 1071340643212919651797301)
              ·
                refine ⟨100438185301211217355997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1071340643212919651797301 100438185301211217355997)
                ·
                  rfl

theorem cell20_660159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 5].length) (baseStart_660159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660159 prefixEnd_660159 := by exact prefixLift 660159
  have htrace : WordTrace (prefixWord ++ tailWord_660159) baseStart_660159 baseEnd_660159 := by
    simpa [prefixWord, tailWord_660159, baseEnd_660159] using wordTrace_append hprefix tailTrace_660159
  have hstable : (prefixWord ++ tailWord_660159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660159).length < 2 ^ (prefixWord ++ tailWord_660159).sum := by decide
  have hdescent : baseEnd_660159 < baseStart_660159 := by decide
  rcases family_descends (prefixWord ++ tailWord_660159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660200 : List Nat := [2, 1, 4, 1, 4, 2, 1, 2, 3]
def baseStart_660200 : Nat := 118140960795 + 660200 * 2 ^ 59
def prefixEnd_660200 : Nat := 4983230072969 + 3 ^ 40 * 660200 * 2
def baseEnd_660200 : Nat := 301333269420819731701157

theorem tailTrace_660200 : CollatzResearch.WordTrace tailWord_660200 prefixEnd_660200 301333269420819731701157 := by
  unfold tailWord_660200
  simp only [CollatzResearch.WordTrace]
  refine ⟨12039736104107814014185027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16052981472143752018913369 12039736104107814014185027)
  ·
    refine ⟨18059604156161721021277541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12039736104107814014185027 18059604156161721021277541)
    ·
      refine ⟨3386175779280322691489539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18059604156161721021277541 3386175779280322691489539)
      ·
        refine ⟨5079263668920484037234309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3386175779280322691489539 5079263668920484037234309)
        ·
          refine ⟨952361937922590756981433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5079263668920484037234309 952361937922590756981433)
          ·
            refine ⟨714271453441943067736075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 952361937922590756981433 714271453441943067736075)
            ·
              refine ⟨1071407180162914601604113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714271453441943067736075 1071407180162914601604113)
              ·
                refine ⟨803555385122185951203085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1071407180162914601604113 803555385122185951203085)
                ·
                  refine ⟨301333269420819731701157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 803555385122185951203085 301333269420819731701157)
                  ·
                    rfl

theorem cell20_660200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 3].length) (baseStart_660200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660200 prefixEnd_660200 := by exact prefixLift 660200
  have htrace : WordTrace (prefixWord ++ tailWord_660200) baseStart_660200 baseEnd_660200 := by
    simpa [prefixWord, tailWord_660200, baseEnd_660200] using wordTrace_append hprefix tailTrace_660200
  have hstable : (prefixWord ++ tailWord_660200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660200).length < 2 ^ (prefixWord ++ tailWord_660200).sum := by decide
  have hdescent : baseEnd_660200 < baseStart_660200 := by decide
  rcases family_descends (prefixWord ++ tailWord_660200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660221 : List Nat := [1, 4, 1, 1, 1, 1, 7, 1, 3]
def baseStart_660221 : Nat := 118140960795 + 660221 * 2 ^ 59
def prefixEnd_660221 : Nat := 4983230072969 + 3 ^ 40 * 660221 * 2
def baseEnd_660221 : Nat := 301342854393036992001071

theorem tailTrace_660221 : CollatzResearch.WordTrace tailWord_660221 prefixEnd_660221 301342854393036992001071 := by
  unfold tailWord_660221
  simp only [CollatzResearch.WordTrace]
  refine ⟨24080238141139548614884517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16053492094093032409923011 24080238141139548614884517)
  ·
    refine ⟨4515044651463665365290847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24080238141139548614884517 4515044651463665365290847)
    ·
      refine ⟨6772566977195498047936271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4515044651463665365290847 6772566977195498047936271)
      ·
        refine ⟨10158850465793247071904407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6772566977195498047936271 10158850465793247071904407)
        ·
          refine ⟨15238275698689870607856611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10158850465793247071904407 15238275698689870607856611)
          ·
            refine ⟨22857413548034805911784917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15238275698689870607856611 22857413548034805911784917)
            ·
              refine ⟨535720630032065763557459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 22857413548034805911784917 535720630032065763557459)
              ·
                refine ⟨803580945048098645336189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535720630032065763557459 803580945048098645336189)
                ·
                  refine ⟨301342854393036992001071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 803580945048098645336189 301342854393036992001071)
                  ·
                    rfl

theorem cell20_660221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_660221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660221 prefixEnd_660221 := by exact prefixLift 660221
  have htrace : WordTrace (prefixWord ++ tailWord_660221) baseStart_660221 baseEnd_660221 := by
    simpa [prefixWord, tailWord_660221, baseEnd_660221] using wordTrace_append hprefix tailTrace_660221
  have hstable : (prefixWord ++ tailWord_660221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660221).length < 2 ^ (prefixWord ++ tailWord_660221).sum := by decide
  have hdescent : baseEnd_660221 < baseStart_660221 := by decide
  rcases family_descends (prefixWord ++ tailWord_660221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660256 : List Nat := [2, 1, 1, 5, 1, 2, 8]
def baseStart_660256 : Nat := 118140960795 + 660256 * 2 ^ 59
def prefixEnd_660256 : Nat := 4983230072969 + 3 ^ 40 * 660256 * 2
def baseEnd_660256 : Nat := 33484314371859158426029

theorem tailTrace_660256 : CollatzResearch.WordTrace tailWord_660256 prefixEnd_660256 33484314371859158426029 := by
  unfold tailWord_660256
  simp only [CollatzResearch.WordTrace]
  refine ⟨12040757348006374796204311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16054343130675166394939081 12040757348006374796204311)
  ·
    refine ⟨18061136022009562194306467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12040757348006374796204311 18061136022009562194306467)
    ·
      refine ⟨27091704033014343291459701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18061136022009562194306467 27091704033014343291459701)
      ·
        refine ⟨2539847253095094683574347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27091704033014343291459701 2539847253095094683574347)
        ·
          refine ⟨3809770879642642025361521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2539847253095094683574347 3809770879642642025361521)
          ·
            refine ⟨2857328159731981519021141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3809770879642642025361521 2857328159731981519021141)
            ·
              refine ⟨33484314371859158426029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2857328159731981519021141 33484314371859158426029)
              ·
                rfl

theorem cell20_660256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 8].length) (baseStart_660256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660256 prefixEnd_660256 := by exact prefixLift 660256
  have htrace : WordTrace (prefixWord ++ tailWord_660256) baseStart_660256 baseEnd_660256 := by
    simpa [prefixWord, tailWord_660256, baseEnd_660256] using wordTrace_append hprefix tailTrace_660256
  have hstable : (prefixWord ++ tailWord_660256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660256).length < 2 ^ (prefixWord ++ tailWord_660256).sum := by decide
  have hdescent : baseEnd_660256 < baseStart_660256 := by decide
  rcases family_descends (prefixWord ++ tailWord_660256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660269 : List Nat := [1, 5, 3, 2, 1, 1, 2, 5]
def baseStart_660269 : Nat := 118140960795 + 660269 * 2 ^ 59
def prefixEnd_660269 : Nat := 4983230072969 + 3 ^ 40 * 660269 * 2
def baseEnd_660269 : Nat := 100454920966987386133625

theorem tailTrace_660269 : CollatzResearch.WordTrace tailWord_660269 prefixEnd_660269 100454920966987386133625 := by
  unfold tailWord_660269
  simp only [CollatzResearch.WordTrace]
  refine ⟨24081988844965652812631861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16054659229977101875087907 24081988844965652812631861)
  ·
    refine ⟨2257686454215529951184237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24081988844965652812631861 2257686454215529951184237)
    ·
      refine ⟨846632420330823731694089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2257686454215529951184237 846632420330823731694089)
      ·
        refine ⟨634974315248117798770567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 846632420330823731694089 634974315248117798770567)
        ·
          refine ⟨952461472872176698155851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634974315248117798770567 952461472872176698155851)
          ·
            refine ⟨1428692209308265047233777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952461472872176698155851 1428692209308265047233777)
            ·
              refine ⟨1071519156981198785425333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1428692209308265047233777 1071519156981198785425333)
              ·
                refine ⟨100454920966987386133625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1071519156981198785425333 100454920966987386133625)
                ·
                  rfl

theorem cell20_660269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 5].length) (baseStart_660269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660269 prefixEnd_660269 := by exact prefixLift 660269
  have htrace : WordTrace (prefixWord ++ tailWord_660269) baseStart_660269 baseEnd_660269 := by
    simpa [prefixWord, tailWord_660269, baseEnd_660269] using wordTrace_append hprefix tailTrace_660269
  have hstable : (prefixWord ++ tailWord_660269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660269).length < 2 ^ (prefixWord ++ tailWord_660269).sum := by decide
  have hdescent : baseEnd_660269 < baseStart_660269 := by decide
  rcases family_descends (prefixWord ++ tailWord_660269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660276 : List Nat := [2, 5, 1, 1, 3, 1, 1, 3, 3]
def baseStart_660276 : Nat := 118140960795 + 660276 * 2 ^ 59
def prefixEnd_660276 : Nat := 4983230072969 + 3 ^ 40 * 660276 * 2
def baseEnd_660276 : Nat := 301367957891701245167513

theorem tailTrace_660276 : CollatzResearch.WordTrace tailWord_660276 prefixEnd_660276 301367957891701245167513 := by
  unfold tailWord_660276
  simp only [CollatzResearch.WordTrace]
  refine ⟨12041122077970146504068341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16054829437293528672091121 12041122077970146504068341)
  ·
    refine ⟨1128855194809701234756407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12041122077970146504068341 1128855194809701234756407)
    ·
      refine ⟨1693282792214551852134611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1128855194809701234756407 1693282792214551852134611)
      ·
        refine ⟨2539924188321827778201917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1693282792214551852134611 2539924188321827778201917)
        ·
          refine ⟨952471570620685416825719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2539924188321827778201917 952471570620685416825719)
          ·
            refine ⟨1428707355931028125238579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952471570620685416825719 1428707355931028125238579)
            ·
              refine ⟨2143061033896542187857869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1428707355931028125238579 2143061033896542187857869)
              ·
                refine ⟨803647887711203320446701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2143061033896542187857869 803647887711203320446701)
                ·
                  refine ⟨301367957891701245167513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 803647887711203320446701 301367957891701245167513)
                  ·
                    rfl

theorem cell20_660276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_660276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660276 prefixEnd_660276 := by exact prefixLift 660276
  have htrace : WordTrace (prefixWord ++ tailWord_660276) baseStart_660276 baseEnd_660276 := by
    simpa [prefixWord, tailWord_660276, baseEnd_660276] using wordTrace_append hprefix tailTrace_660276
  have hstable : (prefixWord ++ tailWord_660276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660276).length < 2 ^ (prefixWord ++ tailWord_660276).sum := by decide
  have hdescent : baseEnd_660276 < baseStart_660276 := by decide
  rcases family_descends (prefixWord ++ tailWord_660276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660280 : List Nat := [2, 1, 2, 1, 3, 2, 3, 3, 3]
def baseStart_660280 : Nat := 118140960795 + 660280 * 2 ^ 59
def prefixEnd_660280 : Nat := 4983230072969 + 3 ^ 40 * 660280 * 2
def baseEnd_660280 : Nat := 301369783600695009034163

theorem tailTrace_660280 : CollatzResearch.WordTrace tailWord_660280 prefixEnd_660280 301369783600695009034163 := by
  unfold tailWord_660280
  simp only [CollatzResearch.WordTrace]
  refine ⟨12041195023962900845641147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16054926698617201127521529 12041195023962900845641147)
  ·
    refine ⟨18061792535944351268461721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12041195023962900845641147 18061792535944351268461721)
    ·
      refine ⟨13546344401958263451346291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18061792535944351268461721 13546344401958263451346291)
      ·
        refine ⟨20319516602937395177019437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13546344401958263451346291 20319516602937395177019437)
        ·
          refine ⟨7619818726101523191382289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20319516602937395177019437 7619818726101523191382289)
          ·
            refine ⟨5714864044576142393536717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7619818726101523191382289 5714864044576142393536717)
            ·
              refine ⟨2143074016716053397576269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5714864044576142393536717 2143074016716053397576269)
              ·
                refine ⟨803652756268520024091101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2143074016716053397576269 803652756268520024091101)
                ·
                  refine ⟨301369783600695009034163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 803652756268520024091101 301369783600695009034163)
                  ·
                    rfl

theorem cell20_660280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_660280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660280 prefixEnd_660280 := by exact prefixLift 660280
  have htrace : WordTrace (prefixWord ++ tailWord_660280) baseStart_660280 baseEnd_660280 := by
    simpa [prefixWord, tailWord_660280, baseEnd_660280] using wordTrace_append hprefix tailTrace_660280
  have hstable : (prefixWord ++ tailWord_660280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660280).length < 2 ^ (prefixWord ++ tailWord_660280).sum := by decide
  have hdescent : baseEnd_660280 < baseStart_660280 := by decide
  rcases family_descends (prefixWord ++ tailWord_660280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660342 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_660342 : Nat := 118140960795 + 660342 * 2 ^ 59
def prefixEnd_660342 : Nat := 4983230072969 + 3 ^ 40 * 660342 * 2
def baseEnd_660342 : Nat := 301398082090098348967243

theorem tailTrace_660342 : CollatzResearch.WordTrace tailWord_660342 prefixEnd_660342 301398082090098348967243 := by
  unfold tailWord_660342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1505290710856324142502455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16056434249134124186692853 1505290710856324142502455)
  ·
    refine ⟨2257936066284486213753683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1505290710856324142502455 2257936066284486213753683)
    ·
      refine ⟨3386904099426729320630525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2257936066284486213753683 3386904099426729320630525)
      ·
        refine ⟨1270089037285023495236447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3386904099426729320630525 1270089037285023495236447)
        ·
          refine ⟨1905133555927535242854671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1270089037285023495236447 1905133555927535242854671)
          ·
            refine ⟨2857700333891302864282007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1905133555927535242854671 2857700333891302864282007)
            ·
              refine ⟨4286550500836954296423011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2857700333891302864282007 4286550500836954296423011)
              ·
                refine ⟨6429825751255431444634517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4286550500836954296423011 6429825751255431444634517)
                ·
                  refine ⟨301398082090098348967243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6429825751255431444634517 301398082090098348967243)
                  ·
                    rfl

theorem cell20_660342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_660342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660342 prefixEnd_660342 := by exact prefixLift 660342
  have htrace : WordTrace (prefixWord ++ tailWord_660342) baseStart_660342 baseEnd_660342 := by
    simpa [prefixWord, tailWord_660342, baseEnd_660342] using wordTrace_append hprefix tailTrace_660342
  have hstable : (prefixWord ++ tailWord_660342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660342).length < 2 ^ (prefixWord ++ tailWord_660342).sum := by decide
  have hdescent : baseEnd_660342 < baseStart_660342 := by decide
  rcases family_descends (prefixWord ++ tailWord_660342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660359 : List Nat := [1, 1, 4, 2, 3, 2, 2, 3, 2]
def baseStart_660359 : Nat := 118140960795 + 660359 * 2 ^ 59
def prefixEnd_660359 : Nat := 4983230072969 + 3 ^ 40 * 660359 * 2
def baseEnd_660359 : Nat := 301405841353321845400507

theorem tailTrace_660359 : CollatzResearch.WordTrace tailWord_660359 prefixEnd_660359 301405841353321845400507 := by
  unfold tailWord_660359
  simp only [CollatzResearch.WordTrace]
  refine ⟨24085271414639598183408131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16056847609759732122272087 24085271414639598183408131)
  ·
    refine ⟨36127907121959397275112197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24085271414639598183408131 36127907121959397275112197)
    ·
      refine ⟨6773982585367386989083537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36127907121959397275112197 6773982585367386989083537)
      ·
        refine ⟨5080486939025540241812653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6773982585367386989083537 5080486939025540241812653)
        ·
          refine ⟨1905182602134577590679745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5080486939025540241812653 1905182602134577590679745)
          ·
            refine ⟨1428886951600933193009809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1905182602134577590679745 1428886951600933193009809)
            ·
              refine ⟨1071665213700699894757357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1428886951600933193009809 1071665213700699894757357)
              ·
                refine ⟨401874455137762460534009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1071665213700699894757357 401874455137762460534009)
                ·
                  refine ⟨301405841353321845400507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401874455137762460534009 301405841353321845400507)
                  ·
                    rfl

theorem cell20_660359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 2].length) (baseStart_660359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660359 prefixEnd_660359 := by exact prefixLift 660359
  have htrace : WordTrace (prefixWord ++ tailWord_660359) baseStart_660359 baseEnd_660359 := by
    simpa [prefixWord, tailWord_660359, baseEnd_660359] using wordTrace_append hprefix tailTrace_660359
  have hstable : (prefixWord ++ tailWord_660359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660359).length < 2 ^ (prefixWord ++ tailWord_660359).sum := by decide
  have hdescent : baseEnd_660359 < baseStart_660359 := by decide
  rcases family_descends (prefixWord ++ tailWord_660359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660373 : List Nat := [1, 3, 2, 1, 1, 6, 1, 2, 3]
def baseStart_660373 : Nat := 118140960795 + 660373 * 2 ^ 59
def prefixEnd_660373 : Nat := 4983230072969 + 3 ^ 40 * 660373 * 2
def baseEnd_660373 : Nat := 301412231334800018933783

theorem tailTrace_660373 : CollatzResearch.WordTrace tailWord_660373 prefixEnd_660373 301412231334800018933783 := by
  unfold tailWord_660373
  simp only [CollatzResearch.WordTrace]
  refine ⟨24085782036588878574417773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16057188024392585716278515 24085782036588878574417773)
  ·
    refine ⟨9032168263720829465406665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24085782036588878574417773 9032168263720829465406665)
    ·
      refine ⟨6774126197790622099054999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9032168263720829465406665 6774126197790622099054999)
      ·
        refine ⟨10161189296685933148582499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6774126197790622099054999 10161189296685933148582499)
        ·
          refine ⟨15241783945028899722873749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10161189296685933148582499 15241783945028899722873749)
          ·
            refine ⟨714458622423229674509707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15241783945028899722873749 714458622423229674509707)
            ·
              refine ⟨1071687933634844511764561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714458622423229674509707 1071687933634844511764561)
              ·
                refine ⟨803765950226133383823421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1071687933634844511764561 803765950226133383823421)
                ·
                  refine ⟨301412231334800018933783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 803765950226133383823421 301412231334800018933783)
                  ·
                    rfl

theorem cell20_660373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_660373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660373 prefixEnd_660373 := by exact prefixLift 660373
  have htrace : WordTrace (prefixWord ++ tailWord_660373) baseStart_660373 baseEnd_660373 := by
    simpa [prefixWord, tailWord_660373, baseEnd_660373] using wordTrace_append hprefix tailTrace_660373
  have hstable : (prefixWord ++ tailWord_660373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660373).length < 2 ^ (prefixWord ++ tailWord_660373).sum := by decide
  have hdescent : baseEnd_660373 < baseStart_660373 := by decide
  rcases family_descends (prefixWord ++ tailWord_660373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660404 : List Nat := [2, 5, 2, 1, 1, 2, 1, 6]
def baseStart_660404 : Nat := 118140960795 + 660404 * 2 ^ 59
def prefixEnd_660404 : Nat := 4983230072969 + 3 ^ 40 * 660404 * 2
def baseEnd_660404 : Nat := 100475460193167229633441

theorem tailTrace_660404 : CollatzResearch.WordTrace tailWord_660404 prefixEnd_660404 100475460193167229633441 := by
  unfold tailWord_660404
  simp only [CollatzResearch.WordTrace]
  refine ⟨12043456349738285434398133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16057941799651047245864177 12043456349738285434398133)
  ·
    refine ⟨1129074032787964259474825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12043456349738285434398133 1129074032787964259474825)
    ·
      refine ⟨846805524590973194606119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1129074032787964259474825 846805524590973194606119)
      ·
        refine ⟨1270208286886459791909179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 846805524590973194606119 1270208286886459791909179)
        ·
          refine ⟨1905312430329689687863769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1270208286886459791909179 1905312430329689687863769)
          ·
            refine ⟨1428984322747267265897827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1905312430329689687863769 1428984322747267265897827)
            ·
              refine ⟨2143476484120900898846741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1428984322747267265897827 2143476484120900898846741)
              ·
                refine ⟨100475460193167229633441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2143476484120900898846741 100475460193167229633441)
                ·
                  rfl

theorem cell20_660404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_660404 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660404 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660404 prefixEnd_660404 := by exact prefixLift 660404
  have htrace : WordTrace (prefixWord ++ tailWord_660404) baseStart_660404 baseEnd_660404 := by
    simpa [prefixWord, tailWord_660404, baseEnd_660404] using wordTrace_append hprefix tailTrace_660404
  have hstable : (prefixWord ++ tailWord_660404).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660404).length < 2 ^ (prefixWord ++ tailWord_660404).sum := by decide
  have hdescent : baseEnd_660404 < baseStart_660404 := by decide
  rcases family_descends (prefixWord ++ tailWord_660404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660408 : List Nat := [2, 1, 2, 1, 2, 5, 1, 6]
def baseStart_660408 : Nat := 118140960795 + 660408 * 2 ^ 59
def prefixEnd_660408 : Nat := 4983230072969 + 3 ^ 40 * 660408 * 2
def baseEnd_660408 : Nat := 100476068762831817588991

theorem tailTrace_660408 : CollatzResearch.WordTrace tailWord_660408 prefixEnd_660408 100476068762831817588991 := by
  unfold tailWord_660408
  simp only [CollatzResearch.WordTrace]
  refine ⟨12043529295731039775970939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16058039060974719701294585 12043529295731039775970939)
  ·
    refine ⟨18065293943596559663956409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12043529295731039775970939 18065293943596559663956409)
    ·
      refine ⟨13548970457697419747967307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18065293943596559663956409 13548970457697419747967307)
      ·
        refine ⟨20323455686546129621950961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13548970457697419747967307 20323455686546129621950961)
        ·
          refine ⟨15242591764909597216463221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20323455686546129621950961 15242591764909597216463221)
          ·
            refine ⟨1428992977960274739043427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15242591764909597216463221 1428992977960274739043427)
            ·
              refine ⟨2143489466940412108565141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1428992977960274739043427 2143489466940412108565141)
              ·
                refine ⟨100476068762831817588991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2143489466940412108565141 100476068762831817588991)
                ·
                  rfl

theorem cell20_660408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_660408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660408 prefixEnd_660408 := by exact prefixLift 660408
  have htrace : WordTrace (prefixWord ++ tailWord_660408) baseStart_660408 baseEnd_660408 := by
    simpa [prefixWord, tailWord_660408, baseEnd_660408] using wordTrace_append hprefix tailTrace_660408
  have hstable : (prefixWord ++ tailWord_660408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660408).length < 2 ^ (prefixWord ++ tailWord_660408).sum := by decide
  have hdescent : baseEnd_660408 < baseStart_660408 := by decide
  rcases family_descends (prefixWord ++ tailWord_660408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660490 : List Nat := [3, 1, 2, 2, 3, 3, 2, 2, 2]
def baseStart_660490 : Nat := 118140960795 + 660490 * 2 ^ 59
def prefixEnd_660490 : Nat := 4983230072969 + 3 ^ 40 * 660490 * 2
def baseEnd_660490 : Nat := 301465633322867612033305

theorem tailTrace_660490 : CollatzResearch.WordTrace tailWord_660490 prefixEnd_660490 301465633322867612033305 := by
  unfold tailWord_660490
  simp only [CollatzResearch.WordTrace]
  refine ⟨6022512344291251889106731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16060032918110005037617949 6022512344291251889106731)
  ·
    refine ⟨9033768516436877833660097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6022512344291251889106731 9033768516436877833660097)
    ·
      refine ⟨6775326387327658375245073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9033768516436877833660097 6775326387327658375245073)
      ·
        refine ⟨5081494790495743781433805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6775326387327658375245073 5081494790495743781433805)
        ·
          refine ⟨1905560546435903918037677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5081494790495743781433805 1905560546435903918037677)
          ·
            refine ⟨714585204913463969264129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1905560546435903918037677 714585204913463969264129)
            ·
              refine ⟨535938903685097976948097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 714585204913463969264129 535938903685097976948097)
              ·
                refine ⟨401954177763823482711073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 535938903685097976948097 401954177763823482711073)
                ·
                  refine ⟨301465633322867612033305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 401954177763823482711073 301465633322867612033305)
                  ·
                    rfl

theorem cell20_660490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 2].length) (baseStart_660490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660490 prefixEnd_660490 := by exact prefixLift 660490
  have htrace : WordTrace (prefixWord ++ tailWord_660490) baseStart_660490 baseEnd_660490 := by
    simpa [prefixWord, tailWord_660490, baseEnd_660490] using wordTrace_append hprefix tailTrace_660490
  have hstable : (prefixWord ++ tailWord_660490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660490).length < 2 ^ (prefixWord ++ tailWord_660490).sum := by decide
  have hdescent : baseEnd_660490 < baseStart_660490 := by decide
  rcases family_descends (prefixWord ++ tailWord_660490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660501 : List Nat := [1, 3, 2, 1, 4, 3, 1, 5]
def baseStart_660501 : Nat := 118140960795 + 660501 * 2 ^ 59
def prefixEnd_660501 : Nat := 4983230072969 + 3 ^ 40 * 660501 * 2
def baseEnd_660501 : Nat := 100490218007533487555531

theorem tailTrace_660501 : CollatzResearch.WordTrace tailWord_660501 prefixEnd_660501 100490218007533487555531 := by
  unfold tailWord_660501
  simp only [CollatzResearch.WordTrace]
  refine ⟨24090450580125156435077357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16060300386750104290051571 24090450580125156435077357)
  ·
    refine ⟨9033918967546933663154009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24090450580125156435077357 9033918967546933663154009)
    ·
      refine ⟨6775439225660200247365507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9033918967546933663154009 6775439225660200247365507)
      ·
        refine ⟨10163158838490300371048261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6775439225660200247365507 10163158838490300371048261)
        ·
          refine ⟨1905592282216931319571549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10163158838490300371048261 1905592282216931319571549)
          ·
            refine ⟨714597105831349244839331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1905592282216931319571549 714597105831349244839331)
            ·
              refine ⟨1071895658747023867258997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714597105831349244839331 1071895658747023867258997)
              ·
                refine ⟨100490218007533487555531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1071895658747023867258997 100490218007533487555531)
                ·
                  rfl

theorem cell20_660501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 5].length) (baseStart_660501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660501 prefixEnd_660501 := by exact prefixLift 660501
  have htrace : WordTrace (prefixWord ++ tailWord_660501) baseStart_660501 baseEnd_660501 := by
    simpa [prefixWord, tailWord_660501, baseEnd_660501] using wordTrace_append hprefix tailTrace_660501
  have hstable : (prefixWord ++ tailWord_660501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660501).length < 2 ^ (prefixWord ++ tailWord_660501).sum := by decide
  have hdescent : baseEnd_660501 < baseStart_660501 := by decide
  rcases family_descends (prefixWord ++ tailWord_660501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660515 : List Nat := [1, 1, 1, 4, 3, 3, 1, 2, 4]
def baseStart_660515 : Nat := 118140960795 + 660515 * 2 ^ 59
def prefixEnd_660515 : Nat := 4983230072969 + 3 ^ 40 * 660515 * 2
def baseEnd_660515 : Nat := 301477044004078636199869

theorem tailTrace_660515 : CollatzResearch.WordTrace tailWord_660515 prefixEnd_660515 301477044004078636199869 := by
  unfold tailWord_660515
  simp only [CollatzResearch.WordTrace]
  refine ⟨24090961202074436826086999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16060640801382957884057999 24090961202074436826086999)
  ·
    refine ⟨36136441803111655239130499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24090961202074436826086999 36136441803111655239130499)
    ·
      refine ⟨54204662704667482858695749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36136441803111655239130499 54204662704667482858695749)
      ·
        refine ⟨10163374257125153036005453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54204662704667482858695749 10163374257125153036005453)
        ·
          refine ⟨3811265346421932388502045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10163374257125153036005453 3811265346421932388502045)
          ·
            refine ⟨1429224504908224645688267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3811265346421932388502045 1429224504908224645688267)
            ·
              refine ⟨2143836757362336968532401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1429224504908224645688267 2143836757362336968532401)
              ·
                refine ⟨1607877568021752726399301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2143836757362336968532401 1607877568021752726399301)
                ·
                  refine ⟨301477044004078636199869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1607877568021752726399301 301477044004078636199869)
                  ·
                    rfl

theorem cell20_660515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 4].length) (baseStart_660515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660515 prefixEnd_660515 := by exact prefixLift 660515
  have htrace : WordTrace (prefixWord ++ tailWord_660515) baseStart_660515 baseEnd_660515 := by
    simpa [prefixWord, tailWord_660515, baseEnd_660515] using wordTrace_append hprefix tailTrace_660515
  have hstable : (prefixWord ++ tailWord_660515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660515).length < 2 ^ (prefixWord ++ tailWord_660515).sum := by decide
  have hdescent : baseEnd_660515 < baseStart_660515 := by decide
  rcases family_descends (prefixWord ++ tailWord_660515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660529 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 5]
def baseStart_660529 : Nat := 118140960795 + 660529 * 2 ^ 59
def prefixEnd_660529 : Nat := 4983230072969 + 3 ^ 40 * 660529 * 2
def baseEnd_660529 : Nat := 301483433985556809733145

theorem tailTrace_660529 : CollatzResearch.WordTrace tailWord_660529 prefixEnd_660529 301483433985556809733145 := by
  unfold tailWord_660529
  simp only [CollatzResearch.WordTrace]
  refine ⟨24091471824023717217096641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16060981216015811478064427 24091471824023717217096641)
  ·
    refine ⟨18068603868017787912822481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24091471824023717217096641 18068603868017787912822481)
    ·
      refine ⟨13551452901013340934616861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18068603868017787912822481 13551452901013340934616861)
      ·
        refine ⟨5081794837880002850481323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13551452901013340934616861 5081794837880002850481323)
        ·
          refine ⟨7622692256820004275721985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5081794837880002850481323 7622692256820004275721985)
          ·
            refine ⟨5717019192615003206791489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7622692256820004275721985 5717019192615003206791489)
            ·
              refine ⟨4287764394461252405093617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5717019192615003206791489 4287764394461252405093617)
              ·
                refine ⟨3215823295845939303820213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4287764394461252405093617 3215823295845939303820213)
                ·
                  refine ⟨301483433985556809733145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3215823295845939303820213 301483433985556809733145)
                  ·
                    rfl

theorem cell20_660529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_660529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660529 prefixEnd_660529 := by exact prefixLift 660529
  have htrace : WordTrace (prefixWord ++ tailWord_660529) baseStart_660529 baseEnd_660529 := by
    simpa [prefixWord, tailWord_660529, baseEnd_660529] using wordTrace_append hprefix tailTrace_660529
  have hstable : (prefixWord ++ tailWord_660529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660529).length < 2 ^ (prefixWord ++ tailWord_660529).sum := by decide
  have hdescent : baseEnd_660529 < baseStart_660529 := by decide
  rcases family_descends (prefixWord ++ tailWord_660529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660542 : List Nat := [4, 2, 1, 3, 1, 3, 1, 2, 3]
def baseStart_660542 : Nat := 118140960795 + 660542 * 2 ^ 59
def prefixEnd_660542 : Nat := 4983230072969 + 3 ^ 40 * 660542 * 2
def baseEnd_660542 : Nat := 301489367539786542299759

theorem tailTrace_660542 : CollatzResearch.WordTrace tailWord_660542 prefixEnd_660542 301489367539786542299759 := by
  unfold tailWord_660542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3011493246622077554664985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16061297315317746958213253 3011493246622077554664985)
  ·
    refine ⟨2258619934966558165998739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3011493246622077554664985 2258619934966558165998739)
    ·
      refine ⟨3387929902449837248998109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2258619934966558165998739 3387929902449837248998109)
      ·
        refine ⟨1270473713418688968374291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3387929902449837248998109 1270473713418688968374291)
        ·
          refine ⟨1905710570128033452561437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1270473713418688968374291 1905710570128033452561437)
          ·
            refine ⟨714641463798012544710539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1905710570128033452561437 714641463798012544710539)
            ·
              refine ⟨1071962195697018817065809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714641463798012544710539 1071962195697018817065809)
              ·
                refine ⟨803971646772764112799357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1071962195697018817065809 803971646772764112799357)
                ·
                  refine ⟨301489367539786542299759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 803971646772764112799357 301489367539786542299759)
                  ·
                    rfl

theorem cell20_660542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_660542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660542 prefixEnd_660542 := by exact prefixLift 660542
  have htrace : WordTrace (prefixWord ++ tailWord_660542) baseStart_660542 baseEnd_660542 := by
    simpa [prefixWord, tailWord_660542, baseEnd_660542] using wordTrace_append hprefix tailTrace_660542
  have hstable : (prefixWord ++ tailWord_660542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660542).length < 2 ^ (prefixWord ++ tailWord_660542).sum := by decide
  have hdescent : baseEnd_660542 < baseStart_660542 := by decide
  rcases family_descends (prefixWord ++ tailWord_660542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660573 : List Nat := [1, 4, 4, 1, 2, 2, 2, 4]
def baseStart_660573 : Nat := 118140960795 + 660573 * 2 ^ 59
def prefixEnd_660573 : Nat := 4983230072969 + 3 ^ 40 * 660573 * 2
def baseEnd_660573 : Nat := 100501172261496070755433

theorem tailTrace_660573 : CollatzResearch.WordTrace tailWord_660573 prefixEnd_660573 100501172261496070755433 := by
  unfold tailWord_660573
  simp only [CollatzResearch.WordTrace]
  refine ⟨24093076635864312731698373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16062051090576208487798915 24093076635864312731698373)
  ·
    refine ⟨4517451869224558637193445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24093076635864312731698373 4517451869224558637193445)
    ·
      refine ⟨847022225479604744473771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4517451869224558637193445 847022225479604744473771)
      ·
        refine ⟨1270533338219407116710657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 847022225479604744473771 1270533338219407116710657)
        ·
          refine ⟨952900003664555337532993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1270533338219407116710657 952900003664555337532993)
          ·
            refine ⟨714675002748416503149745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 952900003664555337532993 714675002748416503149745)
            ·
              refine ⟨536006252061312377362309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 714675002748416503149745 536006252061312377362309)
              ·
                refine ⟨100501172261496070755433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 536006252061312377362309 100501172261496070755433)
                ·
                  rfl

theorem cell20_660573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 4].length) (baseStart_660573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660573 prefixEnd_660573 := by exact prefixLift 660573
  have htrace : WordTrace (prefixWord ++ tailWord_660573) baseStart_660573 baseEnd_660573 := by
    simpa [prefixWord, tailWord_660573, baseEnd_660573] using wordTrace_append hprefix tailTrace_660573
  have hstable : (prefixWord ++ tailWord_660573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660573).length < 2 ^ (prefixWord ++ tailWord_660573).sum := by decide
  have hdescent : baseEnd_660573 < baseStart_660573 := by decide
  rcases family_descends (prefixWord ++ tailWord_660573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660605 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 5]
def baseStart_660605 : Nat := 118140960795 + 660605 * 2 ^ 59
def prefixEnd_660605 : Nat := 4983230072969 + 3 ^ 40 * 660605 * 2
def baseEnd_660605 : Nat := 301518122456438323199501

theorem tailTrace_660605 : CollatzResearch.WordTrace tailWord_660605 prefixEnd_660605 301518122456438323199501 := by
  unfold tailWord_660605
  simp only [CollatzResearch.WordTrace]
  refine ⟨24094243771748382196863269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16062829181165588131242179 24094243771748382196863269)
  ·
    refine ⟨4517670707202821661911863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24094243771748382196863269 4517670707202821661911863)
    ·
      refine ⟨6776506060804232492867795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4517670707202821661911863 6776506060804232492867795)
      ·
        refine ⟨10164759091206348739301693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6776506060804232492867795 10164759091206348739301693)
        ·
          refine ⟨3811784659202380777238135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10164759091206348739301693 3811784659202380777238135)
          ·
            refine ⟨5717676988803571165857203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3811784659202380777238135 5717676988803571165857203)
            ·
              refine ⟨8576515483205356748785805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5717676988803571165857203 8576515483205356748785805)
              ·
                refine ⟨3216193306202008780794677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8576515483205356748785805 3216193306202008780794677)
                ·
                  refine ⟨301518122456438323199501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3216193306202008780794677 301518122456438323199501)
                  ·
                    rfl

theorem cell20_660605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_660605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660605 prefixEnd_660605 := by exact prefixLift 660605
  have htrace : WordTrace (prefixWord ++ tailWord_660605) baseStart_660605 baseEnd_660605 := by
    simpa [prefixWord, tailWord_660605, baseEnd_660605] using wordTrace_append hprefix tailTrace_660605
  have hstable : (prefixWord ++ tailWord_660605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660605).length < 2 ^ (prefixWord ++ tailWord_660605).sum := by decide
  have hdescent : baseEnd_660605 < baseStart_660605 := by decide
  rcases family_descends (prefixWord ++ tailWord_660605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660636 : List Nat := [2, 2, 3, 2, 1, 2, 2, 6]
def baseStart_660636 : Nat := 118140960795 + 660636 * 2 ^ 59
def prefixEnd_660636 : Nat := 4983230072969 + 3 ^ 40 * 660636 * 2
def baseEnd_660636 : Nat := 100510757233713331055347

theorem tailTrace_660636 : CollatzResearch.WordTrace tailWord_660636 prefixEnd_660636 100510757233713331055347 := by
  unfold tailWord_660636
  simp only [CollatzResearch.WordTrace]
  refine ⟨12047687217318037245620881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16063582956424049660827841 12047687217318037245620881)
  ·
    refine ⟨9035765412988527934215661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12047687217318037245620881 9035765412988527934215661)
    ·
      refine ⟨3388412029870697975330873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9035765412988527934215661 3388412029870697975330873)
      ·
        refine ⟨2541309022403023481498155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3388412029870697975330873 2541309022403023481498155)
        ·
          refine ⟨3811963533604535222247233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2541309022403023481498155 3811963533604535222247233)
          ·
            refine ⟨2858972650203401416685425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3811963533604535222247233 2858972650203401416685425)
            ·
              refine ⟨2144229487652551062514069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2858972650203401416685425 2144229487652551062514069)
              ·
                refine ⟨100510757233713331055347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2144229487652551062514069 100510757233713331055347)
                ·
                  rfl

theorem cell20_660636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_660636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660636 prefixEnd_660636 := by exact prefixLift 660636
  have htrace : WordTrace (prefixWord ++ tailWord_660636) baseStart_660636 baseEnd_660636 := by
    simpa [prefixWord, tailWord_660636, baseEnd_660636] using wordTrace_append hprefix tailTrace_660636
  have hstable : (prefixWord ++ tailWord_660636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660636).length < 2 ^ (prefixWord ++ tailWord_660636).sum := by decide
  have hdescent : baseEnd_660636 < baseStart_660636 := by decide
  rcases family_descends (prefixWord ++ tailWord_660636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660653 : List Nat := [1, 5, 2, 1, 4, 7]
def baseStart_660653 : Nat := 118140960795 + 660653 * 2 ^ 59
def prefixEnd_660653 : Nat := 4983230072969 + 3 ^ 40 * 660653 * 2
def baseEnd_660653 : Nat := 11168149294976425540715

theorem tailTrace_660653 : CollatzResearch.WordTrace tailWord_660653 prefixEnd_660653 11168149294976425540715 := by
  unfold tailWord_660653
  simp only [CollatzResearch.WordTrace]
  refine ⟨24095994475574486394610613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16063996317049657596407075 24095994475574486394610613)
  ·
    refine ⟨2258999482085108099494745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24095994475574486394610613 2258999482085108099494745)
    ·
      refine ⟨1694249611563831074621059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2258999482085108099494745 1694249611563831074621059)
      ·
        refine ⟨2541374417345746611931589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1694249611563831074621059 2541374417345746611931589)
        ·
          refine ⟨476507703252327489737173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2541374417345746611931589 476507703252327489737173)
          ·
            refine ⟨11168149294976425540715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 476507703252327489737173 11168149294976425540715)
            ·
              rfl

theorem cell20_660653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 7].length) (baseStart_660653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660653 prefixEnd_660653 := by exact prefixLift 660653
  have htrace : WordTrace (prefixWord ++ tailWord_660653) baseStart_660653 baseEnd_660653 := by
    simpa [prefixWord, tailWord_660653, baseEnd_660653] using wordTrace_append hprefix tailTrace_660653
  have hstable : (prefixWord ++ tailWord_660653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660653).length < 2 ^ (prefixWord ++ tailWord_660653).sum := by decide
  have hdescent : baseEnd_660653 < baseStart_660653 := by decide
  rcases family_descends (prefixWord ++ tailWord_660653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660695 : List Nat := [1, 1, 3, 2, 1, 2, 2, 8]
def baseStart_660695 : Nat := 118140960795 + 660695 * 2 ^ 59
def prefixEnd_660695 : Nat := 4983230072969 + 3 ^ 40 * 660695 * 2
def baseEnd_660695 : Nat := 100519733636266003399711

theorem tailTrace_660695 : CollatzResearch.WordTrace tailWord_660695 prefixEnd_660695 100519733636266003399711 := by
  unfold tailWord_660695
  simp only [CollatzResearch.WordTrace]
  refine ⟨24097526341422327567639539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16065017560948218378426359 24097526341422327567639539)
  ·
    refine ⟨36146289512133491351459309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24097526341422327567639539 36146289512133491351459309)
    ·
      refine ⟨13554858567050059256797241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36146289512133491351459309 13554858567050059256797241)
      ·
        refine ⟨10166143925287544442597931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13554858567050059256797241 10166143925287544442597931)
        ·
          refine ⟨15249215887931316663896897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10166143925287544442597931 15249215887931316663896897)
          ·
            refine ⟨11436911915948487497922673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15249215887931316663896897 11436911915948487497922673)
            ·
              refine ⟨8577683936961365623442005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11436911915948487497922673 8577683936961365623442005)
              ·
                refine ⟨100519733636266003399711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8577683936961365623442005 100519733636266003399711)
                ·
                  rfl

theorem cell20_660695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 8].length) (baseStart_660695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660695 prefixEnd_660695 := by exact prefixLift 660695
  have htrace : WordTrace (prefixWord ++ tailWord_660695) baseStart_660695 baseEnd_660695 := by
    simpa [prefixWord, tailWord_660695, baseEnd_660695] using wordTrace_append hprefix tailTrace_660695
  have hstable : (prefixWord ++ tailWord_660695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660695).length < 2 ^ (prefixWord ++ tailWord_660695).sum := by decide
  have hdescent : baseEnd_660695 < baseStart_660695 := by decide
  rcases family_descends (prefixWord ++ tailWord_660695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660722 : List Nat := [3, 2, 1, 3, 3, 1, 2, 1, 4]
def baseStart_660722 : Nat := 118140960795 + 660722 * 2 ^ 59
def prefixEnd_660722 : Nat := 4983230072969 + 3 ^ 40 * 660722 * 2
def baseEnd_660722 : Nat := 301571524444505916299023

theorem tailTrace_660722 : CollatzResearch.WordTrace tailWord_660722 prefixEnd_660722 301571524444505916299023 := by
  unfold tailWord_660722
  simp only [CollatzResearch.WordTrace]
  refine ⟨6024627778081127794718105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16065674074883007452581613 6024627778081127794718105)
  ·
    refine ⟨4518470833560845846038579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6024627778081127794718105 4518470833560845846038579)
    ·
      refine ⟨6777706250341268769057869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4518470833560845846038579 6777706250341268769057869)
      ·
        refine ⟨2541639843877975788396701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6777706250341268769057869 2541639843877975788396701)
        ·
          refine ⟨953114941454240920648763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2541639843877975788396701 953114941454240920648763)
          ·
            refine ⟨1429672412181361380973145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953114941454240920648763 1429672412181361380973145)
            ·
              refine ⟨1072254309136021035729859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1429672412181361380973145 1072254309136021035729859)
              ·
                refine ⟨1608381463704031553594789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1072254309136021035729859 1608381463704031553594789)
                ·
                  refine ⟨301571524444505916299023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1608381463704031553594789 301571524444505916299023)
                  ·
                    rfl

theorem cell20_660722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_660722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660722 prefixEnd_660722 := by exact prefixLift 660722
  have htrace : WordTrace (prefixWord ++ tailWord_660722) baseStart_660722 baseEnd_660722 := by
    simpa [prefixWord, tailWord_660722, baseEnd_660722] using wordTrace_append hprefix tailTrace_660722
  have hstable : (prefixWord ++ tailWord_660722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660722).length < 2 ^ (prefixWord ++ tailWord_660722).sum := by decide
  have hdescent : baseEnd_660722 < baseStart_660722 := by decide
  rcases family_descends (prefixWord ++ tailWord_660722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660750 : List Nat := [4, 1, 1, 2, 1, 4, 1, 6]
def baseStart_660750 : Nat := 118140960795 + 660750 * 2 ^ 59
def prefixEnd_660750 : Nat := 4983230072969 + 3 ^ 40 * 660750 * 2
def baseEnd_660750 : Nat := 100528101469154087788525

theorem tailTrace_660750 : CollatzResearch.WordTrace tailWord_660750 prefixEnd_660750 100528101469154087788525 := by
  unfold tailWord_660750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3012441544527883995111463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16066354904148714640594469 3012441544527883995111463)
  ·
    refine ⟨4518662316791825992667195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3012441544527883995111463 4518662316791825992667195)
    ·
      refine ⟨6777993475187738989000793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4518662316791825992667195 6777993475187738989000793)
      ·
        refine ⟨5083495106390804241750595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6777993475187738989000793 5083495106390804241750595)
        ·
          refine ⟨7625242659586206362625893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5083495106390804241750595 7625242659586206362625893)
          ·
            refine ⟨1429732998672413692992355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7625242659586206362625893 1429732998672413692992355)
            ·
              refine ⟨2144599498008620539488533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1429732998672413692992355 2144599498008620539488533)
              ·
                refine ⟨100528101469154087788525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2144599498008620539488533 100528101469154087788525)
                ·
                  rfl

theorem cell20_660750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_660750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660750 prefixEnd_660750 := by exact prefixLift 660750
  have htrace : WordTrace (prefixWord ++ tailWord_660750) baseStart_660750 baseEnd_660750 := by
    simpa [prefixWord, tailWord_660750, baseEnd_660750] using wordTrace_append hprefix tailTrace_660750
  have hstable : (prefixWord ++ tailWord_660750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660750).length < 2 ^ (prefixWord ++ tailWord_660750).sum := by decide
  have hdescent : baseEnd_660750 < baseStart_660750 := by decide
  rcases family_descends (prefixWord ++ tailWord_660750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660760 : List Nat := [2, 1, 2, 3, 1, 3, 3, 3, 2]
def baseStart_660760 : Nat := 118140960795 + 660760 * 2 ^ 59
def prefixEnd_660760 : Nat := 4983230072969 + 3 ^ 40 * 660760 * 2
def baseEnd_660760 : Nat := 301588868679946673032201

theorem tailTrace_660760 : CollatzResearch.WordTrace tailWord_660760 prefixEnd_660760 301588868679946673032201 := by
  unfold tailWord_660760
  simp only [CollatzResearch.WordTrace]
  refine ⟨12049948543093421834377867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16066598057457895779170489 12049948543093421834377867)
  ·
    refine ⟨18074922814640132751566801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12049948543093421834377867 18074922814640132751566801)
    ·
      refine ⟨13556192110980099563675101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18074922814640132751566801 13556192110980099563675101)
      ·
        refine ⟨5083572041617537336378163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13556192110980099563675101 5083572041617537336378163)
        ·
          refine ⟨7625358062426306004567245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5083572041617537336378163 7625358062426306004567245)
          ·
            refine ⟨2859509273409864751712717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7625358062426306004567245 2859509273409864751712717)
            ·
              refine ⟨1072315977528699281892269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2859509273409864751712717 1072315977528699281892269)
              ·
                refine ⟨402118491573262230709601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1072315977528699281892269 402118491573262230709601)
                ·
                  refine ⟨301588868679946673032201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402118491573262230709601 301588868679946673032201)
                  ·
                    rfl

theorem cell20_660760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 2].length) (baseStart_660760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660760 prefixEnd_660760 := by exact prefixLift 660760
  have htrace : WordTrace (prefixWord ++ tailWord_660760) baseStart_660760 baseEnd_660760 := by
    simpa [prefixWord, tailWord_660760, baseEnd_660760] using wordTrace_append hprefix tailTrace_660760
  have hstable : (prefixWord ++ tailWord_660760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660760).length < 2 ^ (prefixWord ++ tailWord_660760).sum := by decide
  have hdescent : baseEnd_660760 < baseStart_660760 := by decide
  rcases family_descends (prefixWord ++ tailWord_660760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660764 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 6]
def baseStart_660764 : Nat := 118140960795 + 660764 * 2 ^ 59
def prefixEnd_660764 : Nat := 4983230072969 + 3 ^ 40 * 660764 * 2
def baseEnd_660764 : Nat := 301590694388940436898851

theorem tailTrace_660764 : CollatzResearch.WordTrace tailWord_660764 prefixEnd_660764 301590694388940436898851 := by
  unfold tailWord_660764
  simp only [CollatzResearch.WordTrace]
  refine ⟨12050021489086176175950673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16066695318781568234600897 12050021489086176175950673)
  ·
    refine ⟨9037516116814632131963005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12050021489086176175950673 9037516116814632131963005)
    ·
      refine ⟨3389068543805487049486127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9037516116814632131963005 3389068543805487049486127)
      ·
        refine ⟨5083602815708230574229191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3389068543805487049486127 5083602815708230574229191)
        ·
          refine ⟨7625404223562345861343787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5083602815708230574229191 7625404223562345861343787)
          ·
            refine ⟨11438106335343518792015681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7625404223562345861343787 11438106335343518792015681)
            ·
              refine ⟨8578579751507639094011761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11438106335343518792015681 8578579751507639094011761)
              ·
                refine ⟨6433934813630729320508821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8578579751507639094011761 6433934813630729320508821)
                ·
                  refine ⟨301590694388940436898851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6433934813630729320508821 301590694388940436898851)
                  ·
                    rfl

theorem cell20_660764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_660764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660764 prefixEnd_660764 := by exact prefixLift 660764
  have htrace : WordTrace (prefixWord ++ tailWord_660764) baseStart_660764 baseEnd_660764 := by
    simpa [prefixWord, tailWord_660764, baseEnd_660764] using wordTrace_append hprefix tailTrace_660764
  have hstable : (prefixWord ++ tailWord_660764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660764).length < 2 ^ (prefixWord ++ tailWord_660764).sum := by decide
  have hdescent : baseEnd_660764 < baseStart_660764 := by decide
  rcases family_descends (prefixWord ++ tailWord_660764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660767 : List Nat := [1, 1, 2, 4, 5, 1, 6]
def baseStart_660767 : Nat := 118140960795 + 660767 * 2 ^ 59
def prefixEnd_660767 : Nat := 4983230072969 + 3 ^ 40 * 660767 * 2
def baseEnd_660767 : Nat := 33510229296742862199871

theorem tailTrace_660767 : CollatzResearch.WordTrace tailWord_660767 prefixEnd_660767 33510229296742862199871 := by
  unfold tailWord_660767
  simp only [CollatzResearch.WordTrace]
  refine ⟨24100152397161483864260555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16066768264774322576173703 24100152397161483864260555)
  ·
    refine ⟨36150228595742225796390833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24100152397161483864260555 36150228595742225796390833)
    ·
      refine ⟨27112671446806669347293125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36150228595742225796390833 27112671446806669347293125)
      ·
        refine ⟨5083625896276250502617461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27112671446806669347293125 5083625896276250502617461)
        ·
          refine ⟨476589927775898484620387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5083625896276250502617461 476589927775898484620387)
          ·
            refine ⟨714884891663847726930581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476589927775898484620387 714884891663847726930581)
            ·
              refine ⟨33510229296742862199871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 714884891663847726930581 33510229296742862199871)
              ·
                rfl

theorem cell20_660767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 6].length) (baseStart_660767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660767 prefixEnd_660767 := by exact prefixLift 660767
  have htrace : WordTrace (prefixWord ++ tailWord_660767) baseStart_660767 baseEnd_660767 := by
    simpa [prefixWord, tailWord_660767, baseEnd_660767] using wordTrace_append hprefix tailTrace_660767
  have hstable : (prefixWord ++ tailWord_660767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660767).length < 2 ^ (prefixWord ++ tailWord_660767).sum := by decide
  have hdescent : baseEnd_660767 < baseStart_660767 := by decide
  rcases family_descends (prefixWord ++ tailWord_660767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660771 : List Nat := [1, 1, 1, 4, 2, 3, 8]
def baseStart_660771 : Nat := 118140960795 + 660771 * 2 ^ 59
def prefixEnd_660771 : Nat := 4983230072969 + 3 ^ 40 * 660771 * 2
def baseEnd_660771 : Nat := 33510432153297724851721

theorem tailTrace_660771 : CollatzResearch.WordTrace tailWord_660771 prefixEnd_660771 33510432153297724851721 := by
  unfold tailWord_660771
  simp only [CollatzResearch.WordTrace]
  refine ⟨24100298289146992547406167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16066865526097995031604111 24100298289146992547406167)
  ·
    refine ⟨36150447433720488821109251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24100298289146992547406167 36150447433720488821109251)
    ·
      refine ⟨54225671150580733231663877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36150447433720488821109251 54225671150580733231663877)
      ·
        refine ⟨10167313340733887480936977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54225671150580733231663877 10167313340733887480936977)
        ·
          refine ⟨7625485005550415610702733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10167313340733887480936977 7625485005550415610702733)
          ·
            refine ⟨2859556877081405854013525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7625485005550415610702733 2859556877081405854013525)
            ·
              refine ⟨33510432153297724851721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2859556877081405854013525 33510432153297724851721)
              ·
                rfl

theorem cell20_660771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 8].length) (baseStart_660771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660771 prefixEnd_660771 := by exact prefixLift 660771
  have htrace : WordTrace (prefixWord ++ tailWord_660771) baseStart_660771 baseEnd_660771 := by
    simpa [prefixWord, tailWord_660771, baseEnd_660771] using wordTrace_append hprefix tailTrace_660771
  have hstable : (prefixWord ++ tailWord_660771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660771).length < 2 ^ (prefixWord ++ tailWord_660771).sum := by decide
  have hdescent : baseEnd_660771 < baseStart_660771 := by decide
  rcases family_descends (prefixWord ++ tailWord_660771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660809 : List Nat := [1, 2, 1, 1, 2, 3, 4, 6]
def baseStart_660809 : Nat := 118140960795 + 660809 * 2 ^ 59
def prefixEnd_660809 : Nat := 4983230072969 + 3 ^ 40 * 660809 * 2
def baseEnd_660809 : Nat := 100537077871706760132889

theorem tailTrace_660809 : CollatzResearch.WordTrace tailWord_660809 prefixEnd_660809 100537077871706760132889 := by
  unfold tailWord_660809
  simp only [CollatzResearch.WordTrace]
  refine ⟨24101684263009325037289481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16067789508672883358192987 24101684263009325037289481)
  ·
    refine ⟨18076263197256993777967111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24101684263009325037289481 18076263197256993777967111)
    ·
      refine ⟨27114394795885490666950667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18076263197256993777967111 27114394795885490666950667)
      ·
        refine ⟨40671592193828236000426001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27114394795885490666950667 40671592193828236000426001)
        ·
          refine ⟨30503694145371177000319501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40671592193828236000426001 30503694145371177000319501)
          ·
            refine ⟨11438885304514191375119813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30503694145371177000319501 11438885304514191375119813)
            ·
              refine ⟨2144790994596410882834965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11438885304514191375119813 2144790994596410882834965)
              ·
                refine ⟨100537077871706760132889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2144790994596410882834965 100537077871706760132889)
                ·
                  rfl

theorem cell20_660809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 6].length) (baseStart_660809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660809 prefixEnd_660809 := by exact prefixLift 660809
  have htrace : WordTrace (prefixWord ++ tailWord_660809) baseStart_660809 baseEnd_660809 := by
    simpa [prefixWord, tailWord_660809, baseEnd_660809] using wordTrace_append hprefix tailTrace_660809
  have hstable : (prefixWord ++ tailWord_660809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660809).length < 2 ^ (prefixWord ++ tailWord_660809).sum := by decide
  have hdescent : baseEnd_660809 < baseStart_660809 := by decide
  rcases family_descends (prefixWord ++ tailWord_660809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660819 : List Nat := [1, 1, 1, 2, 1, 1, 6, 5, 2]
def baseStart_660819 : Nat := 118140960795 + 660819 * 2 ^ 59
def prefixEnd_660819 : Nat := 4983230072969 + 3 ^ 40 * 660819 * 2
def baseEnd_660819 : Nat := 301615797887604690065293

theorem tailTrace_660819 : CollatzResearch.WordTrace tailWord_660819 prefixEnd_660819 301615797887604690065293 := by
  unfold tailWord_660819
  simp only [CollatzResearch.WordTrace]
  refine ⟨24102048992973096745153511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16068032661982064496769007 24102048992973096745153511)
  ·
    refine ⟨36153073489459645117730267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24102048992973096745153511 36153073489459645117730267)
    ·
      refine ⟨54229610234189467676595401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36153073489459645117730267 54229610234189467676595401)
      ·
        refine ⟨40672207675642100757446551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54229610234189467676595401 40672207675642100757446551)
        ·
          refine ⟨61008311513463151136169827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40672207675642100757446551 61008311513463151136169827)
          ·
            refine ⟨91512467270194726704254741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61008311513463151136169827 91512467270194726704254741)
            ·
              refine ⟨4289646903290377814261941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91512467270194726704254741 4289646903290377814261941)
              ·
                refine ⟨402154397183472920087057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4289646903290377814261941 402154397183472920087057)
                ·
                  refine ⟨301615797887604690065293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402154397183472920087057 301615797887604690065293)
                  ·
                    rfl

theorem cell20_660819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 2].length) (baseStart_660819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660819 prefixEnd_660819 := by exact prefixLift 660819
  have htrace : WordTrace (prefixWord ++ tailWord_660819) baseStart_660819 baseEnd_660819 := by
    simpa [prefixWord, tailWord_660819, baseEnd_660819] using wordTrace_append hprefix tailTrace_660819
  have hstable : (prefixWord ++ tailWord_660819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660819).length < 2 ^ (prefixWord ++ tailWord_660819).sum := by decide
  have hdescent : baseEnd_660819 < baseStart_660819 := by decide
  rcases family_descends (prefixWord ++ tailWord_660819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660822 : List Nat := [5, 2, 3, 1, 9]
def baseStart_660822 : Nat := 118140960795 + 660822 * 2 ^ 59
def prefixEnd_660822 : Nat := 4983230072969 + 3 ^ 40 * 660822 * 2
def baseEnd_660822 : Nat := 3723668730485802629201

theorem tailTrace_660822 : CollatzResearch.WordTrace tailWord_660822 prefixEnd_660822 3723668730485802629201 := by
  unfold tailWord_660822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1506384900747639266094545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16068105607974818838341813 1506384900747639266094545)
  ·
    refine ⟨1129788675560729449570909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1506384900747639266094545 1129788675560729449570909)
    ·
      refine ⟨423670753335273543589091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1129788675560729449570909 423670753335273543589091)
      ·
        refine ⟨635506130002910315383637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423670753335273543589091 635506130002910315383637)
        ·
          refine ⟨3723668730485802629201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 635506130002910315383637 3723668730485802629201)
          ·
            rfl

theorem cell20_660822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 9].length) (baseStart_660822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660822 prefixEnd_660822 := by exact prefixLift 660822
  have htrace : WordTrace (prefixWord ++ tailWord_660822) baseStart_660822 baseEnd_660822 := by
    simpa [prefixWord, tailWord_660822, baseEnd_660822] using wordTrace_append hprefix tailTrace_660822
  have hstable : (prefixWord ++ tailWord_660822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660822).length < 2 ^ (prefixWord ++ tailWord_660822).sum := by decide
  have hdescent : baseEnd_660822 < baseStart_660822 := by decide
  rcases family_descends (prefixWord ++ tailWord_660822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660836 : List Nat := [2, 3, 1, 1, 3, 3, 1, 4, 2]
def baseStart_660836 : Nat := 118140960795 + 660836 * 2 ^ 59
def prefixEnd_660836 : Nat := 4983230072969 + 3 ^ 40 * 660836 * 2
def baseEnd_660836 : Nat := 301623557150828186498557

theorem tailTrace_660836 : CollatzResearch.WordTrace tailWord_660836 prefixEnd_660836 301623557150828186498557 := by
  unfold tailWord_660836
  simp only [CollatzResearch.WordTrace]
  refine ⟨12051334516955754324261181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16068446022607672432348241 12051334516955754324261181)
  ·
    refine ⟨4519250443858407871597943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12051334516955754324261181 4519250443858407871597943)
    ·
      refine ⟨6778875665787611807396915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4519250443858407871597943 6778875665787611807396915)
      ·
        refine ⟨10168313498681417711095373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6778875665787611807396915 10168313498681417711095373)
        ·
          refine ⟨3813117562005531641660765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10168313498681417711095373 3813117562005531641660765)
          ·
            refine ⟨1429919085752074365622787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3813117562005531641660765 1429919085752074365622787)
            ·
              refine ⟨2144878628628111548434181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1429919085752074365622787 2144878628628111548434181)
              ·
                refine ⟨402164742867770915331409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2144878628628111548434181 402164742867770915331409)
                ·
                  refine ⟨301623557150828186498557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402164742867770915331409 301623557150828186498557)
                  ·
                    rfl

theorem cell20_660836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_660836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660836 prefixEnd_660836 := by exact prefixLift 660836
  have htrace : WordTrace (prefixWord ++ tailWord_660836) baseStart_660836 baseEnd_660836 := by
    simpa [prefixWord, tailWord_660836, baseEnd_660836] using wordTrace_append hprefix tailTrace_660836
  have hstable : (prefixWord ++ tailWord_660836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660836).length < 2 ^ (prefixWord ++ tailWord_660836).sum := by decide
  have hdescent : baseEnd_660836 < baseStart_660836 := by decide
  rcases family_descends (prefixWord ++ tailWord_660836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660888 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 5]
def baseStart_660888 : Nat := 118140960795 + 660888 * 2 ^ 59
def prefixEnd_660888 : Nat := 4983230072969 + 3 ^ 40 * 660888 * 2
def baseEnd_660888 : Nat := 301647291367747116765011

theorem tailTrace_660888 : CollatzResearch.WordTrace tailWord_660888 prefixEnd_660888 301647291367747116765011 := by
  unfold tailWord_660888
  simp only [CollatzResearch.WordTrace]
  refine ⟨12052282814861560764707659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16069710419815414352943545 12052282814861560764707659)
  ·
    refine ⟨18078424222292341147061489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12052282814861560764707659 18078424222292341147061489)
    ·
      refine ⟨13558818166719255860296117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18078424222292341147061489 13558818166719255860296117)
      ·
        refine ⟨1271139203129930236902761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13558818166719255860296117 1271139203129930236902761)
        ·
          refine ⟨953354402347447677677071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1271139203129930236902761 953354402347447677677071)
          ·
            refine ⟨1430031603521171516515607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953354402347447677677071 1430031603521171516515607)
            ·
              refine ⟨2145047405281757274773411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1430031603521171516515607 2145047405281757274773411)
              ·
                refine ⟨3217571107922635912160117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2145047405281757274773411 3217571107922635912160117)
                ·
                  refine ⟨301647291367747116765011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3217571107922635912160117 301647291367747116765011)
                  ·
                    rfl

theorem cell20_660888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_660888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660888 prefixEnd_660888 := by exact prefixLift 660888
  have htrace : WordTrace (prefixWord ++ tailWord_660888) baseStart_660888 baseEnd_660888 := by
    simpa [prefixWord, tailWord_660888, baseEnd_660888] using wordTrace_append hprefix tailTrace_660888
  have hstable : (prefixWord ++ tailWord_660888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660888).length < 2 ^ (prefixWord ++ tailWord_660888).sum := by decide
  have hdescent : baseEnd_660888 < baseStart_660888 := by decide
  rcases family_descends (prefixWord ++ tailWord_660888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660895 : List Nat := [1, 1, 2, 5, 1, 3, 2, 1, 4]
def baseStart_660895 : Nat := 118140960795 + 660895 * 2 ^ 59
def prefixEnd_660895 : Nat := 4983230072969 + 3 ^ 40 * 660895 * 2
def baseEnd_660895 : Nat := 301650486358486203531649

theorem tailTrace_660895 : CollatzResearch.WordTrace tailWord_660895 prefixEnd_660895 301650486358486203531649 := by
  unfold tailWord_660895
  simp only [CollatzResearch.WordTrace]
  refine ⟨24104820940697761724920139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16069880627131841149946759 24104820940697761724920139)
  ·
    refine ⟨36157231411046642587380209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24104820940697761724920139 36157231411046642587380209)
    ·
      refine ⟨27117923558284981940535157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36157231411046642587380209 27117923558284981940535157)
      ·
        refine ⟨2542305333589217056925171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27117923558284981940535157 2542305333589217056925171)
        ·
          refine ⟨3813458000383825585387757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2542305333589217056925171 3813458000383825585387757)
          ·
            refine ⟨1430046750143934594520409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3813458000383825585387757 1430046750143934594520409)
            ·
              refine ⟨1072535062607950945890307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1430046750143934594520409 1072535062607950945890307)
              ·
                refine ⟨1608802593911926418835461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1072535062607950945890307 1608802593911926418835461)
                ·
                  refine ⟨301650486358486203531649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1608802593911926418835461 301650486358486203531649)
                  ·
                    rfl

theorem cell20_660895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 4].length) (baseStart_660895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660895 prefixEnd_660895 := by exact prefixLift 660895
  have htrace : WordTrace (prefixWord ++ tailWord_660895) baseStart_660895 baseEnd_660895 := by
    simpa [prefixWord, tailWord_660895, baseEnd_660895] using wordTrace_append hprefix tailTrace_660895
  have hstable : (prefixWord ++ tailWord_660895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660895).length < 2 ^ (prefixWord ++ tailWord_660895).sum := by decide
  have hdescent : baseEnd_660895 < baseStart_660895 := by decide
  rcases family_descends (prefixWord ++ tailWord_660895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660940 : List Nat := [2, 2, 1, 4, 2, 3, 6]
def baseStart_660940 : Nat := 118140960795 + 660940 * 2 ^ 59
def prefixEnd_660940 : Nat := 4983230072969 + 3 ^ 40 * 660940 * 2
def baseEnd_660940 : Nat := 33519002842740671892385

theorem tailTrace_660940 : CollatzResearch.WordTrace tailWord_660940 prefixEnd_660940 33519002842740671892385 := by
  unfold tailWord_660940
  simp only [CollatzResearch.WordTrace]
  refine ⟨12053231112767367205154137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16070974817023156273538849 12053231112767367205154137)
  ·
    refine ⟨9039923334575525403865603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12053231112767367205154137 9039923334575525403865603)
    ·
      refine ⟨13559885001863288105798405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9039923334575525403865603 13559885001863288105798405)
      ·
        refine ⟨2542478437849366519837201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13559885001863288105798405 2542478437849366519837201)
        ·
          refine ⟨1906858828387024889877901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2542478437849366519837201 1906858828387024889877901)
          ·
            refine ⟨715072060645134333704213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1906858828387024889877901 715072060645134333704213)
            ·
              refine ⟨33519002842740671892385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 715072060645134333704213 33519002842740671892385)
              ·
                rfl

theorem cell20_660940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 6].length) (baseStart_660940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660940 prefixEnd_660940 := by exact prefixLift 660940
  have htrace : WordTrace (prefixWord ++ tailWord_660940) baseStart_660940 baseEnd_660940 := by
    simpa [prefixWord, tailWord_660940, baseEnd_660940] using wordTrace_append hprefix tailTrace_660940
  have hstable : (prefixWord ++ tailWord_660940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660940).length < 2 ^ (prefixWord ++ tailWord_660940).sum := by decide
  have hdescent : baseEnd_660940 < baseStart_660940 := by decide
  rcases family_descends (prefixWord ++ tailWord_660940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660950 : List Nat := [5, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_660950 : Nat := 118140960795 + 660950 * 2 ^ 59
def prefixEnd_660950 : Nat := 4983230072969 + 3 ^ 40 * 660950 * 2
def baseEnd_660950 : Nat := 301675589857150456698091

theorem tailTrace_660950 : CollatzResearch.WordTrace tailWord_660950 prefixEnd_660950 301675589857150456698091 := by
  unfold tailWord_660950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1506676684718656632385769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16071217970332337412114869 1506676684718656632385769)
  ·
    refine ⟨1130007513538992474289327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1506676684718656632385769 1130007513538992474289327)
    ·
      refine ⟨1695011270308488711433991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1130007513538992474289327 1695011270308488711433991)
      ·
        refine ⟨2542516905462733067150987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1695011270308488711433991 2542516905462733067150987)
        ·
          refine ⟨3813775358194099600726481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2542516905462733067150987 3813775358194099600726481)
          ·
            refine ⟨2860331518645574700544861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3813775358194099600726481 2860331518645574700544861)
            ·
              refine ⟨1072624319492090512704323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2860331518645574700544861 1072624319492090512704323)
              ·
                refine ⟨1608936479238135769056485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1072624319492090512704323 1608936479238135769056485)
                ·
                  refine ⟨301675589857150456698091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1608936479238135769056485 301675589857150456698091)
                  ·
                    rfl

theorem cell20_660950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_660950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660950 prefixEnd_660950 := by exact prefixLift 660950
  have htrace : WordTrace (prefixWord ++ tailWord_660950) baseStart_660950 baseEnd_660950 := by
    simpa [prefixWord, tailWord_660950, baseEnd_660950] using wordTrace_append hprefix tailTrace_660950
  have hstable : (prefixWord ++ tailWord_660950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660950).length < 2 ^ (prefixWord ++ tailWord_660950).sum := by decide
  have hdescent : baseEnd_660950 < baseStart_660950 := by decide
  rcases family_descends (prefixWord ++ tailWord_660950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660961 : List Nat := [1, 2, 3, 1, 2, 3, 1, 7]
def baseStart_660961 : Nat := 118140960795 + 660961 * 2 ^ 59
def prefixEnd_660961 : Nat := 4983230072969 + 3 ^ 40 * 660961 * 2
def baseEnd_660961 : Nat := 100560203518961102443793

theorem tailTrace_660961 : CollatzResearch.WordTrace tailWord_660961 prefixEnd_660961 100560203518961102443793 := by
  unfold tailWord_660961
  simp only [CollatzResearch.WordTrace]
  refine ⟨24107228158458654996822737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16071485438972436664548491 24107228158458654996822737)
  ·
    refine ⟨18080421118843991247617053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24107228158458654996822737 18080421118843991247617053)
    ·
      refine ⟨6780157919566496717856395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18080421118843991247617053 6780157919566496717856395)
      ·
        refine ⟨10170236879349745076784593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6780157919566496717856395 10170236879349745076784593)
        ·
          refine ⟨7627677659512308807588445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10170236879349745076784593 7627677659512308807588445)
          ·
            refine ⟨2860379122317115802845667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7627677659512308807588445 2860379122317115802845667)
            ·
              refine ⟨4290568683475673704268501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2860379122317115802845667 4290568683475673704268501)
              ·
                refine ⟨100560203518961102443793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4290568683475673704268501 100560203518961102443793)
                ·
                  rfl

theorem cell20_660961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 7].length) (baseStart_660961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660961 prefixEnd_660961 := by exact prefixLift 660961
  have htrace : WordTrace (prefixWord ++ tailWord_660961) baseStart_660961 baseEnd_660961 := by
    simpa [prefixWord, tailWord_660961, baseEnd_660961] using wordTrace_append hprefix tailTrace_660961
  have hstable : (prefixWord ++ tailWord_660961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660961).length < 2 ^ (prefixWord ++ tailWord_660961).sum := by decide
  have hdescent : baseEnd_660961 < baseStart_660961 := by decide
  rcases family_descends (prefixWord ++ tailWord_660961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660978 : List Nat := [3, 2, 1, 4, 1, 1, 2, 6]
def baseStart_660978 : Nat := 118140960795 + 660978 * 2 ^ 59
def prefixEnd_660978 : Nat := 4983230072969 + 3 ^ 40 * 660978 * 2
def baseEnd_660978 : Nat := 100562789940035601254881

theorem tailTrace_660978 : CollatzResearch.WordTrace tailWord_660978 prefixEnd_660978 100562789940035601254881 := by
  unfold tailWord_660978
  simp only [CollatzResearch.WordTrace]
  refine ⟨6026962049849266725047897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16071898799598044600127725 6026962049849266725047897)
  ·
    refine ⟨4520221537386950043785923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6026962049849266725047897 4520221537386950043785923)
    ·
      refine ⟨6780332306080425065678885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4520221537386950043785923 6780332306080425065678885)
      ·
        refine ⟨1271312307390079699814791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6780332306080425065678885 1271312307390079699814791)
        ·
          refine ⟨1906968461085119549722187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1271312307390079699814791 1906968461085119549722187)
          ·
            refine ⟨2860452691627679324583281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1906968461085119549722187 2860452691627679324583281)
            ·
              refine ⟨2145339518720759493437461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2860452691627679324583281 2145339518720759493437461)
              ·
                refine ⟨100562789940035601254881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2145339518720759493437461 100562789940035601254881)
                ·
                  rfl

theorem cell20_660978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_660978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660978 prefixEnd_660978 := by exact prefixLift 660978
  have htrace : WordTrace (prefixWord ++ tailWord_660978) baseStart_660978 baseEnd_660978 := by
    simpa [prefixWord, tailWord_660978, baseEnd_660978] using wordTrace_append hprefix tailTrace_660978
  have hstable : (prefixWord ++ tailWord_660978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660978).length < 2 ^ (prefixWord ++ tailWord_660978).sum := by decide
  have hdescent : baseEnd_660978 < baseStart_660978 := by decide
  rcases family_descends (prefixWord ++ tailWord_660978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660999 : List Nat := [1, 1, 4, 3, 2, 9]
def baseStart_660999 : Nat := 118140960795 + 660999 * 2 ^ 59
def prefixEnd_660999 : Nat := 4983230072969 + 3 ^ 40 * 660999 * 2
def baseEnd_660999 : Nat := 11173998325641632002391

theorem tailTrace_660999 : CollatzResearch.WordTrace tailWord_660999 prefixEnd_660999 11173998325641632002391 := by
  unfold tailWord_660999
  simp only [CollatzResearch.WordTrace]
  refine ⟨24108614132320987486706051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16072409421547324991137367 24108614132320987486706051)
  ·
    refine ⟨36162921198481481230059077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24108614132320987486706051 36162921198481481230059077)
    ·
      refine ⟨6780547724715277730636077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36162921198481481230059077 6780547724715277730636077)
      ·
        refine ⟨2542705396768229148988529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6780547724715277730636077 2542705396768229148988529)
        ·
          refine ⟨1907029047576171861741397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2542705396768229148988529 1907029047576171861741397)
          ·
            refine ⟨11173998325641632002391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1907029047576171861741397 11173998325641632002391)
            ·
              rfl

theorem cell20_660999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 9].length) (baseStart_660999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_660999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_660999 prefixEnd_660999 := by exact prefixLift 660999
  have htrace : WordTrace (prefixWord ++ tailWord_660999) baseStart_660999 baseEnd_660999 := by
    simpa [prefixWord, tailWord_660999, baseEnd_660999] using wordTrace_append hprefix tailTrace_660999
  have hstable : (prefixWord ++ tailWord_660999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660999).length < 2 ^ (prefixWord ++ tailWord_660999).sum := by decide
  have hdescent : baseEnd_660999 < baseStart_660999 := by decide
  rcases family_descends (prefixWord ++ tailWord_660999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661002 : List Nat := [3, 1, 2, 2, 2, 3, 2, 2, 3]
def baseStart_661002 : Nat := 118140960795 + 661002 * 2 ^ 59
def prefixEnd_661002 : Nat := 4983230072969 + 3 ^ 40 * 661002 * 2
def baseEnd_661002 : Nat := 301699324074069386964545

theorem tailTrace_661002 : CollatzResearch.WordTrace tailWord_661002 prefixEnd_661002 301699324074069386964545 := by
  unfold tailWord_661002
  simp only [CollatzResearch.WordTrace]
  refine ⟨6027180887827529749766315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16072482367540079332710173 6027180887827529749766315)
  ·
    refine ⟨9040771331741294624649473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6027180887827529749766315 9040771331741294624649473)
    ·
      refine ⟨6780578498805970968487105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9040771331741294624649473 6780578498805970968487105)
      ·
        refine ⟨5085433874104478226365329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6780578498805970968487105 5085433874104478226365329)
        ·
          refine ⟨3814075405578358669773997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5085433874104478226365329 3814075405578358669773997)
          ·
            refine ⟨1430278277091884501165249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3814075405578358669773997 1430278277091884501165249)
            ·
              refine ⟨1072708707818913375873937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1430278277091884501165249 1072708707818913375873937)
              ·
                refine ⟨804531530864185031905453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1072708707818913375873937 804531530864185031905453)
                ·
                  refine ⟨301699324074069386964545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 804531530864185031905453 301699324074069386964545)
                  ·
                    rfl

theorem cell20_661002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_661002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661002 prefixEnd_661002 := by exact prefixLift 661002
  have htrace : WordTrace (prefixWord ++ tailWord_661002) baseStart_661002 baseEnd_661002 := by
    simpa [prefixWord, tailWord_661002, baseEnd_661002] using wordTrace_append hprefix tailTrace_661002
  have hstable : (prefixWord ++ tailWord_661002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661002).length < 2 ^ (prefixWord ++ tailWord_661002).sum := by decide
  have hdescent : baseEnd_661002 < baseStart_661002 := by decide
  rcases family_descends (prefixWord ++ tailWord_661002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661009 : List Nat := [1, 2, 2, 1, 1, 2, 5, 4, 2]
def baseStart_661009 : Nat := 118140960795 + 661009 * 2 ^ 59
def prefixEnd_661009 : Nat := 4983230072969 + 3 ^ 40 * 661009 * 2
def baseEnd_661009 : Nat := 301702519064808473731183

theorem tailTrace_661009 : CollatzResearch.WordTrace tailWord_661009 prefixEnd_661009 301702519064808473731183 := by
  unfold tailWord_661009
  simp only [CollatzResearch.WordTrace]
  refine ⟨24108978862284759194570081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16072652574856506129713387 24108978862284759194570081)
  ·
    refine ⟨18081734146713569395927561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24108978862284759194570081 18081734146713569395927561)
    ·
      refine ⟨13561300610035177046945671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18081734146713569395927561 13561300610035177046945671)
      ·
        refine ⟨20341950915052765570418507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13561300610035177046945671 20341950915052765570418507)
        ·
          refine ⟨30512926372579148355627761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20341950915052765570418507 30512926372579148355627761)
          ·
            refine ⟨22884694779434361266720821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30512926372579148355627761 22884694779434361266720821)
            ·
              refine ⟨2145440135571971368755077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22884694779434361266720821 2145440135571971368755077)
              ·
                refine ⟨402270025419744631641577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2145440135571971368755077 402270025419744631641577)
                ·
                  refine ⟨301702519064808473731183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402270025419744631641577 301702519064808473731183)
                  ·
                    rfl

theorem cell20_661009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 2].length) (baseStart_661009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661009 prefixEnd_661009 := by exact prefixLift 661009
  have htrace : WordTrace (prefixWord ++ tailWord_661009) baseStart_661009 baseEnd_661009 := by
    simpa [prefixWord, tailWord_661009, baseEnd_661009] using wordTrace_append hprefix tailTrace_661009
  have hstable : (prefixWord ++ tailWord_661009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661009).length < 2 ^ (prefixWord ++ tailWord_661009).sum := by decide
  have hdescent : baseEnd_661009 < baseStart_661009 := by decide
  rcases family_descends (prefixWord ++ tailWord_661009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661012 : List Nat := [2, 4, 3, 1, 2, 2, 1, 5]
def baseStart_661012 : Nat := 118140960795 + 661012 * 2 ^ 59
def prefixEnd_661012 : Nat := 4983230072969 + 3 ^ 40 * 661012 * 2
def baseEnd_661012 : Nat := 100567962782184598877057

theorem tailTrace_661012 : CollatzResearch.WordTrace tailWord_661012 prefixEnd_661012 100567962782184598877057 := by
  unfold tailWord_661012
  simp only [CollatzResearch.WordTrace]
  refine ⟨12054544140636945353464645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16072725520849260471286193 12054544140636945353464645)
  ·
    refine ⟨2260227026369427253774621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12054544140636945353464645 2260227026369427253774621)
    ·
      refine ⟨847585134888535220165483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2260227026369427253774621 847585134888535220165483)
      ·
        refine ⟨1271377702332802830248225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 847585134888535220165483 1271377702332802830248225)
        ·
          refine ⟨953533276749602122686169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1271377702332802830248225 953533276749602122686169)
          ·
            refine ⟨715149957562201592014627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 953533276749602122686169 715149957562201592014627)
            ·
              refine ⟨1072724936343302388021941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715149957562201592014627 1072724936343302388021941)
              ·
                refine ⟨100567962782184598877057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1072724936343302388021941 100567962782184598877057)
                ·
                  rfl

theorem cell20_661012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 5].length) (baseStart_661012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661012 prefixEnd_661012 := by exact prefixLift 661012
  have htrace : WordTrace (prefixWord ++ tailWord_661012) baseStart_661012 baseEnd_661012 := by
    simpa [prefixWord, tailWord_661012, baseEnd_661012] using wordTrace_append hprefix tailTrace_661012
  have hstable : (prefixWord ++ tailWord_661012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661012).length < 2 ^ (prefixWord ++ tailWord_661012).sum := by decide
  have hdescent : baseEnd_661012 < baseStart_661012 := by decide
  rcases family_descends (prefixWord ++ tailWord_661012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661022 : List Nat := [4, 3, 3, 1, 1, 1, 1, 2, 4]
def baseStart_661022 : Nat := 118140960795 + 661022 * 2 ^ 59
def prefixEnd_661022 : Nat := 4983230072969 + 3 ^ 40 * 661022 * 2
def baseEnd_661022 : Nat := 301708452619038206297797

theorem tailTrace_661022 : CollatzResearch.WordTrace tailWord_661022 prefixEnd_661022 301708452619038206297797 := by
  unfold tailWord_661022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3013681626404707801849165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16072968674158441609862213 3013681626404707801849165)
  ·
    refine ⟨1130130609901765425693437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3013681626404707801849165 1130130609901765425693437)
    ·
      refine ⟨423798978713162034635039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1130130609901765425693437 423798978713162034635039)
      ·
        refine ⟨635698468069743051952559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423798978713162034635039 635698468069743051952559)
        ·
          refine ⟨953547702104614577928839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635698468069743051952559 953547702104614577928839)
          ·
            refine ⟨1430321553156921866893259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953547702104614577928839 1430321553156921866893259)
            ·
              refine ⟨2145482329735382800339889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1430321553156921866893259 2145482329735382800339889)
              ·
                refine ⟨1609111747301537100254917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2145482329735382800339889 1609111747301537100254917)
                ·
                  refine ⟨301708452619038206297797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1609111747301537100254917 301708452619038206297797)
                  ·
                    rfl

theorem cell20_661022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_661022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661022 prefixEnd_661022 := by exact prefixLift 661022
  have htrace : WordTrace (prefixWord ++ tailWord_661022) baseStart_661022 baseEnd_661022 := by
    simpa [prefixWord, tailWord_661022, baseEnd_661022] using wordTrace_append hprefix tailTrace_661022
  have hstable : (prefixWord ++ tailWord_661022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661022).length < 2 ^ (prefixWord ++ tailWord_661022).sum := by decide
  have hdescent : baseEnd_661022 < baseStart_661022 := by decide
  rcases family_descends (prefixWord ++ tailWord_661022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661023 : List Nat := [1, 1, 2, 4, 1, 1, 4, 3, 3]
def baseStart_661023 : Nat := 118140960795 + 661023 * 2 ^ 59
def prefixEnd_661023 : Nat := 4983230072969 + 3 ^ 40 * 661023 * 2
def baseEnd_661023 : Nat := 301708909046286647264459

theorem tailTrace_661023 : CollatzResearch.WordTrace tailWord_661023 prefixEnd_661023 301708909046286647264459 := by
  unfold tailWord_661023
  simp only [CollatzResearch.WordTrace]
  refine ⟨24109489484234039585579723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16072992989489359723719815 24109489484234039585579723)
  ·
    refine ⟨36164234226351059378369585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24109489484234039585579723 36164234226351059378369585)
    ·
      refine ⟨27123175669763294533777189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36164234226351059378369585 27123175669763294533777189)
      ·
        refine ⟨5085595438080617725083223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27123175669763294533777189 5085595438080617725083223)
        ·
          refine ⟨7628393157120926587624835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5085595438080617725083223 7628393157120926587624835)
          ·
            refine ⟨11442589735681389881437253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7628393157120926587624835 11442589735681389881437253)
            ·
              refine ⟨2145485575440260602769485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11442589735681389881437253 2145485575440260602769485)
              ·
                refine ⟨804557090790097726038557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2145485575440260602769485 804557090790097726038557)
                ·
                  refine ⟨301708909046286647264459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 804557090790097726038557 301708909046286647264459)
                  ·
                    rfl

theorem cell20_661023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 3].length) (baseStart_661023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661023 prefixEnd_661023 := by exact prefixLift 661023
  have htrace : WordTrace (prefixWord ++ tailWord_661023) baseStart_661023 baseEnd_661023 := by
    simpa [prefixWord, tailWord_661023, baseEnd_661023] using wordTrace_append hprefix tailTrace_661023
  have hstable : (prefixWord ++ tailWord_661023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661023).length < 2 ^ (prefixWord ++ tailWord_661023).sum := by decide
  have hdescent : baseEnd_661023 < baseStart_661023 := by decide
  rcases family_descends (prefixWord ++ tailWord_661023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661047 : List Nat := [1, 1, 3, 1, 2, 4, 1, 5, 2]
def baseStart_661047 : Nat := 118140960795 + 661047 * 2 ^ 59
def prefixEnd_661047 : Nat := 4983230072969 + 3 ^ 40 * 661047 * 2
def baseEnd_661047 : Nat := 301719863300249230464361

theorem tailTrace_661047 : CollatzResearch.WordTrace tailWord_661047 prefixEnd_661047 301719863300249230464361 := by
  unfold tailWord_661047
  simp only [CollatzResearch.WordTrace]
  refine ⟨24110364836147091684453395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16073576557431394456302263 24110364836147091684453395)
  ·
    refine ⟨36165547254220637526680093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24110364836147091684453395 36165547254220637526680093)
    ·
      refine ⟨13562080220332739072505035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36165547254220637526680093 13562080220332739072505035)
      ·
        refine ⟨20343120330499108608757553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13562080220332739072505035 20343120330499108608757553)
        ·
          refine ⟨15257340247874331456568165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20343120330499108608757553 15257340247874331456568165)
          ·
            refine ⟨2860751296476437148106531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15257340247874331456568165 2860751296476437148106531)
            ·
              refine ⟨4291126944714655722159797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2860751296476437148106531 4291126944714655722159797)
              ·
                refine ⟨402293151066998973952481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4291126944714655722159797 402293151066998973952481)
                ·
                  refine ⟨301719863300249230464361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402293151066998973952481 301719863300249230464361)
                  ·
                    rfl

theorem cell20_661047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 2].length) (baseStart_661047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661047 prefixEnd_661047 := by exact prefixLift 661047
  have htrace : WordTrace (prefixWord ++ tailWord_661047) baseStart_661047 baseEnd_661047 := by
    simpa [prefixWord, tailWord_661047, baseEnd_661047] using wordTrace_append hprefix tailTrace_661047
  have hstable : (prefixWord ++ tailWord_661047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661047).length < 2 ^ (prefixWord ++ tailWord_661047).sum := by decide
  have hdescent : baseEnd_661047 < baseStart_661047 := by decide
  rcases family_descends (prefixWord ++ tailWord_661047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661068 : List Nat := [2, 2, 1, 3, 1, 3, 1, 3, 4]
def baseStart_661068 : Nat := 118140960795 + 661068 * 2 ^ 59
def prefixEnd_661068 : Nat := 4983230072969 + 3 ^ 40 * 661068 * 2
def baseEnd_661068 : Nat := 301729448272466490764275

theorem tailTrace_661068 : CollatzResearch.WordTrace tailWord_661068 prefixEnd_661068 301729448272466490764275 := by
  unfold tailWord_661068
  simp only [CollatzResearch.WordTrace]
  refine ⟨12055565384535506135483929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16074087179380674847311905 12055565384535506135483929)
  ·
    refine ⟨9041674038401629601612947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12055565384535506135483929 9041674038401629601612947)
    ·
      refine ⟨13562511057602444402419421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9041674038401629601612947 13562511057602444402419421)
      ·
        refine ⟨5085941646600916650907283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13562511057602444402419421 5085941646600916650907283)
        ·
          refine ⟨7628912469901374976360925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5085941646600916650907283 7628912469901374976360925)
          ·
            refine ⟨2860842176213015616135347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7628912469901374976360925 2860842176213015616135347)
            ·
              refine ⟨4291263264319523424203021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2860842176213015616135347 4291263264319523424203021)
              ·
                refine ⟨1609223724119821284076133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4291263264319523424203021 1609223724119821284076133)
                ·
                  refine ⟨301729448272466490764275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1609223724119821284076133 301729448272466490764275)
                  ·
                    rfl

theorem cell20_661068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_661068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661068 prefixEnd_661068 := by exact prefixLift 661068
  have htrace : WordTrace (prefixWord ++ tailWord_661068) baseStart_661068 baseEnd_661068 := by
    simpa [prefixWord, tailWord_661068, baseEnd_661068] using wordTrace_append hprefix tailTrace_661068
  have hstable : (prefixWord ++ tailWord_661068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661068).length < 2 ^ (prefixWord ++ tailWord_661068).sum := by decide
  have hdescent : baseEnd_661068 < baseStart_661068 := by decide
  rcases family_descends (prefixWord ++ tailWord_661068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661092 : List Nat := [2, 3, 1, 1, 2, 3, 4, 4]
def baseStart_661092 : Nat := 118140960795 + 661092 * 2 ^ 59
def prefixEnd_661092 : Nat := 4983230072969 + 3 ^ 40 * 661092 * 2
def baseEnd_661092 : Nat := 100580134175476357988059

theorem tailTrace_661092 : CollatzResearch.WordTrace tailWord_661092 prefixEnd_661092 100580134175476357988059 := by
  unfold tailWord_661092
  simp only [CollatzResearch.WordTrace]
  refine ⟨12056003060492032184920765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16074670747322709579894353 12056003060492032184920765)
  ·
    refine ⟨4521001147684512069345287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12056003060492032184920765 4521001147684512069345287)
    ·
      refine ⟨6781501721526768104017931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4521001147684512069345287 6781501721526768104017931)
      ·
        refine ⟨10172252582290152156026897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6781501721526768104017931 10172252582290152156026897)
        ·
          refine ⟨7629189436717614117020173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10172252582290152156026897 7629189436717614117020173)
          ·
            refine ⟨2860946038769105293882565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7629189436717614117020173 2860946038769105293882565)
            ·
              refine ⟨536427382269207242602981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2860946038769105293882565 536427382269207242602981)
              ·
                refine ⟨100580134175476357988059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 536427382269207242602981 100580134175476357988059)
                ·
                  rfl

theorem cell20_661092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 4].length) (baseStart_661092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661092 prefixEnd_661092 := by exact prefixLift 661092
  have htrace : WordTrace (prefixWord ++ tailWord_661092) baseStart_661092 baseEnd_661092 := by
    simpa [prefixWord, tailWord_661092, baseEnd_661092] using wordTrace_append hprefix tailTrace_661092
  have hstable : (prefixWord ++ tailWord_661092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661092).length < 2 ^ (prefixWord ++ tailWord_661092).sum := by decide
  have hdescent : baseEnd_661092 < baseStart_661092 := by decide
  rcases family_descends (prefixWord ++ tailWord_661092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661120 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 5]
def baseStart_661120 : Nat := 118140960795 + 661120 * 2 ^ 59
def prefixEnd_661120 : Nat := 4983230072969 + 3 ^ 40 * 661120 * 2
def baseEnd_661120 : Nat := 301753182489385421030729

theorem tailTrace_661120 : CollatzResearch.WordTrace tailWord_661120 prefixEnd_661120 301753182489385421030729 := by
  unfold tailWord_661120
  simp only [CollatzResearch.WordTrace]
  refine ⟨12056513682441312575930407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16075351576588416767907209 12056513682441312575930407)
  ·
    refine ⟨18084770523661968863895611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12056513682441312575930407 18084770523661968863895611)
    ·
      refine ⟨27127155785492953295843417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18084770523661968863895611 27127155785492953295843417)
      ·
        refine ⟨20345366839119714971882563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27127155785492953295843417 20345366839119714971882563)
        ·
          refine ⟨30518050258679572457823845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20345366839119714971882563 30518050258679572457823845)
          ·
            refine ⟨5722134423502419835841971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30518050258679572457823845 5722134423502419835841971)
            ·
              refine ⟨8583201635253629753762957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5722134423502419835841971 8583201635253629753762957)
              ·
                refine ⟨3218700613220111157661109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8583201635253629753762957 3218700613220111157661109)
                ·
                  refine ⟨301753182489385421030729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3218700613220111157661109 301753182489385421030729)
                  ·
                    rfl

theorem cell20_661120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_661120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661120 prefixEnd_661120 := by exact prefixLift 661120
  have htrace : WordTrace (prefixWord ++ tailWord_661120) baseStart_661120 baseEnd_661120 := by
    simpa [prefixWord, tailWord_661120, baseEnd_661120] using wordTrace_append hprefix tailTrace_661120
  have hstable : (prefixWord ++ tailWord_661120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661120).length < 2 ^ (prefixWord ++ tailWord_661120).sum := by decide
  have hdescent : baseEnd_661120 < baseStart_661120 := by decide
  rcases family_descends (prefixWord ++ tailWord_661120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661130 : List Nat := [3, 1, 2, 3, 2, 2, 2, 5]
def baseStart_661130 : Nat := 118140960795 + 661130 * 2 ^ 59
def prefixEnd_661130 : Nat := 4983230072969 + 3 ^ 40 * 661130 * 2
def baseEnd_661130 : Nat := 100585915587289943565785

theorem tailTrace_661130 : CollatzResearch.WordTrace tailWord_661130 prefixEnd_661130 100585915587289943565785 := by
  unfold tailWord_661130
  simp only [CollatzResearch.WordTrace]
  refine ⟨6028348023711599214931211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16075594729897597906483229 6028348023711599214931211)
  ·
    refine ⟨9042522035567398822396817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6028348023711599214931211 9042522035567398822396817)
    ·
      refine ⟨6781891526675549116797613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9042522035567398822396817 6781891526675549116797613)
      ·
        refine ⟨2543209322503330918799105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6781891526675549116797613 2543209322503330918799105)
        ·
          refine ⟨1907406991877498189099329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2543209322503330918799105 1907406991877498189099329)
          ·
            refine ⟨1430555243908123641824497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1907406991877498189099329 1430555243908123641824497)
            ·
              refine ⟨1072916432931092731368373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1430555243908123641824497 1072916432931092731368373)
              ·
                refine ⟨100585915587289943565785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1072916432931092731368373 100585915587289943565785)
                ·
                  rfl

theorem cell20_661130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 5].length) (baseStart_661130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661130 prefixEnd_661130 := by exact prefixLift 661130
  have htrace : WordTrace (prefixWord ++ tailWord_661130) baseStart_661130 baseEnd_661130 := by
    simpa [prefixWord, tailWord_661130, baseEnd_661130] using wordTrace_append hprefix tailTrace_661130
  have hstable : (prefixWord ++ tailWord_661130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661130).length < 2 ^ (prefixWord ++ tailWord_661130).sum := by decide
  have hdescent : baseEnd_661130 < baseStart_661130 := by decide
  rcases family_descends (prefixWord ++ tailWord_661130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661174 : List Nat := [5, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_661174 : Nat := 118140960795 + 661174 * 2 ^ 59
def prefixEnd_661174 : Nat := 4983230072969 + 3 ^ 40 * 661174 * 2
def baseEnd_661174 : Nat := 301777829560801233230509

theorem tailTrace_661174 : CollatzResearch.WordTrace tailWord_661174 prefixEnd_661174 301777829560801233230509 := by
  unfold tailWord_661174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1507187306667937023395411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16076664604457994916217717 1507187306667937023395411)
  ·
    refine ⟨2260780960001905535093117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1507187306667937023395411 2260780960001905535093117)
    ·
      refine ⟨847792860000714575659919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2260780960001905535093117 847792860000714575659919)
      ·
        refine ⟨1271689290001071863489879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 847792860000714575659919 1271689290001071863489879)
        ·
          refine ⟨1907533935001607795234819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1271689290001071863489879 1907533935001607795234819)
          ·
            refine ⟨2861300902502411692852229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1907533935001607795234819 2861300902502411692852229)
            ·
              refine ⟨536493919219202192409793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2861300902502411692852229 536493919219202192409793)
              ·
                refine ⟨402370439414401644307345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 536493919219202192409793 402370439414401644307345)
                ·
                  refine ⟨301777829560801233230509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402370439414401644307345 301777829560801233230509)
                  ·
                    rfl

theorem cell20_661174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_661174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661174 prefixEnd_661174 := by exact prefixLift 661174
  have htrace : WordTrace (prefixWord ++ tailWord_661174) baseStart_661174 baseEnd_661174 := by
    simpa [prefixWord, tailWord_661174, baseEnd_661174] using wordTrace_append hprefix tailTrace_661174
  have hstable : (prefixWord ++ tailWord_661174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661174).length < 2 ^ (prefixWord ++ tailWord_661174).sum := by decide
  have hdescent : baseEnd_661174 < baseStart_661174 := by decide
  rcases family_descends (prefixWord ++ tailWord_661174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661175 : List Nat := [1, 1, 3, 1, 5, 1, 1, 4, 3]
def baseStart_661175 : Nat := 118140960795 + 661175 * 2 ^ 59
def prefixEnd_661175 : Nat := 4983230072969 + 3 ^ 40 * 661175 * 2
def baseEnd_661175 : Nat := 301778285988049674197171

theorem tailTrace_661175 : CollatzResearch.WordTrace tailWord_661175 prefixEnd_661175 301778285988049674197171 := by
  unfold tailWord_661175
  simp only [CollatzResearch.WordTrace]
  refine ⟨24115033379683369545112979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16076688919788913030075319 24115033379683369545112979)
  ·
    refine ⟨36172550069525054317669469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24115033379683369545112979 36172550069525054317669469)
    ·
      refine ⟨13564706276071895369126051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36172550069525054317669469 13564706276071895369126051)
      ·
        refine ⟨20347059414107843053689077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13564706276071895369126051 20347059414107843053689077)
        ·
          refine ⟨1907536820072610286283351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20347059414107843053689077 1907536820072610286283351)
          ·
            refine ⟨2861305230108915429425027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1907536820072610286283351 2861305230108915429425027)
            ·
              refine ⟨4291957845163373144137541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2861305230108915429425027 4291957845163373144137541)
              ·
                refine ⟨804742095968132464525789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4291957845163373144137541 804742095968132464525789)
                ·
                  refine ⟨301778285988049674197171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 804742095968132464525789 301778285988049674197171)
                  ·
                    rfl

theorem cell20_661175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 3].length) (baseStart_661175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661175 prefixEnd_661175 := by exact prefixLift 661175
  have htrace : WordTrace (prefixWord ++ tailWord_661175) baseStart_661175 baseEnd_661175 := by
    simpa [prefixWord, tailWord_661175, baseEnd_661175] using wordTrace_append hprefix tailTrace_661175
  have hstable : (prefixWord ++ tailWord_661175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661175).length < 2 ^ (prefixWord ++ tailWord_661175).sum := by decide
  have hdescent : baseEnd_661175 < baseStart_661175 := by decide
  rcases family_descends (prefixWord ++ tailWord_661175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661178 : List Nat := [3, 1, 1, 1, 2, 4, 4, 2, 2]
def baseStart_661178 : Nat := 118140960795 + 661178 * 2 ^ 59
def prefixEnd_661178 : Nat := 4983230072969 + 3 ^ 40 * 661178 * 2
def baseEnd_661178 : Nat := 301779655269794997097159

theorem tailTrace_661178 : CollatzResearch.WordTrace tailWord_661178 prefixEnd_661178 301779655269794997097159 := by
  unfold tailWord_661178
  simp only [CollatzResearch.WordTrace]
  refine ⟨6028785699668125264368047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16076761865781667371648125 6028785699668125264368047)
  ·
    refine ⟨9043178549502187896552071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6028785699668125264368047 9043178549502187896552071)
    ·
      refine ⟨13564767824253281844828107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9043178549502187896552071 13564767824253281844828107)
      ·
        refine ⟨20347151736379922767242161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13564767824253281844828107 20347151736379922767242161)
        ·
          refine ⟨15260363802284942075431621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20347151736379922767242161 15260363802284942075431621)
          ·
            refine ⟨2861318212928426639143429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15260363802284942075431621 2861318212928426639143429)
            ·
              refine ⟨536497164924079994839393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2861318212928426639143429 536497164924079994839393)
              ·
                refine ⟨402372873693059996129545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 536497164924079994839393 402372873693059996129545)
                ·
                  refine ⟨301779655269794997097159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402372873693059996129545 301779655269794997097159)
                  ·
                    rfl

theorem cell20_661178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 2].length) (baseStart_661178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661178 prefixEnd_661178 := by exact prefixLift 661178
  have htrace : WordTrace (prefixWord ++ tailWord_661178) baseStart_661178 baseEnd_661178 := by
    simpa [prefixWord, tailWord_661178, baseEnd_661178] using wordTrace_append hprefix tailTrace_661178
  have hstable : (prefixWord ++ tailWord_661178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661178).length < 2 ^ (prefixWord ++ tailWord_661178).sum := by decide
  have hdescent : baseEnd_661178 < baseStart_661178 := by decide
  rcases family_descends (prefixWord ++ tailWord_661178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661258 : List Nat := [3, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_661258 : Nat := 118140960795 + 661258 * 2 ^ 59
def prefixEnd_661258 : Nat := 4983230072969 + 3 ^ 40 * 661258 * 2
def baseEnd_661258 : Nat := 301816169449670274430165

theorem tailTrace_661258 : CollatzResearch.WordTrace tailWord_661258 prefixEnd_661258 301816169449670274430165 := by
  unfold tailWord_661258
  simp only [CollatzResearch.WordTrace]
  refine ⟨6029515159595668680096107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16078707092255116480256285 6029515159595668680096107)
  ·
    refine ⟨9044272739393503020144161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6029515159595668680096107 9044272739393503020144161)
    ·
      refine ⟨6783204554545127265108121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9044272739393503020144161 6783204554545127265108121)
      ·
        refine ⟨5087403415908845448831091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6783204554545127265108121 5087403415908845448831091)
        ·
          refine ⟨7631105123863268173246637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5087403415908845448831091 7631105123863268173246637)
          ·
            refine ⟨2861664421448725564967489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7631105123863268173246637 2861664421448725564967489)
            ·
              refine ⟨2146248316086544173725617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2861664421448725564967489 2146248316086544173725617)
              ·
                refine ⟨1609686237064908130294213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2146248316086544173725617 1609686237064908130294213)
                ·
                  refine ⟨301816169449670274430165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1609686237064908130294213 301816169449670274430165)
                  ·
                    rfl

theorem cell20_661258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_661258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661258 prefixEnd_661258 := by exact prefixLift 661258
  have htrace : WordTrace (prefixWord ++ tailWord_661258) baseStart_661258 baseEnd_661258 := by
    simpa [prefixWord, tailWord_661258, baseEnd_661258] using wordTrace_append hprefix tailTrace_661258
  have hstable : (prefixWord ++ tailWord_661258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661258).length < 2 ^ (prefixWord ++ tailWord_661258).sum := by decide
  have hdescent : baseEnd_661258 < baseStart_661258 := by decide
  rcases family_descends (prefixWord ++ tailWord_661258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661272 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 5]
def baseStart_661272 : Nat := 118140960795 + 661272 * 2 ^ 59
def prefixEnd_661272 : Nat := 4983230072969 + 3 ^ 40 * 661272 * 2
def baseEnd_661272 : Nat := 301822559431148447963441

theorem tailTrace_661272 : CollatzResearch.WordTrace tailWord_661272 prefixEnd_661272 301822559431148447963441 := by
  unfold tailWord_661272
  simp only [CollatzResearch.WordTrace]
  refine ⟨12059285630165977555697035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16079047506887970074262713 12059285630165977555697035)
  ·
    refine ⟨18088928445248966333545553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12059285630165977555697035 18088928445248966333545553)
    ·
      refine ⟨13566696333936724750159165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18088928445248966333545553 13566696333936724750159165)
      ·
        refine ⟨5087511125226271781309687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13566696333936724750159165 5087511125226271781309687)
        ·
          refine ⟨7631266687839407671964531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5087511125226271781309687 7631266687839407671964531)
          ·
            refine ⟨11446900031759111507946797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7631266687839407671964531 11446900031759111507946797)
            ·
              refine ⟨4292587511909666815480049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11446900031759111507946797 4292587511909666815480049)
              ·
                refine ⟨3219440633932250111610037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4292587511909666815480049 3219440633932250111610037)
                ·
                  refine ⟨301822559431148447963441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3219440633932250111610037 301822559431148447963441)
                  ·
                    rfl

theorem cell20_661272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_661272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661272 prefixEnd_661272 := by exact prefixLift 661272
  have htrace : WordTrace (prefixWord ++ tailWord_661272) baseStart_661272 baseEnd_661272 := by
    simpa [prefixWord, tailWord_661272, baseEnd_661272] using wordTrace_append hprefix tailTrace_661272
  have hstable : (prefixWord ++ tailWord_661272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661272).length < 2 ^ (prefixWord ++ tailWord_661272).sum := by decide
  have hdescent : baseEnd_661272 < baseStart_661272 := by decide
  rcases family_descends (prefixWord ++ tailWord_661272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661278 : List Nat := [4, 3, 2, 2, 1, 2, 6]
def baseStart_661278 : Nat := 118140960795 + 661278 * 2 ^ 59
def prefixEnd_661278 : Nat := 4983230072969 + 3 ^ 40 * 661278 * 2
def baseEnd_661278 : Nat := 33536144221626565973713

theorem tailTrace_661278 : CollatzResearch.WordTrace tailWord_661278 prefixEnd_661278 33536144221626565973713 := by
  unfold tailWord_661278
  simp only [CollatzResearch.WordTrace]
  refine ⟨3014848762288777267014061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16079193398873478757408325 3014848762288777267014061)
  ·
    refine ⟨1130568285858291475130273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3014848762288777267014061 1130568285858291475130273)
    ·
      refine ⟨847926214393718606347705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1130568285858291475130273 847926214393718606347705)
      ·
        refine ⟨635944660795288954760779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 847926214393718606347705 635944660795288954760779)
        ·
          refine ⟨953916991192933432141169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635944660795288954760779 953916991192933432141169)
          ·
            refine ⟨715437743394700074105877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 953916991192933432141169 715437743394700074105877)
            ·
              refine ⟨33536144221626565973713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 715437743394700074105877 33536144221626565973713)
              ·
                rfl

theorem cell20_661278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 6].length) (baseStart_661278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661278 prefixEnd_661278 := by exact prefixLift 661278
  have htrace : WordTrace (prefixWord ++ tailWord_661278) baseStart_661278 baseEnd_661278 := by
    simpa [prefixWord, tailWord_661278, baseEnd_661278] using wordTrace_append hprefix tailTrace_661278
  have hstable : (prefixWord ++ tailWord_661278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661278).length < 2 ^ (prefixWord ++ tailWord_661278).sum := by decide
  have hdescent : baseEnd_661278 < baseStart_661278 := by decide
  rcases family_descends (prefixWord ++ tailWord_661278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661292 : List Nat := [2, 2, 1, 1, 1, 6, 3, 2, 2]
def baseStart_661292 : Nat := 118140960795 + 661292 * 2 ^ 59
def prefixEnd_661292 : Nat := 4983230072969 + 3 ^ 40 * 661292 * 2
def baseEnd_661292 : Nat := 301831687976117267296693

theorem tailTrace_661292 : CollatzResearch.WordTrace tailWord_661292 prefixEnd_661292 301831687976117267296693 := by
  unfold tailWord_661292
  simp only [CollatzResearch.WordTrace]
  refine ⟨12059650360129749263561065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16079533813506332351414753 12059650360129749263561065)
  ·
    refine ⟨9044737770097311947670799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12059650360129749263561065 9044737770097311947670799)
    ·
      refine ⟨13567106655145967921506199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9044737770097311947670799 13567106655145967921506199)
      ·
        refine ⟨20350659982718951882259299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13567106655145967921506199 20350659982718951882259299)
        ·
          refine ⟨30525989974078427823388949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20350659982718951882259299 30525989974078427823388949)
          ·
            refine ⟨1430905780034926304221357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30525989974078427823388949 1430905780034926304221357)
            ·
              refine ⟨536589667513097364083009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1430905780034926304221357 536589667513097364083009)
              ·
                refine ⟨402442250634823023062257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 536589667513097364083009 402442250634823023062257)
                ·
                  refine ⟨301831687976117267296693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402442250634823023062257 301831687976117267296693)
                  ·
                    rfl

theorem cell20_661292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_661292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661292 prefixEnd_661292 := by exact prefixLift 661292
  have htrace : WordTrace (prefixWord ++ tailWord_661292) baseStart_661292 baseEnd_661292 := by
    simpa [prefixWord, tailWord_661292, baseEnd_661292] using wordTrace_append hprefix tailTrace_661292
  have hstable : (prefixWord ++ tailWord_661292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661292).length < 2 ^ (prefixWord ++ tailWord_661292).sum := by decide
  have hdescent : baseEnd_661292 < baseStart_661292 := by decide
  rcases family_descends (prefixWord ++ tailWord_661292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661302 : List Nat := [5, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_661302 : Nat := 118140960795 + 661302 * 2 ^ 59
def prefixEnd_661302 : Nat := 4983230072969 + 3 ^ 40 * 661302 * 2
def baseEnd_661302 : Nat := 301836252248601676963319

theorem tailTrace_661302 : CollatzResearch.WordTrace tailWord_661302 prefixEnd_661302 301836252248601676963319 := by
  unfold tailWord_661302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1507479090638954389686635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16079776966815513489990773 1507479090638954389686635)
  ·
    refine ⟨2261218635958431584529953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1507479090638954389686635 2261218635958431584529953)
    ·
      refine ⟨1695913976968823688397465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2261218635958431584529953 1695913976968823688397465)
      ·
        refine ⟨1271935482726617766298099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1695913976968823688397465 1271935482726617766298099)
        ·
          refine ⟨1907903224089926649447149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1271935482726617766298099 1907903224089926649447149)
          ·
            refine ⟨715463709033722493542681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1907903224089926649447149 715463709033722493542681)
            ·
              refine ⟨536597781775291870157011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 715463709033722493542681 536597781775291870157011)
              ·
                refine ⟨804896672662937805235517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536597781775291870157011 804896672662937805235517)
                ·
                  refine ⟨301836252248601676963319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 804896672662937805235517 301836252248601676963319)
                  ·
                    rfl

theorem cell20_661302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_661302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661302 prefixEnd_661302 := by exact prefixLift 661302
  have htrace : WordTrace (prefixWord ++ tailWord_661302) baseStart_661302 baseEnd_661302 := by
    simpa [prefixWord, tailWord_661302, baseEnd_661302] using wordTrace_append hprefix tailTrace_661302
  have hstable : (prefixWord ++ tailWord_661302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661302).length < 2 ^ (prefixWord ++ tailWord_661302).sum := by decide
  have hdescent : baseEnd_661302 < baseStart_661302 := by decide
  rcases family_descends (prefixWord ++ tailWord_661302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661306 : List Nat := [3, 1, 1, 1, 5, 1, 4, 1, 3]
def baseStart_661306 : Nat := 118140960795 + 661306 * 2 ^ 59
def prefixEnd_661306 : Nat := 4983230072969 + 3 ^ 40 * 661306 * 2
def baseEnd_661306 : Nat := 301838077957595440829969

theorem tailTrace_661306 : CollatzResearch.WordTrace tailWord_661306 prefixEnd_661306 301838077957595440829969 := by
  unfold tailWord_661306
  simp only [CollatzResearch.WordTrace]
  refine ⟨6029952835552194729532943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16079874228139185945421181 6029952835552194729532943)
  ·
    refine ⟨9044929253328292094299415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6029952835552194729532943 9044929253328292094299415)
    ·
      refine ⟨13567393879992438141449123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9044929253328292094299415 13567393879992438141449123)
      ·
        refine ⟨20351090819988657212173685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13567393879992438141449123 20351090819988657212173685)
        ·
          refine ⟨1907914764373936613641283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20351090819988657212173685 1907914764373936613641283)
          ·
            refine ⟨2861872146560904920461925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1907914764373936613641283 2861872146560904920461925)
            ·
              refine ⟨536601027480169672586611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2861872146560904920461925 536601027480169672586611)
              ·
                refine ⟨804901541220254508879917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536601027480169672586611 804901541220254508879917)
                ·
                  refine ⟨301838077957595440829969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 804901541220254508879917 301838077957595440829969)
                  ·
                    rfl

theorem cell20_661306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_661306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661306 prefixEnd_661306 := by exact prefixLift 661306
  have htrace : WordTrace (prefixWord ++ tailWord_661306) baseStart_661306 baseEnd_661306 := by
    simpa [prefixWord, tailWord_661306, baseEnd_661306] using wordTrace_append hprefix tailTrace_661306
  have hstable : (prefixWord ++ tailWord_661306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661306).length < 2 ^ (prefixWord ++ tailWord_661306).sum := by decide
  have hdescent : baseEnd_661306 < baseStart_661306 := by decide
  rcases family_descends (prefixWord ++ tailWord_661306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661317 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 6]
def baseStart_661317 : Nat := 118140960795 + 661317 * 2 ^ 59
def prefixEnd_661317 : Nat := 4983230072969 + 3 ^ 40 * 661317 * 2
def baseEnd_661317 : Nat := 301843098657328291463257

theorem tailTrace_661317 : CollatzResearch.WordTrace tailWord_661317 prefixEnd_661317 301843098657328291463257 := by
  unfold tailWord_661317
  simp only [CollatzResearch.WordTrace]
  refine ⟨24120212545168927796782205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16080141696779285197854803 24120212545168927796782205)
  ·
    refine ⟨9045079704438347923793327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24120212545168927796782205 9045079704438347923793327)
    ·
      refine ⟨13567619556657521885689991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9045079704438347923793327 13567619556657521885689991)
      ·
        refine ⟨20351429334986282828534987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13567619556657521885689991 20351429334986282828534987)
        ·
          refine ⟨30527144002479424242802481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20351429334986282828534987 30527144002479424242802481)
          ·
            refine ⟨22895358001859568182101861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30527144002479424242802481 22895358001859568182101861)
            ·
              refine ⟨4292879625348669034144099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22895358001859568182101861 4292879625348669034144099)
              ·
                refine ⟨6439319438023003551216149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4292879625348669034144099 6439319438023003551216149)
                ·
                  refine ⟨301843098657328291463257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6439319438023003551216149 301843098657328291463257)
                  ·
                    rfl

theorem cell20_661317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_661317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661317 prefixEnd_661317 := by exact prefixLift 661317
  have htrace : WordTrace (prefixWord ++ tailWord_661317) baseStart_661317 baseEnd_661317 := by
    simpa [prefixWord, tailWord_661317, baseEnd_661317] using wordTrace_append hprefix tailTrace_661317
  have hstable : (prefixWord ++ tailWord_661317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661317).length < 2 ^ (prefixWord ++ tailWord_661317).sum := by decide
  have hdescent : baseEnd_661317 < baseStart_661317 := by decide
  rcases family_descends (prefixWord ++ tailWord_661317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661347 : List Nat := [1, 1, 1, 5, 4, 2, 2, 2, 2]
def baseStart_661347 : Nat := 118140960795 + 661347 * 2 ^ 59
def prefixEnd_661347 : Nat := 4983230072969 + 3 ^ 40 * 661347 * 2
def baseEnd_661347 : Nat := 301856791474781520463135

theorem tailTrace_661347 : CollatzResearch.WordTrace tailWord_661347 prefixEnd_661347 301856791474781520463135 := by
  unfold tailWord_661347
  simp only [CollatzResearch.WordTrace]
  refine ⟨24121306735060242920374295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16080871156706828613582863 24121306735060242920374295)
  ·
    refine ⟨36181960102590364380561443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24121306735060242920374295 36181960102590364380561443)
    ·
      refine ⟨54272940153885546570842165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36181960102590364380561443 54272940153885546570842165)
      ·
        refine ⟨5088088139426769991016453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54272940153885546570842165 5088088139426769991016453)
        ·
          refine ⟨954016526142519373315585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5088088139426769991016453 954016526142519373315585)
          ·
            refine ⟨715512394606889529986689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954016526142519373315585 715512394606889529986689)
            ·
              refine ⟨536634295955167147490017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 715512394606889529986689 536634295955167147490017)
              ·
                refine ⟨402475721966375360617513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 536634295955167147490017 402475721966375360617513)
                ·
                  refine ⟨301856791474781520463135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402475721966375360617513 301856791474781520463135)
                  ·
                    rfl

theorem cell20_661347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 2].length) (baseStart_661347 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661347 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661347 prefixEnd_661347 := by exact prefixLift 661347
  have htrace : WordTrace (prefixWord ++ tailWord_661347) baseStart_661347 baseEnd_661347 := by
    simpa [prefixWord, tailWord_661347, baseEnd_661347] using wordTrace_append hprefix tailTrace_661347
  have hstable : (prefixWord ++ tailWord_661347).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661347).length < 2 ^ (prefixWord ++ tailWord_661347).sum := by decide
  have hdescent : baseEnd_661347 < baseStart_661347 := by decide
  rcases family_descends (prefixWord ++ tailWord_661347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661351 : List Nat := [1, 1, 5, 1, 2, 1, 3, 4, 2]
def baseStart_661351 : Nat := 118140960795 + 661351 * 2 ^ 59
def prefixEnd_661351 : Nat := 4983230072969 + 3 ^ 40 * 661351 * 2
def baseEnd_661351 : Nat := 301858617183775284329785

theorem tailTrace_661351 : CollatzResearch.WordTrace tailWord_661351 prefixEnd_661351 301858617183775284329785 := by
  unfold tailWord_661351
  simp only [CollatzResearch.WordTrace]
  refine ⟨24121452627045751603519907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16080968418030501069013271 24121452627045751603519907)
  ·
    refine ⟨36182178940568627405279861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24121452627045751603519907 36182178940568627405279861)
    ·
      refine ⟨3392079275678308819244987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36182178940568627405279861 3392079275678308819244987)
      ·
        refine ⟨5088118913517463228867481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3392079275678308819244987 5088118913517463228867481)
        ·
          refine ⟨3816089185138097421650611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5088118913517463228867481 3816089185138097421650611)
          ·
            refine ⟨5724133777707146132475917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3816089185138097421650611 5724133777707146132475917)
            ·
              refine ⟨2146550166640179799678469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5724133777707146132475917 2146550166640179799678469)
              ·
                refine ⟨402478156245033712439713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2146550166640179799678469 402478156245033712439713)
                ·
                  refine ⟨301858617183775284329785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402478156245033712439713 301858617183775284329785)
                  ·
                    rfl

theorem cell20_661351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 2].length) (baseStart_661351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661351 prefixEnd_661351 := by exact prefixLift 661351
  have htrace : WordTrace (prefixWord ++ tailWord_661351) baseStart_661351 baseEnd_661351 := by
    simpa [prefixWord, tailWord_661351, baseEnd_661351] using wordTrace_append hprefix tailTrace_661351
  have hstable : (prefixWord ++ tailWord_661351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661351).length < 2 ^ (prefixWord ++ tailWord_661351).sum := by decide
  have hdescent : baseEnd_661351 < baseStart_661351 := by decide
  rcases family_descends (prefixWord ++ tailWord_661351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661354 : List Nat := [3, 1, 3, 4, 2, 1, 1, 5]
def baseStart_661354 : Nat := 118140960795 + 661354 * 2 ^ 59
def prefixEnd_661354 : Nat := 4983230072969 + 3 ^ 40 * 661354 * 2
def baseEnd_661354 : Nat := 100619995488506869076591

theorem tailTrace_661354 : CollatzResearch.WordTrace tailWord_661354 prefixEnd_661354 100619995488506869076591 := by
  unfold tailWord_661354
  simp only [CollatzResearch.WordTrace]
  refine ⟨6030390511508720778969779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16081041364023255410586077 6030390511508720778969779)
  ·
    refine ⟨9045585767263081168454669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6030390511508720778969779 9045585767263081168454669)
    ·
      refine ⟨3392094662723655438170501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9045585767263081168454669 3392094662723655438170501)
      ·
        refine ⟨636017749260685394656969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3392094662723655438170501 636017749260685394656969)
        ·
          refine ⟨477013311945514045992727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 636017749260685394656969 477013311945514045992727)
          ·
            refine ⟨715519967918271068989091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477013311945514045992727 715519967918271068989091)
            ·
              refine ⟨1073279951877406603483637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715519967918271068989091 1073279951877406603483637)
              ·
                refine ⟨100619995488506869076591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1073279951877406603483637 100619995488506869076591)
                ·
                  rfl

theorem cell20_661354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 5].length) (baseStart_661354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661354 prefixEnd_661354 := by exact prefixLift 661354
  have htrace : WordTrace (prefixWord ++ tailWord_661354) baseStart_661354 baseEnd_661354 := by
    simpa [prefixWord, tailWord_661354, baseEnd_661354] using wordTrace_append hprefix tailTrace_661354
  have hstable : (prefixWord ++ tailWord_661354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661354).length < 2 ^ (prefixWord ++ tailWord_661354).sum := by decide
  have hdescent : baseEnd_661354 < baseStart_661354 := by decide
  rcases family_descends (prefixWord ++ tailWord_661354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661355 : List Nat := [1, 1, 1, 1, 2, 2, 3, 5, 4]
def baseStart_661355 : Nat := 118140960795 + 661355 * 2 ^ 59
def prefixEnd_661355 : Nat := 4983230072969 + 3 ^ 40 * 661355 * 2
def baseEnd_661355 : Nat := 301860442892769048196435

theorem tailTrace_661355 : CollatzResearch.WordTrace tailWord_661355 prefixEnd_661355 301860442892769048196435 := by
  unfold tailWord_661355
  simp only [CollatzResearch.WordTrace]
  refine ⟨24121598519031260286665519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16081065679354173524443679 24121598519031260286665519)
  ·
    refine ⟨36182397778546890429998279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24121598519031260286665519 36182397778546890429998279)
    ·
      refine ⟨54273596667820335644997419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36182397778546890429998279 54273596667820335644997419)
      ·
        refine ⟨81410395001730503467496129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54273596667820335644997419 81410395001730503467496129)
        ·
          refine ⟨61057796251297877600622097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81410395001730503467496129 61057796251297877600622097)
          ·
            refine ⟨45793347188473408200466573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61057796251297877600622097 45793347188473408200466573)
            ·
              refine ⟨17172505195677528075174965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45793347188473408200466573 17172505195677528075174965)
              ·
                refine ⟨1609922362094768257047653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17172505195677528075174965 1609922362094768257047653)
                ·
                  refine ⟨301860442892769048196435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1609922362094768257047653 301860442892769048196435)
                  ·
                    rfl

theorem cell20_661355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 4].length) (baseStart_661355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661355 prefixEnd_661355 := by exact prefixLift 661355
  have htrace : WordTrace (prefixWord ++ tailWord_661355) baseStart_661355 baseEnd_661355 := by
    simpa [prefixWord, tailWord_661355, baseEnd_661355] using wordTrace_append hprefix tailTrace_661355
  have hstable : (prefixWord ++ tailWord_661355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661355).length < 2 ^ (prefixWord ++ tailWord_661355).sum := by decide
  have hdescent : baseEnd_661355 < baseStart_661355 := by decide
  rcases family_descends (prefixWord ++ tailWord_661355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661358 : List Nat := [4, 1, 2, 3, 1, 1, 3, 5]
def baseStart_661358 : Nat := 118140960795 + 661358 * 2 ^ 59
def prefixEnd_661358 : Nat := 4983230072969 + 3 ^ 40 * 661358 * 2
def baseEnd_661358 : Nat := 100620604058171457032141

theorem tailTrace_661358 : CollatzResearch.WordTrace tailWord_661358 prefixEnd_661358 100620604058171457032141 := by
  unfold tailWord_661358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3015213492252548974878091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16081138625346927866016485 3015213492252548974878091)
  ·
    refine ⟨4522820238378823462317137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3015213492252548974878091 4522820238378823462317137)
    ·
      refine ⟨3392115178784117596737853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4522820238378823462317137 3392115178784117596737853)
      ·
        refine ⟨1272043192044044098776695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3392115178784117596737853 1272043192044044098776695)
        ·
          refine ⟨1908064788066066148165043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1272043192044044098776695 1908064788066066148165043)
          ·
            refine ⟨2862097182099099222247565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1908064788066066148165043 2862097182099099222247565)
            ·
              refine ⟨1073286443287162208342837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2862097182099099222247565 1073286443287162208342837)
              ·
                refine ⟨100620604058171457032141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1073286443287162208342837 100620604058171457032141)
                ·
                  rfl

theorem cell20_661358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_661358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661358 prefixEnd_661358 := by exact prefixLift 661358
  have htrace : WordTrace (prefixWord ++ tailWord_661358) baseStart_661358 baseEnd_661358 := by
    simpa [prefixWord, tailWord_661358, baseEnd_661358] using wordTrace_append hprefix tailTrace_661358
  have hstable : (prefixWord ++ tailWord_661358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661358).length < 2 ^ (prefixWord ++ tailWord_661358).sum := by decide
  have hdescent : baseEnd_661358 < baseStart_661358 := by decide
  rcases family_descends (prefixWord ++ tailWord_661358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661365 : List Nat := [1, 3, 4, 1, 1, 1, 1, 5, 3]
def baseStart_661365 : Nat := 118140960795 + 661365 * 2 ^ 59
def prefixEnd_661365 : Nat := 4983230072969 + 3 ^ 40 * 661365 * 2
def baseEnd_661365 : Nat := 301865007165253457863061

theorem tailTrace_661365 : CollatzResearch.WordTrace tailWord_661365 prefixEnd_661365 301865007165253457863061 := by
  unfold tailWord_661365
  simp only [CollatzResearch.WordTrace]
  refine ⟨24121963248995031994529549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16081308832663354663019699 24121963248995031994529549)
  ·
    refine ⟨9045736218373136997948581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24121963248995031994529549 9045736218373136997948581)
    ·
      refine ⟨1696075540944963187115359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9045736218373136997948581 1696075540944963187115359)
      ·
        refine ⟨2544113311417444780673039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1696075540944963187115359 2544113311417444780673039)
        ·
          refine ⟨3816169967126167171009559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2544113311417444780673039 3816169967126167171009559)
          ·
            refine ⟨5724254950689250756514339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3816169967126167171009559 5724254950689250756514339)
            ·
              refine ⟨8586382426033876134771509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5724254950689250756514339 8586382426033876134771509)
              ·
                refine ⟨804973352440675887634829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8586382426033876134771509 804973352440675887634829)
                ·
                  refine ⟨301865007165253457863061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 804973352440675887634829 301865007165253457863061)
                  ·
                    rfl

theorem cell20_661365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 3].length) (baseStart_661365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661365 prefixEnd_661365 := by exact prefixLift 661365
  have htrace : WordTrace (prefixWord ++ tailWord_661365) baseStart_661365 baseEnd_661365 := by
    simpa [prefixWord, tailWord_661365, baseEnd_661365] using wordTrace_append hprefix tailTrace_661365
  have hstable : (prefixWord ++ tailWord_661365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661365).length < 2 ^ (prefixWord ++ tailWord_661365).sum := by decide
  have hdescent : baseEnd_661365 < baseStart_661365 := by decide
  rcases family_descends (prefixWord ++ tailWord_661365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661416 : List Nat := [2, 1, 6, 2, 1, 1, 3, 1, 3]
def baseStart_661416 : Nat := 118140960795 + 661416 * 2 ^ 59
def prefixEnd_661416 : Nat := 4983230072969 + 3 ^ 40 * 661416 * 2
def baseEnd_661416 : Nat := 301888284954923947162853

theorem tailTrace_661416 : CollatzResearch.WordTrace tailWord_661416 prefixEnd_661416 301888284954923947162853 := by
  unfold tailWord_661416
  simp only [CollatzResearch.WordTrace]
  refine ⟨12061911685905133852318051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16082548914540178469757401 12061911685905133852318051)
  ·
    refine ⟨18092867528857700778477077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12061911685905133852318051 18092867528857700778477077)
    ·
      refine ⟨848103165415204723991113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18092867528857700778477077 848103165415204723991113)
      ·
        refine ⟨636077374061403542993335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 848103165415204723991113 636077374061403542993335)
        ·
          refine ⟨954116061092105314490003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636077374061403542993335 954116061092105314490003)
          ·
            refine ⟨1431174091638157971735005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954116061092105314490003 1431174091638157971735005)
            ·
              refine ⟨536690284364309239400627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1431174091638157971735005 536690284364309239400627)
              ·
                refine ⟨805035426546463859100941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536690284364309239400627 805035426546463859100941)
                ·
                  refine ⟨301888284954923947162853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 805035426546463859100941 301888284954923947162853)
                  ·
                    rfl

theorem cell20_661416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 3].length) (baseStart_661416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661416 prefixEnd_661416 := by exact prefixLift 661416
  have htrace : WordTrace (prefixWord ++ tailWord_661416) baseStart_661416 baseEnd_661416 := by
    simpa [prefixWord, tailWord_661416, baseEnd_661416] using wordTrace_append hprefix tailTrace_661416
  have hstable : (prefixWord ++ tailWord_661416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661416).length < 2 ^ (prefixWord ++ tailWord_661416).sum := by decide
  have hdescent : baseEnd_661416 < baseStart_661416 := by decide
  rcases family_descends (prefixWord ++ tailWord_661416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661465 : List Nat := [1, 2, 1, 2, 6, 2, 1, 1, 4]
def baseStart_661465 : Nat := 118140960795 + 661465 * 2 ^ 59
def prefixEnd_661465 : Nat := 4983230072969 + 3 ^ 40 * 661465 * 2
def baseEnd_661465 : Nat := 301910649890097554529319

theorem tailTrace_661465 : CollatzResearch.WordTrace tailWord_661465 prefixEnd_661465 301910649890097554529319 := by
  unfold tailWord_661465
  simp only [CollatzResearch.WordTrace]
  refine ⟨24125610548632749073169849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16083740365755166048779899 24125610548632749073169849)
  ·
    refine ⟨18094207911474561804877387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24125610548632749073169849 18094207911474561804877387)
    ·
      refine ⟨27141311867211842707316081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18094207911474561804877387 27141311867211842707316081)
      ·
        refine ⟨20355983900408882030487061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27141311867211842707316081 20355983900408882030487061)
        ·
          refine ⟨954186745331666345179081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20355983900408882030487061 954186745331666345179081)
          ·
            refine ⟨715640058998749758884311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954186745331666345179081 715640058998749758884311)
            ·
              refine ⟨1073460088498124638326467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715640058998749758884311 1073460088498124638326467)
              ·
                refine ⟨1610190132747186957489701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1073460088498124638326467 1610190132747186957489701)
                ·
                  refine ⟨301910649890097554529319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1610190132747186957489701 301910649890097554529319)
                  ·
                    rfl

theorem cell20_661465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 4].length) (baseStart_661465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661465 prefixEnd_661465 := by exact prefixLift 661465
  have htrace : WordTrace (prefixWord ++ tailWord_661465) baseStart_661465 baseEnd_661465 := by
    simpa [prefixWord, tailWord_661465, baseEnd_661465] using wordTrace_append hprefix tailTrace_661465
  have hstable : (prefixWord ++ tailWord_661465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661465).length < 2 ^ (prefixWord ++ tailWord_661465).sum := by decide
  have hdescent : baseEnd_661465 < baseStart_661465 := by decide
  rcases family_descends (prefixWord ++ tailWord_661465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661468 : List Nat := [2, 2, 6, 1, 1, 1, 2, 5]
def baseStart_661468 : Nat := 118140960795 + 661468 * 2 ^ 59
def prefixEnd_661468 : Nat := 4983230072969 + 3 ^ 40 * 661468 * 2
def baseEnd_661468 : Nat := 100637339723947625809769

theorem tailTrace_661468 : CollatzResearch.WordTrace tailWord_661468 prefixEnd_661468 100637339723947625809769 := by
  unfold tailWord_661468
  simp only [CollatzResearch.WordTrace]
  refine ⟨12062859983810940292764529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16083813311747920390352705 12062859983810940292764529)
  ·
    refine ⟨9047144987858205219573397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12062859983810940292764529 9047144987858205219573397)
    ·
      refine ⟨424084921305853369667503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9047144987858205219573397 424084921305853369667503)
      ·
        refine ⟨636127381958780054501255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424084921305853369667503 636127381958780054501255)
        ·
          refine ⟨954191072938170081751883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636127381958780054501255 954191072938170081751883)
          ·
            refine ⟨1431286609407255122627825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954191072938170081751883 1431286609407255122627825)
            ·
              refine ⟨1073464957055441341970869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1431286609407255122627825 1073464957055441341970869)
              ·
                refine ⟨100637339723947625809769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1073464957055441341970869 100637339723947625809769)
                ·
                  rfl

theorem cell20_661468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 5].length) (baseStart_661468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661468 prefixEnd_661468 := by exact prefixLift 661468
  have htrace : WordTrace (prefixWord ++ tailWord_661468) baseStart_661468 baseEnd_661468 := by
    simpa [prefixWord, tailWord_661468, baseEnd_661468] using wordTrace_append hprefix tailTrace_661468
  have hstable : (prefixWord ++ tailWord_661468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661468).length < 2 ^ (prefixWord ++ tailWord_661468).sum := by decide
  have hdescent : baseEnd_661468 < baseStart_661468 := by decide
  rcases family_descends (prefixWord ++ tailWord_661468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661514 : List Nat := [3, 1, 2, 2, 12]
def baseStart_661514 : Nat := 118140960795 + 661514 * 2 ^ 59
def prefixEnd_661514 : Nat := 4983230072969 + 3 ^ 40 * 661514 * 2
def baseEnd_661514 : Nat := 3727568084262606936985

theorem tailTrace_661514 : CollatzResearch.WordTrace tailWord_661514 prefixEnd_661514 3727568084262606936985 := by
  unfold tailWord_661514
  simp only [CollatzResearch.WordTrace]
  refine ⟨6031849431363807610425899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16084931816970153627802397 6031849431363807610425899)
  ·
    refine ⟨9047774147045711415638849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6031849431363807610425899 9047774147045711415638849)
    ·
      refine ⟨6785830610284283561729137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9047774147045711415638849 6785830610284283561729137)
      ·
        refine ⟨5089372957713212671296853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6785830610284283561729137 5089372957713212671296853)
        ·
          refine ⟨3727568084262606936985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5089372957713212671296853 3727568084262606936985)
          ·
            rfl

theorem cell20_661514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 12].length) (baseStart_661514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661514 prefixEnd_661514 := by exact prefixLift 661514
  have htrace : WordTrace (prefixWord ++ tailWord_661514) baseStart_661514 baseEnd_661514 := by
    simpa [prefixWord, tailWord_661514, baseEnd_661514] using wordTrace_append hprefix tailTrace_661514
  have hstable : (prefixWord ++ tailWord_661514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661514).length < 2 ^ (prefixWord ++ tailWord_661514).sum := by decide
  have hdescent : baseEnd_661514 < baseStart_661514 := by decide
  rcases family_descends (prefixWord ++ tailWord_661514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661527 : List Nat := [1, 1, 3, 5, 3, 1, 1, 5]
def baseStart_661527 : Nat := 118140960795 + 661527 * 2 ^ 59
def prefixEnd_661527 : Nat := 4983230072969 + 3 ^ 40 * 661527 * 2
def baseEnd_661527 : Nat := 100646316126500298154133

theorem tailTrace_661527 : CollatzResearch.WordTrace tailWord_661527 prefixEnd_661527 100646316126500298154133 := by
  unfold tailWord_661527
  simp only [CollatzResearch.WordTrace]
  refine ⟨24127871874408133661926835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16085247916272089107951223 24127871874408133661926835)
  ·
    refine ⟨36191807811612200492890253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24127871874408133661926835 36191807811612200492890253)
    ·
      refine ⟨13571927929354575184833845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36191807811612200492890253 13571927929354575184833845)
      ·
        refine ⟨1272368243376991423578173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13571927929354575184833845 1272368243376991423578173)
        ·
          refine ⟨477138091266371783841815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1272368243376991423578173 477138091266371783841815)
          ·
            refine ⟨715707136899557675762723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477138091266371783841815 715707136899557675762723)
            ·
              refine ⟨1073560705349336513644085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715707136899557675762723 1073560705349336513644085)
              ·
                refine ⟨100646316126500298154133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1073560705349336513644085 100646316126500298154133)
                ·
                  rfl

theorem cell20_661527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 5].length) (baseStart_661527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661527 prefixEnd_661527 := by exact prefixLift 661527
  have htrace : WordTrace (prefixWord ++ tailWord_661527) baseStart_661527 baseEnd_661527 := by
    simpa [prefixWord, tailWord_661527, baseEnd_661527] using wordTrace_append hprefix tailTrace_661527
  have hstable : (prefixWord ++ tailWord_661527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661527).length < 2 ^ (prefixWord ++ tailWord_661527).sum := by decide
  have hdescent : baseEnd_661527 < baseStart_661527 := by decide
  rcases family_descends (prefixWord ++ tailWord_661527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661558 : List Nat := [5, 1, 2, 1, 1, 1, 4, 3, 2]
def baseStart_661558 : Nat := 118140960795 + 661558 * 2 ^ 59
def prefixEnd_661558 : Nat := 4983230072969 + 3 ^ 40 * 661558 * 2
def baseEnd_661558 : Nat := 301953097624202564428939

theorem tailTrace_661558 : CollatzResearch.WordTrace tailWord_661558 prefixEnd_661558 301953097624202564428939 := by
  unfold tailWord_661558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1508062658580989122269083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16086001691530550637536885 1508062658580989122269083)
  ·
    refine ⟨2262093987871483683403625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1508062658580989122269083 2262093987871483683403625)
    ·
      refine ⟨1696570490903612762552719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2262093987871483683403625 1696570490903612762552719)
      ·
        refine ⟨2544855736355419143829079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1696570490903612762552719 2544855736355419143829079)
        ·
          refine ⟨3817283604533128715743619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2544855736355419143829079 3817283604533128715743619)
          ·
            refine ⟨5725925406799693073615429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3817283604533128715743619 5725925406799693073615429)
            ·
              refine ⟨1073611013774942451302893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5725925406799693073615429 1073611013774942451302893)
              ·
                refine ⟨402604130165603419238585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1073611013774942451302893 402604130165603419238585)
                ·
                  refine ⟨301953097624202564428939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 402604130165603419238585 301953097624202564428939)
                  ·
                    rfl

theorem cell20_661558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_661558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661558 prefixEnd_661558 := by exact prefixLift 661558
  have htrace : WordTrace (prefixWord ++ tailWord_661558) baseStart_661558 baseEnd_661558 := by
    simpa [prefixWord, tailWord_661558, baseEnd_661558] using wordTrace_append hprefix tailTrace_661558
  have hstable : (prefixWord ++ tailWord_661558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661558).length < 2 ^ (prefixWord ++ tailWord_661558).sum := by decide
  have hdescent : baseEnd_661558 < baseStart_661558 := by decide
  rcases family_descends (prefixWord ++ tailWord_661558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661569 : List Nat := [1, 2, 5, 1, 2, 2, 7]
def baseStart_661569 : Nat := 118140960795 + 661569 * 2 ^ 59
def prefixEnd_661569 : Nat := 4983230072969 + 3 ^ 40 * 661569 * 2
def baseEnd_661569 : Nat := 33550902035992823895803

theorem tailTrace_661569 : CollatzResearch.WordTrace tailWord_661569 prefixEnd_661569 33550902035992823895803 := by
  unfold tailWord_661569
  simp only [CollatzResearch.WordTrace]
  refine ⟨24129403740255974834955761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16086269160170649889970507 24129403740255974834955761)
  ·
    refine ⟨18097052805191981126216821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24129403740255974834955761 18097052805191981126216821)
    ·
      refine ⟨1696598700486748230582827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18097052805191981126216821 1696598700486748230582827)
      ·
        refine ⟨2544898050730122345874241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1696598700486748230582827 2544898050730122345874241)
        ·
          refine ⟨1908673538047591759405681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2544898050730122345874241 1908673538047591759405681)
          ·
            refine ⟨1431505153535693819554261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1908673538047591759405681 1431505153535693819554261)
            ·
              refine ⟨33550902035992823895803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1431505153535693819554261 33550902035992823895803)
              ·
                rfl

theorem cell20_661569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 7].length) (baseStart_661569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661569 prefixEnd_661569 := by exact prefixLift 661569
  have htrace : WordTrace (prefixWord ++ tailWord_661569) baseStart_661569 baseEnd_661569 := by
    simpa [prefixWord, tailWord_661569, baseEnd_661569] using wordTrace_append hprefix tailTrace_661569
  have hstable : (prefixWord ++ tailWord_661569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661569).length < 2 ^ (prefixWord ++ tailWord_661569).sum := by decide
  have hdescent : baseEnd_661569 < baseStart_661569 := by decide
  rcases family_descends (prefixWord ++ tailWord_661569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661576 : List Nat := [2, 1, 3, 1, 1, 1, 2, 6, 3]
def baseStart_661576 : Nat := 118140960795 + 661576 * 2 ^ 59
def prefixEnd_661576 : Nat := 4983230072969 + 3 ^ 40 * 661576 * 2
def baseEnd_661576 : Nat := 301961313314674501828865

theorem tailTrace_661576 : CollatzResearch.WordTrace tailWord_661576 prefixEnd_661576 301961313314674501828865 := by
  unfold tailWord_661576
  simp only [CollatzResearch.WordTrace]
  refine ⟨12064829525615307515230291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16086439367487076686973721 12064829525615307515230291)
  ·
    refine ⟨18097244288422961272845437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12064829525615307515230291 18097244288422961272845437)
    ·
      refine ⟨6786466608158610477317039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18097244288422961272845437 6786466608158610477317039)
      ·
        refine ⟨10179699912237915715975559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6786466608158610477317039 10179699912237915715975559)
        ·
          refine ⟨15269549868356873573963339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10179699912237915715975559 15269549868356873573963339)
          ·
            refine ⟨22904324802535310360945009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15269549868356873573963339 22904324802535310360945009)
            ·
              refine ⟨17178243601901482770708757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22904324802535310360945009 17178243601901482770708757)
              ·
                refine ⟨805230168839132004876973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17178243601901482770708757 805230168839132004876973)
                ·
                  refine ⟨301961313314674501828865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 805230168839132004876973 301961313314674501828865)
                  ·
                    rfl

theorem cell20_661576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_661576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661576 prefixEnd_661576 := by exact prefixLift 661576
  have htrace : WordTrace (prefixWord ++ tailWord_661576) baseStart_661576 baseEnd_661576 := by
    simpa [prefixWord, tailWord_661576, baseEnd_661576] using wordTrace_append hprefix tailTrace_661576
  have hstable : (prefixWord ++ tailWord_661576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661576).length < 2 ^ (prefixWord ++ tailWord_661576).sum := by decide
  have hdescent : baseEnd_661576 < baseStart_661576 := by decide
  rcases family_descends (prefixWord ++ tailWord_661576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661593 : List Nat := [1, 2, 1, 2, 2, 1, 7, 1, 3]
def baseStart_661593 : Nat := 118140960795 + 661593 * 2 ^ 59
def prefixEnd_661593 : Nat := 4983230072969 + 3 ^ 40 * 661593 * 2
def baseEnd_661593 : Nat := 301969072577897998262129

theorem tailTrace_661593 : CollatzResearch.WordTrace tailWord_661593 prefixEnd_661593 301969072577897998262129 := by
  unfold tailWord_661593
  simp only [CollatzResearch.WordTrace]
  refine ⟨24130279092169026933829433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16086852728112684622552955 24130279092169026933829433)
  ·
    refine ⟨18097709319126770200372075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24130279092169026933829433 18097709319126770200372075)
    ·
      refine ⟨27146563978690155300558113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18097709319126770200372075 27146563978690155300558113)
      ·
        refine ⟨20359922984017616475418585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27146563978690155300558113 20359922984017616475418585)
        ·
          refine ⟨15269942238013212356563939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20359922984017616475418585 15269942238013212356563939)
          ·
            refine ⟨22904913357019818534845909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15269942238013212356563939 22904913357019818534845909)
            ·
              refine ⟨536833906805151996910451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 22904913357019818534845909 536833906805151996910451)
              ·
                refine ⟨805250860207727995365677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536833906805151996910451 805250860207727995365677)
                ·
                  refine ⟨301969072577897998262129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 805250860207727995365677 301969072577897998262129)
                  ·
                    rfl

theorem cell20_661593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 3].length) (baseStart_661593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661593 prefixEnd_661593 := by exact prefixLift 661593
  have htrace : WordTrace (prefixWord ++ tailWord_661593) baseStart_661593 baseEnd_661593 := by
    simpa [prefixWord, tailWord_661593, baseEnd_661593] using wordTrace_append hprefix tailTrace_661593
  have hstable : (prefixWord ++ tailWord_661593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661593).length < 2 ^ (prefixWord ++ tailWord_661593).sum := by decide
  have hdescent : baseEnd_661593 < baseStart_661593 := by decide
  rcases family_descends (prefixWord ++ tailWord_661593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661614 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_661614 : Nat := 118140960795 + 661614 * 2 ^ 59
def prefixEnd_661614 : Nat := 4983230072969 + 3 ^ 40 * 661614 * 2
def baseEnd_661614 : Nat := 301978657550115258562043

theorem tailTrace_661614 : CollatzResearch.WordTrace tailWord_661614 prefixEnd_661614 301978657550115258562043 := by
  unfold tailWord_661614
  simp only [CollatzResearch.WordTrace]
  refine ⟨3016380628136618440042987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16087363350061965013562597 3016380628136618440042987)
  ·
    refine ⟨4524570942204927660064481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3016380628136618440042987 4524570942204927660064481)
    ·
      refine ⟨3393428206653695745048361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4524570942204927660064481 3393428206653695745048361)
      ·
        refine ⟨2545071154990271808786271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3393428206653695745048361 2545071154990271808786271)
        ·
          refine ⟨3817606732485407713179407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2545071154990271808786271 3817606732485407713179407)
          ·
            refine ⟨5726410098728111569769111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3817606732485407713179407 5726410098728111569769111)
            ·
              refine ⟨8589615148092167354653667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5726410098728111569769111 8589615148092167354653667)
              ·
                refine ⟨12884422722138251031980501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8589615148092167354653667 12884422722138251031980501)
                ·
                  refine ⟨301978657550115258562043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12884422722138251031980501 301978657550115258562043)
                  ·
                    rfl

theorem cell20_661614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_661614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661614 prefixEnd_661614 := by exact prefixLift 661614
  have htrace : WordTrace (prefixWord ++ tailWord_661614) baseStart_661614 baseEnd_661614 := by
    simpa [prefixWord, tailWord_661614, baseEnd_661614] using wordTrace_append hprefix tailTrace_661614
  have hstable : (prefixWord ++ tailWord_661614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661614).length < 2 ^ (prefixWord ++ tailWord_661614).sum := by decide
  have hdescent : baseEnd_661614 < baseStart_661614 := by decide
  rcases family_descends (prefixWord ++ tailWord_661614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661628 : List Nat := [2, 2, 2, 1, 1, 4, 8]
def baseStart_661628 : Nat := 118140960795 + 661628 * 2 ^ 59
def prefixEnd_661628 : Nat := 4983230072969 + 3 ^ 40 * 661628 * 2
def baseEnd_661628 : Nat := 33553894170177048010591

theorem tailTrace_661628 : CollatzResearch.WordTrace tailWord_661628 prefixEnd_661628 33553894170177048010591 := by
  unfold tailWord_661628
  simp only [CollatzResearch.WordTrace]
  refine ⟨12065777823521113955676769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16087703764694818607569025 12065777823521113955676769)
  ·
    refine ⟨9049333367640835466757577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12065777823521113955676769 9049333367640835466757577)
    ·
      refine ⟨6787000025730626600068183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9049333367640835466757577 6787000025730626600068183)
      ·
        refine ⟨10180500038595939900102275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6787000025730626600068183 10180500038595939900102275)
        ·
          refine ⟨15270750057893909850153413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10180500038595939900102275 15270750057893909850153413)
          ·
            refine ⟨2863265635855108096903765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15270750057893909850153413 2863265635855108096903765)
            ·
              refine ⟨33553894170177048010591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2863265635855108096903765 33553894170177048010591)
              ·
                rfl

theorem cell20_661628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 8].length) (baseStart_661628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_661628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_661628 prefixEnd_661628 := by exact prefixLift 661628
  have htrace : WordTrace (prefixWord ++ tailWord_661628) baseStart_661628 baseEnd_661628 := by
    simpa [prefixWord, tailWord_661628, baseEnd_661628] using wordTrace_append hprefix tailTrace_661628
  have hstable : (prefixWord ++ tailWord_661628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661628).length < 2 ^ (prefixWord ++ tailWord_661628).sum := by decide
  have hdescent : baseEnd_661628 < baseStart_661628 := by decide
  rcases family_descends (prefixWord ++ tailWord_661628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
