import V185TrunkScan23Chunk1047

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6204745 : List Nat := [1, 2, 1, 1, 2, 3, 2, 4, 3, 4]
def baseStart_6204745 : Nat := 118140960795 + 6204745 * 2 ^ 59
def prefixEnd_6204745 : Nat := 4983230072969 + 3 ^ 40 * 6204745 * 2
def baseEnd_6204745 : Nat := 1062005507860477213450801

theorem tailTrace_6204745 : CollatzResearch.WordTrace tailWord_6204745 prefixEnd_6204745 1062005507860477213450801 := by
  unfold tailWord_6204745
  simp only [CollatzResearch.WordTrace]
  refine ⟨226305641906276025925191689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150870427937517350616794459 226305641906276025925191689)
  ·
    refine ⟨169729231429707019443893767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226305641906276025925191689 169729231429707019443893767)
    ·
      refine ⟨254593847144560529165840651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169729231429707019443893767 254593847144560529165840651)
      ·
        refine ⟨381890770716840793748760977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254593847144560529165840651 381890770716840793748760977)
        ·
          refine ⟨286418078037630595311570733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381890770716840793748760977 286418078037630595311570733)
          ·
            refine ⟨107406779264111473241839025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286418078037630595311570733 107406779264111473241839025)
            ·
              refine ⟨80555084448083604931379269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107406779264111473241839025 80555084448083604931379269)
              ·
                refine ⟨15104078334015675924633613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80555084448083604931379269 15104078334015675924633613)
                ·
                  refine ⟨5664029375255878471737605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15104078334015675924633613 5664029375255878471737605)
                  ·
                    refine ⟨1062005507860477213450801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5664029375255878471737605 1062005507860477213450801)
                    ·
                      rfl

theorem cell23_6204745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 4].length) (baseStart_6204745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204745 prefixEnd_6204745 := by exact prefixLift 6204745
  have htrace : WordTrace (prefixWord ++ tailWord_6204745) baseStart_6204745 baseEnd_6204745 := by
    simpa [prefixWord, tailWord_6204745, baseEnd_6204745] using wordTrace_append hprefix tailTrace_6204745
  have hstable : (prefixWord ++ tailWord_6204745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204745).length < 2 ^ (prefixWord ++ tailWord_6204745).sum := by decide
  have hdescent : baseEnd_6204745 < baseStart_6204745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204772 : List Nat := [2, 3, 1, 1, 3, 2, 2, 2, 2, 2, 3]
def baseStart_6204772 : Nat := 118140960795 + 6204772 * 2 ^ 59
def prefixEnd_6204772 : Nat := 4983230072969 + 3 ^ 40 * 6204772 * 2
def baseEnd_6204772 : Nat := 3186030387559103034714779

theorem tailTrace_6204772 : CollatzResearch.WordTrace tailWord_6204772 prefixEnd_6204772 3186030387559103034714779 := by
  unfold tailWord_6204772
  simp only [CollatzResearch.WordTrace]
  refine ⟨113153313338589104768212285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150871084451452139690949713 113153313338589104768212285)
  ·
    refine ⟨42432492501970914288079607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113153313338589104768212285 42432492501970914288079607)
    ·
      refine ⟨63648738752956371432119411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42432492501970914288079607 63648738752956371432119411)
      ·
        refine ⟨95473108129434557148179117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63648738752956371432119411 95473108129434557148179117)
        ·
          refine ⟨35802415548537958930567169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95473108129434557148179117 35802415548537958930567169)
          ·
            refine ⟨26851811661403469197925377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35802415548537958930567169 26851811661403469197925377)
            ·
              refine ⟨20138858746052601898444033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26851811661403469197925377 20138858746052601898444033)
              ·
                refine ⟨15104144059539451423833025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20138858746052601898444033 15104144059539451423833025)
                ·
                  refine ⟨11328108044654588567874769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15104144059539451423833025 11328108044654588567874769)
                  ·
                    refine ⟨8496081033490941425906077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11328108044654588567874769 8496081033490941425906077)
                    ·
                      refine ⟨3186030387559103034714779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8496081033490941425906077 3186030387559103034714779)
                      ·
                        rfl

theorem cell23_6204772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_6204772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204772 prefixEnd_6204772 := by exact prefixLift 6204772
  have htrace : WordTrace (prefixWord ++ tailWord_6204772) baseStart_6204772 baseEnd_6204772 := by
    simpa [prefixWord, tailWord_6204772, baseEnd_6204772] using wordTrace_append hprefix tailTrace_6204772
  have hstable : (prefixWord ++ tailWord_6204772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204772).length < 2 ^ (prefixWord ++ tailWord_6204772).sum := by decide
  have hdescent : baseEnd_6204772 < baseStart_6204772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204805 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 3, 5]
def baseStart_6204805 : Nat := 118140960795 + 6204805 * 2 ^ 59
def prefixEnd_6204805 : Nat := 4983230072969 + 3 ^ 40 * 6204805 * 2
def baseEnd_6204805 : Nat := 1062015777473567135200709

theorem tailTrace_6204805 : CollatzResearch.WordTrace tailWord_6204805 prefixEnd_6204805 1062015777473567135200709 := by
  unfold tailWord_6204805
  simp only [CollatzResearch.WordTrace]
  refine ⟨226307830286058656172375869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150871886857372437448250579 226307830286058656172375869)
  ·
    refine ⟨84865436357271996064640951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226307830286058656172375869 84865436357271996064640951)
    ·
      refine ⟨127298154535907994096961427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84865436357271996064640951 127298154535907994096961427)
      ·
        refine ⟨190947231803861991145442141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127298154535907994096961427 190947231803861991145442141)
        ·
          refine ⟨71605211926448246679540803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190947231803861991145442141 71605211926448246679540803)
          ·
            refine ⟨107407817889672370019311205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71605211926448246679540803 107407817889672370019311205)
            ·
              refine ⟨20138965854313569378620851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107407817889672370019311205 20138965854313569378620851)
              ·
                refine ⟨30208448781470354067931277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20138965854313569378620851 30208448781470354067931277)
                ·
                  refine ⟨11328168293051382775474229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30208448781470354067931277 11328168293051382775474229)
                  ·
                    refine ⟨1062015777473567135200709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11328168293051382775474229 1062015777473567135200709)
                    ·
                      rfl

theorem cell23_6204805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_6204805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204805 prefixEnd_6204805 := by exact prefixLift 6204805
  have htrace : WordTrace (prefixWord ++ tailWord_6204805) baseStart_6204805 baseEnd_6204805 := by
    simpa [prefixWord, tailWord_6204805, baseEnd_6204805] using wordTrace_append hprefix tailTrace_6204805
  have hstable : (prefixWord ++ tailWord_6204805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204805).length < 2 ^ (prefixWord ++ tailWord_6204805).sum := by decide
  have hdescent : baseEnd_6204805 < baseStart_6204805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204812 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 1, 5, 2]
def baseStart_6204812 : Nat := 118140960795 + 6204812 * 2 ^ 59
def prefixEnd_6204812 : Nat := 4983230072969 + 3 ^ 40 * 6204812 * 2
def baseEnd_6204812 : Nat := 3186050926785282878214595

theorem tailTrace_6204812 : CollatzResearch.WordTrace tailWord_6204812 prefixEnd_6204812 3186050926785282878214595 := by
  unfold tailWord_6204812
  simp only [CollatzResearch.WordTrace]
  refine ⟨113154042798516648183940345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150872057064688864245253793 113154042798516648183940345)
  ·
    refine ⟨84865532098887486137955259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113154042798516648183940345 84865532098887486137955259)
    ·
      refine ⟨127298298148331229206932889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84865532098887486137955259 127298298148331229206932889)
      ·
        refine ⟨95473723611248421905199667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127298298148331229206932889 95473723611248421905199667)
        ·
          refine ⟨143210585416872632857799501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95473723611248421905199667 143210585416872632857799501)
          ·
            refine ⟨53703969531327237321674813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143210585416872632857799501 53703969531327237321674813)
            ·
              refine ⟨20138988574247713995628055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53703969531327237321674813 20138988574247713995628055)
              ·
                refine ⟨30208482861371570993442083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20138988574247713995628055 30208482861371570993442083)
                ·
                  refine ⟨45312724292057356490163125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30208482861371570993442083 45312724292057356490163125)
                  ·
                    refine ⟨4248067902380377170952793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45312724292057356490163125 4248067902380377170952793)
                    ·
                      refine ⟨3186050926785282878214595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4248067902380377170952793 3186050926785282878214595)
                      ·
                        rfl

theorem cell23_6204812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_6204812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204812 prefixEnd_6204812 := by exact prefixLift 6204812
  have htrace : WordTrace (prefixWord ++ tailWord_6204812) baseStart_6204812 baseEnd_6204812 := by
    simpa [prefixWord, tailWord_6204812, baseEnd_6204812] using wordTrace_append hprefix tailTrace_6204812
  have hstable : (prefixWord ++ tailWord_6204812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204812).length < 2 ^ (prefixWord ++ tailWord_6204812).sum := by decide
  have hdescent : baseEnd_6204812 < baseStart_6204812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204855 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 6]
def baseStart_6204855 : Nat := 118140960795 + 6204855 * 2 ^ 59
def prefixEnd_6204855 : Nat := 4983230072969 + 3 ^ 40 * 6204855 * 2
def baseEnd_6204855 : Nat := 3186073006453426209976897

theorem tailTrace_6204855 : CollatzResearch.WordTrace tailWord_6204855 prefixEnd_6204855 3186073006453426209976897 := by
  unfold tailWord_6204855
  simp only [CollatzResearch.WordTrace]
  refine ⟨226309653935877514711696019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150873102623918343141130679 226309653935877514711696019)
  ·
    refine ⟨339464480903816272067544029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226309653935877514711696019 339464480903816272067544029)
    ·
      refine ⟨127299180338931102025329011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339464480903816272067544029 127299180338931102025329011)
      ·
        refine ⟨190948770508396653037993517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127299180338931102025329011 190948770508396653037993517)
        ·
          refine ⟨71605788940648744889247569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190948770508396653037993517 71605788940648744889247569)
          ·
            refine ⟨53704341705486558666935677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71605788940648744889247569 53704341705486558666935677)
            ·
              refine ⟨20139128139557459500100879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53704341705486558666935677 20139128139557459500100879)
              ·
                refine ⟨30208692209336189250151319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20139128139557459500100879 30208692209336189250151319)
                ·
                  refine ⟨45313038314004283875226979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30208692209336189250151319 45313038314004283875226979)
                  ·
                    refine ⟨67969557471006425812840469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45313038314004283875226979 67969557471006425812840469)
                    ·
                      refine ⟨3186073006453426209976897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67969557471006425812840469 3186073006453426209976897)
                      ·
                        rfl

theorem cell23_6204855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_6204855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204855 prefixEnd_6204855 := by exact prefixLift 6204855
  have htrace : WordTrace (prefixWord ++ tailWord_6204855) baseStart_6204855 baseEnd_6204855 := by
    simpa [prefixWord, tailWord_6204855, baseEnd_6204855] using wordTrace_append hprefix tailTrace_6204855
  have hstable : (prefixWord ++ tailWord_6204855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204855).length < 2 ^ (prefixWord ++ tailWord_6204855).sum := by decide
  have hdescent : baseEnd_6204855 < baseStart_6204855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204893 : List Nat := [1, 4, 3, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_6204893 : Nat := 118140960795 + 6204893 * 2 ^ 59
def prefixEnd_6204893 : Nat := 4983230072969 + 3 ^ 40 * 6204893 * 2
def baseEnd_6204893 : Nat := 3186092518718297061301723

theorem tailTrace_6204893 : CollatzResearch.WordTrace tailWord_6204893 prefixEnd_6204893 3186092518718297061301723 := by
  unfold tailWord_6204893
  simp only [CollatzResearch.WordTrace]
  refine ⟨226311039909739847201579333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150874026606493231467719555 226311039909739847201579333)
  ·
    refine ⟨42433319983076221350296125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226311039909739847201579333 42433319983076221350296125)
    ·
      refine ⟨15912494993653583006361047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42433319983076221350296125 15912494993653583006361047)
      ·
        refine ⟨23868742490480374509541571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15912494993653583006361047 23868742490480374509541571)
        ·
          refine ⟨35803113735720561764312357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23868742490480374509541571 35803113735720561764312357)
          ·
            refine ⟨6713083825447605330808567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35803113735720561764312357 6713083825447605330808567)
            ·
              refine ⟨10069625738171407996212851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6713083825447605330808567 10069625738171407996212851)
              ·
                refine ⟨15104438607257111994319277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10069625738171407996212851 15104438607257111994319277)
                ·
                  refine ⟨5664164477721416997869729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15104438607257111994319277 5664164477721416997869729)
                  ·
                    refine ⟨4248123358291062748402297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5664164477721416997869729 4248123358291062748402297)
                    ·
                      refine ⟨3186092518718297061301723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4248123358291062748402297 3186092518718297061301723)
                      ·
                        rfl

theorem cell23_6204893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_6204893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204893 prefixEnd_6204893 := by exact prefixLift 6204893
  have htrace : WordTrace (prefixWord ++ tailWord_6204893) baseStart_6204893 baseEnd_6204893 := by
    simpa [prefixWord, tailWord_6204893, baseEnd_6204893] using wordTrace_append hprefix tailTrace_6204893
  have hstable : (prefixWord ++ tailWord_6204893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204893).length < 2 ^ (prefixWord ++ tailWord_6204893).sum := by decide
  have hdescent : baseEnd_6204893 < baseStart_6204893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204895 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 2, 7]
def baseStart_6204895 : Nat := 118140960795 + 6204895 * 2 ^ 59
def prefixEnd_6204895 : Nat := 4983230072969 + 3 ^ 40 * 6204895 * 2
def baseEnd_6204895 : Nat := 1062031181893202017825571

theorem tailTrace_6204895 : CollatzResearch.WordTrace tailWord_6204895 prefixEnd_6204895 1062031181893202017825571 := by
  unfold tailWord_6204895
  simp only [CollatzResearch.WordTrace]
  refine ⟨226311112855732601543152139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150874075237155067695434759 226311112855732601543152139)
  ·
    refine ⟨339466669283598902314728209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226311112855732601543152139 339466669283598902314728209)
    ·
      refine ⟨254600001962699176736046157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339466669283598902314728209 254600001962699176736046157)
      ·
        refine ⟨95475000736012191276017309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254600001962699176736046157 95475000736012191276017309)
        ·
          refine ⟨35803125276004571728506491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95475000736012191276017309 35803125276004571728506491)
          ·
            refine ⟨53704687914006857592759737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35803125276004571728506491 53704687914006857592759737)
            ·
              refine ⟨40278515935505143194569803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53704687914006857592759737 40278515935505143194569803)
              ·
                refine ⟨60417773903257714791854705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40278515935505143194569803 60417773903257714791854705)
                ·
                  refine ⟨45313330427443286093891029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60417773903257714791854705 45313330427443286093891029)
                  ·
                    refine ⟨1062031181893202017825571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45313330427443286093891029 1062031181893202017825571)
                    ·
                      rfl

theorem cell23_6204895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 7].length) (baseStart_6204895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204895 prefixEnd_6204895 := by exact prefixLift 6204895
  have htrace : WordTrace (prefixWord ++ tailWord_6204895) baseStart_6204895 baseEnd_6204895 := by
    simpa [prefixWord, tailWord_6204895, baseEnd_6204895] using wordTrace_append hprefix tailTrace_6204895
  have hstable : (prefixWord ++ tailWord_6204895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204895).length < 2 ^ (prefixWord ++ tailWord_6204895).sum := by decide
  have hdescent : baseEnd_6204895 < baseStart_6204895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204915 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 4]
def baseStart_6204915 : Nat := 118140960795 + 6204915 * 2 ^ 59
def prefixEnd_6204915 : Nat := 4983230072969 + 3 ^ 40 * 6204915 * 2
def baseEnd_6204915 : Nat := 3186103815292695975226621

theorem tailTrace_6204915 : CollatzResearch.WordTrace tailWord_6204915 prefixEnd_6204915 3186103815292695975226621 := by
  unfold tailWord_6204915
  simp only [CollatzResearch.WordTrace]
  refine ⟨226311842315660144958880199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150874561543773429972586799 226311842315660144958880199)
  ·
    refine ⟨339467763473490217438320299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226311842315660144958880199 339467763473490217438320299)
    ·
      refine ⟨509201645210235326157480449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339467763473490217438320299 509201645210235326157480449)
      ·
        refine ⟨381901233907676494618110337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 509201645210235326157480449 381901233907676494618110337)
        ·
          refine ⟨286425925430757370963582753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381901233907676494618110337 286425925430757370963582753)
          ·
            refine ⟨214819444073068028222687065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286425925430757370963582753 214819444073068028222687065)
            ·
              refine ⟨161114583054801021167015299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214819444073068028222687065 161114583054801021167015299)
              ·
                refine ⟨241671874582201531750522949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161114583054801021167015299 241671874582201531750522949)
                ·
                  refine ⟨45313476484162787203223053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 241671874582201531750522949 45313476484162787203223053)
                  ·
                    refine ⟨16992553681561045201208645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45313476484162787203223053 16992553681561045201208645)
                    ·
                      refine ⟨3186103815292695975226621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16992553681561045201208645 3186103815292695975226621)
                      ·
                        rfl

theorem cell23_6204915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 4].length) (baseStart_6204915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204915 prefixEnd_6204915 := by exact prefixLift 6204915
  have htrace : WordTrace (prefixWord ++ tailWord_6204915) baseStart_6204915 baseEnd_6204915 := by
    simpa [prefixWord, tailWord_6204915, baseEnd_6204915] using wordTrace_append hprefix tailTrace_6204915
  have hstable : (prefixWord ++ tailWord_6204915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204915).length < 2 ^ (prefixWord ++ tailWord_6204915).sum := by decide
  have hdescent : baseEnd_6204915 < baseStart_6204915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204919 : List Nat := [1, 1, 3, 1, 1, 1, 1, 8, 1, 3, 2]
def baseStart_6204919 : Nat := 118140960795 + 6204919 * 2 ^ 59
def prefixEnd_6204919 : Nat := 4983230072969 + 3 ^ 40 * 6204919 * 2
def baseEnd_6204919 : Nat := 3186105869215313959576603

theorem tailTrace_6204919 : CollatzResearch.WordTrace tailWord_6204919 prefixEnd_6204919 3186105869215313959576603 := by
  unfold tailWord_6204919
  simp only [CollatzResearch.WordTrace]
  refine ⟨226311988207645653642025811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150874658805097102428017207 226311988207645653642025811)
  ·
    refine ⟨339467982311468480463038717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226311988207645653642025811 339467982311468480463038717)
    ·
      refine ⟨127300493366800680173639519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339467982311468480463038717 127300493366800680173639519)
      ·
        refine ⟨190950740050201020260459279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127300493366800680173639519 190950740050201020260459279)
        ·
          refine ⟨286426110075301530390688919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190950740050201020260459279 286426110075301530390688919)
          ·
            refine ⟨429639165112952295586033379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286426110075301530390688919 429639165112952295586033379)
            ·
              refine ⟨644458747669428443379050069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429639165112952295586033379 644458747669428443379050069)
              ·
                refine ⟨7552250949251114570848243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 644458747669428443379050069 7552250949251114570848243)
                ·
                  refine ⟨11328376423876671856272365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7552250949251114570848243 11328376423876671856272365)
                  ·
                    refine ⟨4248141158953751946102137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11328376423876671856272365 4248141158953751946102137)
                    ·
                      refine ⟨3186105869215313959576603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4248141158953751946102137 3186105869215313959576603)
                      ·
                        rfl

theorem cell23_6204919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 3, 2].length) (baseStart_6204919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204919 prefixEnd_6204919 := by exact prefixLift 6204919
  have htrace : WordTrace (prefixWord ++ tailWord_6204919) baseStart_6204919 baseEnd_6204919 := by
    simpa [prefixWord, tailWord_6204919, baseEnd_6204919] using wordTrace_append hprefix tailTrace_6204919
  have hstable : (prefixWord ++ tailWord_6204919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204919).length < 2 ^ (prefixWord ++ tailWord_6204919).sum := by decide
  have hdescent : baseEnd_6204919 < baseStart_6204919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6204962 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_6204962 : Nat := 118140960795 + 6204962 * 2 ^ 59
def prefixEnd_6204962 : Nat := 4983230072969 + 3 ^ 40 * 6204962 * 2
def baseEnd_6204962 : Nat := 3186127948883457291338905

theorem tailTrace_6204962 : CollatzResearch.WordTrace tailWord_6204962 prefixEnd_6204962 3186127948883457291338905 := by
  unfold tailWord_6204962
  simp only [CollatzResearch.WordTrace]
  refine ⟨56578389136622467996460285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150875704364326581323894093 56578389136622467996460285)
  ·
    refine ⟨21216895926233425498672607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56578389136622467996460285 21216895926233425498672607)
    ·
      refine ⟨31825343889350138248008911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21216895926233425498672607 31825343889350138248008911)
      ·
        refine ⟨47738015834025207372013367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31825343889350138248008911 47738015834025207372013367)
        ·
          refine ⟨71607023751037811058020051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47738015834025207372013367 71607023751037811058020051)
          ·
            refine ⟨107410535626556716587030077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71607023751037811058020051 107410535626556716587030077)
            ·
              refine ⟨40278950859958768720136279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107410535626556716587030077 40278950859958768720136279)
              ·
                refine ⟨60418426289938153080204419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40278950859958768720136279 60418426289938153080204419)
                ·
                  refine ⟨90627639434907229620306629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60418426289938153080204419 90627639434907229620306629)
                  ·
                    refine ⟨16992682394045105553807493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90627639434907229620306629 16992682394045105553807493)
                    ·
                      refine ⟨3186127948883457291338905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16992682394045105553807493 3186127948883457291338905)
                      ·
                        rfl

theorem cell23_6204962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_6204962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6204962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6204962 prefixEnd_6204962 := by exact prefixLift 6204962
  have htrace : WordTrace (prefixWord ++ tailWord_6204962) baseStart_6204962 baseEnd_6204962 := by
    simpa [prefixWord, tailWord_6204962, baseEnd_6204962] using wordTrace_append hprefix tailTrace_6204962
  have hstable : (prefixWord ++ tailWord_6204962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6204962).length < 2 ^ (prefixWord ++ tailWord_6204962).sum := by decide
  have hdescent : baseEnd_6204962 < baseStart_6204962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6204962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205002 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 4, 5]
def baseStart_6205002 : Nat := 118140960795 + 6205002 * 2 ^ 59
def prefixEnd_6205002 : Nat := 4983230072969 + 3 ^ 40 * 6205002 * 2
def baseEnd_6205002 : Nat := 1062049496036545711612907

theorem tailTrace_6205002 : CollatzResearch.WordTrace tailWord_6205002 prefixEnd_6205002 1062049496036545711612907 := by
  unfold tailWord_6205002
  simp only [CollatzResearch.WordTrace]
  refine ⟨56578753866586239704324315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150876676977563305878198173 56578753866586239704324315)
  ·
    refine ⟨84868130799879359556486473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56578753866586239704324315 84868130799879359556486473)
    ·
      refine ⟨63651098099909519667364855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84868130799879359556486473 63651098099909519667364855)
      ·
        refine ⟨95476647149864279501047283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63651098099909519667364855 95476647149864279501047283)
        ·
          refine ⟨143214970724796419251570925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95476647149864279501047283 143214970724796419251570925)
          ·
            refine ⟨53705614021798657219339097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143214970724796419251570925 53705614021798657219339097)
            ·
              refine ⟨40279210516348992914504323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53705614021798657219339097 40279210516348992914504323)
              ·
                refine ⟨60418815774523489371756485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40279210516348992914504323 60418815774523489371756485)
                ·
                  refine ⟨11328527957723154257204341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60418815774523489371756485 11328527957723154257204341)
                  ·
                    refine ⟨1062049496036545711612907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11328527957723154257204341 1062049496036545711612907)
                    ·
                      rfl

theorem cell23_6205002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_6205002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205002 prefixEnd_6205002 := by exact prefixLift 6205002
  have htrace : WordTrace (prefixWord ++ tailWord_6205002) baseStart_6205002 baseEnd_6205002 := by
    simpa [prefixWord, tailWord_6205002, baseEnd_6205002] using wordTrace_append hprefix tailTrace_6205002
  have hstable : (prefixWord ++ tailWord_6205002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205002).length < 2 ^ (prefixWord ++ tailWord_6205002).sum := by decide
  have hdescent : baseEnd_6205002 < baseStart_6205002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205012 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_6205012 : Nat := 118140960795 + 6205012 * 2 ^ 59
def prefixEnd_6205012 : Nat := 4983230072969 + 3 ^ 40 * 6205012 * 2
def baseEnd_6205012 : Nat := 3186153622916182095713675

theorem tailTrace_6205012 : CollatzResearch.WordTrace tailWord_6205012 prefixEnd_6205012 3186153622916182095713675 := by
  unfold tailWord_6205012
  simp only [CollatzResearch.WordTrace]
  refine ⟨113157690098154365262580645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150876920130872487016774193 113157690098154365262580645)
  ·
    refine ⟨21217066893403943486733871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113157690098154365262580645 21217066893403943486733871)
    ·
      refine ⟨31825600340105915230100807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21217066893403943486733871 31825600340105915230100807)
      ·
        refine ⟨47738400510158872845151211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31825600340105915230100807 47738400510158872845151211)
        ·
          refine ⟨71607600765238309267726817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47738400510158872845151211 71607600765238309267726817)
          ·
            refine ⟨53705700573928731950795113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71607600765238309267726817 53705700573928731950795113)
            ·
              refine ⟨40279275430446548963096335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53705700573928731950795113 40279275430446548963096335)
              ·
                refine ⟨60418913145669823444644503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40279275430446548963096335 60418913145669823444644503)
                ·
                  refine ⟨90628369718504735166966755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60418913145669823444644503 90628369718504735166966755)
                  ·
                    refine ⟨135942554577757102750450133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90628369718504735166966755 135942554577757102750450133)
                    ·
                      refine ⟨3186153622916182095713675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 135942554577757102750450133 3186153622916182095713675)
                      ·
                        rfl

theorem cell23_6205012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_6205012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205012 prefixEnd_6205012 := by exact prefixLift 6205012
  have htrace : WordTrace (prefixWord ++ tailWord_6205012) baseStart_6205012 baseEnd_6205012 := by
    simpa [prefixWord, tailWord_6205012, baseEnd_6205012] using wordTrace_append hprefix tailTrace_6205012
  have hstable : (prefixWord ++ tailWord_6205012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205012).length < 2 ^ (prefixWord ++ tailWord_6205012).sum := by decide
  have hdescent : baseEnd_6205012 < baseStart_6205012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205066 : List Nat := [3, 1, 2, 3, 2, 1, 3, 1, 3, 4]
def baseStart_6205066 : Nat := 118140960795 + 6205066 * 2 ^ 59
def prefixEnd_6205066 : Nat := 4983230072969 + 3 ^ 40 * 6205066 * 2
def baseEnd_6205066 : Nat := 1062060450290508294812809

theorem tailTrace_6205066 : CollatzResearch.WordTrace tailWord_6205066 prefixEnd_6205066 1062060450290508294812809 := by
  unfold tailWord_6205066
  simp only [CollatzResearch.WordTrace]
  refine ⟨56579337434528274436906763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150878233158742065165084701 56579337434528274436906763)
  ·
    refine ⟨84869006151792411655360145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56579337434528274436906763 84869006151792411655360145)
    ·
      refine ⟨63651754613844308741520109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84869006151792411655360145 63651754613844308741520109)
      ·
        refine ⟨23869407980191615778070041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63651754613844308741520109 23869407980191615778070041)
        ·
          refine ⟨17902055985143711833552531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23869407980191615778070041 17902055985143711833552531)
          ·
            refine ⟨26853083977715567750328797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17902055985143711833552531 26853083977715567750328797)
            ·
              refine ⟨10069906491643337906373299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26853083977715567750328797 10069906491643337906373299)
              ·
                refine ⟨15104859737465006859559949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10069906491643337906373299 15104859737465006859559949)
                ·
                  refine ⟨5664322401549377572334981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15104859737465006859559949 5664322401549377572334981)
                  ·
                    refine ⟨1062060450290508294812809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5664322401549377572334981 1062060450290508294812809)
                    ·
                      rfl

theorem cell23_6205066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_6205066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205066 prefixEnd_6205066 := by exact prefixLift 6205066
  have htrace : WordTrace (prefixWord ++ tailWord_6205066) baseStart_6205066 baseEnd_6205066 := by
    simpa [prefixWord, tailWord_6205066, baseEnd_6205066] using wordTrace_append hprefix tailTrace_6205066
  have hstable : (prefixWord ++ tailWord_6205066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205066).length < 2 ^ (prefixWord ++ tailWord_6205066).sum := by decide
  have hdescent : baseEnd_6205066 < baseStart_6205066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205079 : List Nat := [1, 1, 3, 3, 2, 3, 1, 3, 6]
def baseStart_6205079 : Nat := 118140960795 + 6205079 * 2 ^ 59
def prefixEnd_6205079 : Nat := 4983230072969 + 3 ^ 40 * 6205079 * 2
def baseEnd_6205079 : Nat := 354020891791114814841763

theorem tailTrace_6205079 : CollatzResearch.WordTrace tailWord_6205079 prefixEnd_6205079 354020891791114814841763 := by
  unfold tailWord_6205079
  simp only [CollatzResearch.WordTrace]
  refine ⟨226317823887066000967850291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150878549258044000645233527 226317823887066000967850291)
  ·
    refine ⟨339476735830599001451775437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226317823887066000967850291 339476735830599001451775437)
    ·
      refine ⟨127303775936474625544415789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339476735830599001451775437 127303775936474625544415789)
      ·
        refine ⟨47738915976177984579155921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127303775936474625544415789 47738915976177984579155921)
        ·
          refine ⟨35804186982133488434366941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47738915976177984579155921 35804186982133488434366941)
          ·
            refine ⟨13426570118300058162887603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35804186982133488434366941 13426570118300058162887603)
            ·
              refine ⟨20139855177450087244331405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13426570118300058162887603 20139855177450087244331405)
              ·
                refine ⟨7552445691543782716624277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20139855177450087244331405 7552445691543782716624277)
                ·
                  refine ⟨354020891791114814841763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7552445691543782716624277 354020891791114814841763)
                  ·
                    rfl

theorem cell23_6205079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 6].length) (baseStart_6205079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205079 prefixEnd_6205079 := by exact prefixLift 6205079
  have htrace : WordTrace (prefixWord ++ tailWord_6205079) baseStart_6205079 baseEnd_6205079 := by
    simpa [prefixWord, tailWord_6205079, baseEnd_6205079] using wordTrace_append hprefix tailTrace_6205079
  have hstable : (prefixWord ++ tailWord_6205079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205079).length < 2 ^ (prefixWord ++ tailWord_6205079).sum := by decide
  have hdescent : baseEnd_6205079 < baseStart_6205079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205152 : List Nat := [2, 1, 1, 3, 1, 2, 2, 11]
def baseStart_6205152 : Nat := 118140960795 + 6205152 * 2 ^ 59
def prefixEnd_6205152 : Nat := 4983230072969 + 3 ^ 40 * 6205152 * 2
def baseEnd_6205152 : Nat := 118008352229918946220853

theorem tailTrace_6205152 : CollatzResearch.WordTrace tailWord_6205152 prefixEnd_6205152 118008352229918946220853 := by
  unfold tailWord_6205152
  simp only [CollatzResearch.WordTrace]
  refine ⟨113160243207900767217628855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150880324277201022956838473 113160243207900767217628855)
  ·
    refine ⟨169740364811851150826443283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113160243207900767217628855 169740364811851150826443283)
    ·
      refine ⟨254610547217776726239664925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169740364811851150826443283 254610547217776726239664925)
      ·
        refine ⟨95478955206666272339874347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254610547217776726239664925 95478955206666272339874347)
        ·
          refine ⟨143218432809999408509811521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95478955206666272339874347 143218432809999408509811521)
          ·
            refine ⟨107413824607499556382358641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143218432809999408509811521 107413824607499556382358641)
            ·
              refine ⟨80560368455624667286768981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107413824607499556382358641 80560368455624667286768981)
              ·
                refine ⟨118008352229918946220853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 80560368455624667286768981 118008352229918946220853)
                ·
                  rfl

theorem cell23_6205152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 11].length) (baseStart_6205152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205152 prefixEnd_6205152 := by exact prefixLift 6205152
  have htrace : WordTrace (prefixWord ++ tailWord_6205152) baseStart_6205152 baseEnd_6205152 := by
    simpa [prefixWord, tailWord_6205152, baseEnd_6205152] using wordTrace_append hprefix tailTrace_6205152
  have hstable : (prefixWord ++ tailWord_6205152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205152).length < 2 ^ (prefixWord ++ tailWord_6205152).sum := by decide
  have hdescent : baseEnd_6205152 < baseStart_6205152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205180 : List Nat := [2, 2, 2, 1, 3, 1, 1, 6, 1, 2, 2]
def baseStart_6205180 : Nat := 118140960795 + 6205180 * 2 ^ 59
def prefixEnd_6205180 : Nat := 4983230072969 + 3 ^ 40 * 6205180 * 2
def baseEnd_6205180 : Nat := 3186239887666137438412903

theorem tailTrace_6205180 : CollatzResearch.WordTrace tailWord_6205180 prefixEnd_6205180 3186239887666137438412903 := by
  unfold tailWord_6205180
  simp only [CollatzResearch.WordTrace]
  refine ⟨113160753829850047608638497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150881005106466730144851329 113160753829850047608638497)
  ·
    refine ⟨84870565372387535706478873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113160753829850047608638497 84870565372387535706478873)
    ·
      refine ⟨63652924029290651779859155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84870565372387535706478873 63652924029290651779859155)
      ·
        refine ⟨95479386043935977669788733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63652924029290651779859155 95479386043935977669788733)
        ·
          refine ⟨35804769766475991626170775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95479386043935977669788733 35804769766475991626170775)
          ·
            refine ⟨53707154649713987439256163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35804769766475991626170775 53707154649713987439256163)
            ·
              refine ⟨80560731974570981158884245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53707154649713987439256163 80560731974570981158884245)
              ·
                refine ⟨3776284311308014741822699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80560731974570981158884245 3776284311308014741822699)
                ·
                  refine ⟨5664426466962022112734049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3776284311308014741822699 5664426466962022112734049)
                  ·
                    refine ⟨4248319850221516584550537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5664426466962022112734049 4248319850221516584550537)
                    ·
                      refine ⟨3186239887666137438412903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4248319850221516584550537 3186239887666137438412903)
                      ·
                        rfl

theorem cell23_6205180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 1, 2, 2].length) (baseStart_6205180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205180 prefixEnd_6205180 := by exact prefixLift 6205180
  have htrace : WordTrace (prefixWord ++ tailWord_6205180) baseStart_6205180 baseEnd_6205180 := by
    simpa [prefixWord, tailWord_6205180, baseEnd_6205180] using wordTrace_append hprefix tailTrace_6205180
  have hstable : (prefixWord ++ tailWord_6205180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205180).length < 2 ^ (prefixWord ++ tailWord_6205180).sum := by decide
  have hdescent : baseEnd_6205180 < baseStart_6205180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205196 : List Nat := [2, 2, 1, 2, 2, 1, 5, 1, 1, 3, 3]
def baseStart_6205196 : Nat := 118140960795 + 6205196 * 2 ^ 59
def prefixEnd_6205196 : Nat := 4983230072969 + 3 ^ 40 * 6205196 * 2
def baseEnd_6205196 : Nat := 3186248103356609375812829

theorem tailTrace_6205196 : CollatzResearch.WordTrace tailWord_6205196 prefixEnd_6205196 3186248103356609375812829 := by
  unfold tailWord_6205196
  simp only [CollatzResearch.WordTrace]
  refine ⟨113161045613821064974929721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150881394151761419966572961 113161045613821064974929721)
  ·
    refine ⟨84870784210365798731197291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113161045613821064974929721 84870784210365798731197291)
    ·
      refine ⟨127306176315548698096795937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84870784210365798731197291 127306176315548698096795937)
      ·
        refine ⟨95479632236661523572596953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127306176315548698096795937 95479632236661523572596953)
        ·
          refine ⟨71609724177496142679447715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95479632236661523572596953 71609724177496142679447715)
          ·
            refine ⟨107414586266244214019171573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71609724177496142679447715 107414586266244214019171573)
            ·
              refine ⟨10070117462460395064297335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107414586266244214019171573 10070117462460395064297335)
              ·
                refine ⟨15105176193690592596446003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10070117462460395064297335 15105176193690592596446003)
                ·
                  refine ⟨22657764290535888894669005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15105176193690592596446003 22657764290535888894669005)
                  ·
                    refine ⟨8496661608950958335500877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22657764290535888894669005 8496661608950958335500877)
                    ·
                      refine ⟨3186248103356609375812829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8496661608950958335500877 3186248103356609375812829)
                      ·
                        rfl

theorem cell23_6205196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_6205196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205196 prefixEnd_6205196 := by exact prefixLift 6205196
  have htrace : WordTrace (prefixWord ++ tailWord_6205196) baseStart_6205196 baseEnd_6205196 := by
    simpa [prefixWord, tailWord_6205196, baseEnd_6205196] using wordTrace_append hprefix tailTrace_6205196
  have hstable : (prefixWord ++ tailWord_6205196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205196).length < 2 ^ (prefixWord ++ tailWord_6205196).sum := by decide
  have hdescent : baseEnd_6205196 < baseStart_6205196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205247 : List Nat := [1, 1, 2, 2, 6, 2, 2, 1, 2, 1, 3]
def baseStart_6205247 : Nat := 118140960795 + 6205247 * 2 ^ 59
def prefixEnd_6205247 : Nat := 4983230072969 + 3 ^ 40 * 6205247 * 2
def baseEnd_6205247 : Nat := 3186274290869988676275095

theorem tailTrace_6205247 : CollatzResearch.WordTrace tailWord_6205247 prefixEnd_6205247 3186274290869988676275095 := by
  unfold tailWord_6205247
  simp only [CollatzResearch.WordTrace]
  refine ⟨226323951350457365659965995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150882634233638243773310663 226323951350457365659965995)
  ·
    refine ⟨339485927025686048489948993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226323951350457365659965995 339485927025686048489948993)
    ·
      refine ⟨254614445269264536367461745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339485927025686048489948993 254614445269264536367461745)
      ·
        refine ⟨190960833951948402275596309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254614445269264536367461745 190960833951948402275596309)
        ·
          refine ⟨8951289091497581356668577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 190960833951948402275596309 8951289091497581356668577)
          ·
            refine ⟨6713466818623186017501433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8951289091497581356668577 6713466818623186017501433)
            ·
              refine ⟨5035100113967389513126075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6713466818623186017501433 5035100113967389513126075)
              ·
                refine ⟨7552650170951084269689113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5035100113967389513126075 7552650170951084269689113)
                ·
                  refine ⟨5664487628213313202266835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7552650170951084269689113 5664487628213313202266835)
                  ·
                    refine ⟨8496731442319969803400253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5664487628213313202266835 8496731442319969803400253)
                    ·
                      refine ⟨3186274290869988676275095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8496731442319969803400253 3186274290869988676275095)
                      ·
                        rfl

theorem cell23_6205247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 2, 1, 3].length) (baseStart_6205247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205247 prefixEnd_6205247 := by exact prefixLift 6205247
  have htrace : WordTrace (prefixWord ++ tailWord_6205247) baseStart_6205247 baseEnd_6205247 := by
    simpa [prefixWord, tailWord_6205247, baseEnd_6205247] using wordTrace_append hprefix tailTrace_6205247
  have hstable : (prefixWord ++ tailWord_6205247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205247).length < 2 ^ (prefixWord ++ tailWord_6205247).sum := by decide
  have hdescent : baseEnd_6205247 < baseStart_6205247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205376 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 3]
def baseStart_6205376 : Nat := 118140960795 + 6205376 * 2 ^ 59
def prefixEnd_6205376 : Nat := 4983230072969 + 3 ^ 40 * 6205376 * 2
def baseEnd_6205376 : Nat := 3186340529874418671562001

theorem tailTrace_6205376 : CollatzResearch.WordTrace tailWord_6205376 prefixEnd_6205376 3186340529874418671562001 := by
  unfold tailWord_6205376
  simp only [CollatzResearch.WordTrace]
  refine ⟨113164328183495010345705991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150885770911326680460941321 113164328183495010345705991)
  ·
    refine ⟨169746492275242515518558987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113164328183495010345705991 169746492275242515518558987)
    ·
      refine ⟨254619738412863773277838481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169746492275242515518558987 254619738412863773277838481)
      ·
        refine ⟨190964803809647829958378861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254619738412863773277838481 190964803809647829958378861)
        ·
          refine ⟨71611801428617936234392073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 190964803809647829958378861 71611801428617936234392073)
          ·
            refine ⟨53708851071463452175794055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71611801428617936234392073 53708851071463452175794055)
            ·
              refine ⟨80563276607195178263691083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53708851071463452175794055 80563276607195178263691083)
              ·
                refine ⟨120844914910792767395536625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80563276607195178263691083 120844914910792767395536625)
                ·
                  refine ⟨90633686183094575546652469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120844914910792767395536625 90633686183094575546652469)
                  ·
                    refine ⟨8496908079665116457498669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90633686183094575546652469 8496908079665116457498669)
                    ·
                      refine ⟨3186340529874418671562001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8496908079665116457498669 3186340529874418671562001)
                      ·
                        rfl

theorem cell23_6205376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_6205376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205376 prefixEnd_6205376 := by exact prefixLift 6205376
  have htrace : WordTrace (prefixWord ++ tailWord_6205376) baseStart_6205376 baseEnd_6205376 := by
    simpa [prefixWord, tailWord_6205376, baseEnd_6205376] using wordTrace_append hprefix tailTrace_6205376
  have hstable : (prefixWord ++ tailWord_6205376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205376).length < 2 ^ (prefixWord ++ tailWord_6205376).sum := by decide
  have hdescent : baseEnd_6205376 < baseStart_6205376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205416 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_6205416 : Nat := 118140960795 + 6205416 * 2 ^ 59
def prefixEnd_6205416 : Nat := 4983230072969 + 3 ^ 40 * 6205416 * 2
def baseEnd_6205416 : Nat := 3186361069100598515061817

theorem tailTrace_6205416 : CollatzResearch.WordTrace tailWord_6205416 prefixEnd_6205416 3186361069100598515061817 := by
  unfold tailWord_6205416
  simp only [CollatzResearch.WordTrace]
  refine ⟨113165057643422553761434051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150886743524563405015245401 113165057643422553761434051)
  ·
    refine ⟨169747586465133830642151077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113165057643422553761434051 169747586465133830642151077)
    ·
      refine ⟨31827672462212593245403327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169747586465133830642151077 31827672462212593245403327)
      ·
        refine ⟨47741508693318889868104991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31827672462212593245403327 47741508693318889868104991)
        ·
          refine ⟨71612263039978334802157487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47741508693318889868104991 71612263039978334802157487)
          ·
            refine ⟨107418394559967502203236231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71612263039978334802157487 107418394559967502203236231)
            ·
              refine ⟨161127591839951253304854347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107418394559967502203236231 161127591839951253304854347)
              ·
                refine ⟨241691387759926879957281521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161127591839951253304854347 241691387759926879957281521)
                ·
                  refine ⟨181268540819945159967961141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241691387759926879957281521 181268540819945159967961141)
                  ·
                    refine ⟨16993925701869858746996357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 181268540819945159967961141 16993925701869858746996357)
                    ·
                      refine ⟨3186361069100598515061817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16993925701869858746996357 3186361069100598515061817)
                      ·
                        rfl

theorem cell23_6205416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_6205416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205416 prefixEnd_6205416 := by exact prefixLift 6205416
  have htrace : WordTrace (prefixWord ++ tailWord_6205416) baseStart_6205416 baseEnd_6205416 := by
    simpa [prefixWord, tailWord_6205416, baseEnd_6205416] using wordTrace_append hprefix tailTrace_6205416
  have hstable : (prefixWord ++ tailWord_6205416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205416).length < 2 ^ (prefixWord ++ tailWord_6205416).sum := by decide
  have hdescent : baseEnd_6205416 < baseStart_6205416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205430 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_6205430 : Nat := 118140960795 + 6205430 * 2 ^ 59
def prefixEnd_6205430 : Nat := 4983230072969 + 3 ^ 40 * 6205430 * 2
def baseEnd_6205430 : Nat := 1062122752609920486762251

theorem tailTrace_6205430 : CollatzResearch.WordTrace tailWord_6205430 prefixEnd_6205430 1062122752609920486762251 := by
  unfold tailWord_6205430
  simp only [CollatzResearch.WordTrace]
  refine ⟨14145664119299649244617359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150887083939196258609251829 14145664119299649244617359)
  ·
    refine ⟨21218496178949473866926039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14145664119299649244617359 21218496178949473866926039)
    ·
      refine ⟨31827744268424210800389059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21218496178949473866926039 31827744268424210800389059)
      ·
        refine ⟨47741616402636316200583589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31827744268424210800389059 47741616402636316200583589)
        ·
          refine ⟨8951553075494309287609423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47741616402636316200583589 8951553075494309287609423)
          ·
            refine ⟨13427329613241463931414135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8951553075494309287609423 13427329613241463931414135)
            ·
              refine ⟨20140994419862195897121203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13427329613241463931414135 20140994419862195897121203)
              ·
                refine ⟨30211491629793293845681805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20140994419862195897121203 30211491629793293845681805)
                ·
                  refine ⟨11329309361172485192130677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30211491629793293845681805 11329309361172485192130677)
                  ·
                    refine ⟨1062122752609920486762251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11329309361172485192130677 1062122752609920486762251)
                    ·
                      rfl

theorem cell23_6205430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_6205430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205430 prefixEnd_6205430 := by exact prefixLift 6205430
  have htrace : WordTrace (prefixWord ++ tailWord_6205430) baseStart_6205430 baseEnd_6205430 := by
    simpa [prefixWord, tailWord_6205430, baseEnd_6205430] using wordTrace_append hprefix tailTrace_6205430
  have hstable : (prefixWord ++ tailWord_6205430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205430).length < 2 ^ (prefixWord ++ tailWord_6205430).sum := by decide
  have hdescent : baseEnd_6205430 < baseStart_6205430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205433 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 3, 1, 4]
def baseStart_6205433 : Nat := 118140960795 + 6205433 * 2 ^ 59
def prefixEnd_6205433 : Nat := 4983230072969 + 3 ^ 40 * 6205433 * 2
def baseEnd_6205433 : Nat := 3186369798271724948549239

theorem tailTrace_6205433 : CollatzResearch.WordTrace tailWord_6205433 prefixEnd_6205433 3186369798271724948549239 := by
  unfold tailWord_6205433
  simp only [CollatzResearch.WordTrace]
  refine ⟨226330735327783519426236953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150887156885189012950824635 226330735327783519426236953)
  ·
    refine ⟨169748051495837639569677715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226330735327783519426236953 169748051495837639569677715)
    ·
      refine ⟨254622077243756459354516573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169748051495837639569677715 254622077243756459354516573)
      ·
        refine ⟨95483278966408672257943715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254622077243756459354516573 95483278966408672257943715)
        ·
          refine ⟨143224918449613008386915573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95483278966408672257943715 143224918449613008386915573)
          ·
            refine ⟨13427336104651219536273335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143224918449613008386915573 13427336104651219536273335)
            ·
              refine ⟨20141004156976829304410003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13427336104651219536273335 20141004156976829304410003)
              ·
                refine ⟨30211506235465243956615005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20141004156976829304410003 30211506235465243956615005)
                ·
                  refine ⟨11329314838299466483730627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30211506235465243956615005 11329314838299466483730627)
                  ·
                    refine ⟨16993972257449199725595941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11329314838299466483730627 16993972257449199725595941)
                    ·
                      refine ⟨3186369798271724948549239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16993972257449199725595941 3186369798271724948549239)
                      ·
                        rfl

theorem cell23_6205433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_6205433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205433 prefixEnd_6205433 := by exact prefixLift 6205433
  have htrace : WordTrace (prefixWord ++ tailWord_6205433) baseStart_6205433 baseEnd_6205433 := by
    simpa [prefixWord, tailWord_6205433, baseEnd_6205433] using wordTrace_append hprefix tailTrace_6205433
  have hstable : (prefixWord ++ tailWord_6205433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205433).length < 2 ^ (prefixWord ++ tailWord_6205433).sum := by decide
  have hdescent : baseEnd_6205433 < baseStart_6205433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205461 : List Nat := [1, 3, 2, 1, 5, 2, 2, 2, 1, 1, 3]
def baseStart_6205461 : Nat := 118140960795 + 6205461 * 2 ^ 59
def prefixEnd_6205461 : Nat := 4983230072969 + 3 ^ 40 * 6205461 * 2
def baseEnd_6205461 : Nat := 3186384175730050838999111

theorem tailTrace_6205461 : CollatzResearch.WordTrace tailWord_6205461 prefixEnd_6205461 3186384175730050838999111 := by
  unfold tailWord_6205461
  simp only [CollatzResearch.WordTrace]
  refine ⟨226331756571682080208256237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150887837714454720138837491 226331756571682080208256237)
  ·
    refine ⟨84874408714380780078096089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226331756571682080208256237 84874408714380780078096089)
    ·
      refine ⟨63655806535785585058572067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84874408714380780078096089 63655806535785585058572067)
      ·
        refine ⟨95483709803678377587858101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63655806535785585058572067 95483709803678377587858101)
        ·
          refine ⟨8951597794094847898861697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95483709803678377587858101 8951597794094847898861697)
          ·
            refine ⟨6713698345571135924146273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8951597794094847898861697 6713698345571135924146273)
            ·
              refine ⟨5035273759178351943109705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6713698345571135924146273 5035273759178351943109705)
              ·
                refine ⟨3776455319383763957332279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5035273759178351943109705 3776455319383763957332279)
                ·
                  refine ⟨5664682979075645935998419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3776455319383763957332279 5664682979075645935998419)
                  ·
                    refine ⟨8497024468613468903997629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5664682979075645935998419 8497024468613468903997629)
                    ·
                      refine ⟨3186384175730050838999111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8497024468613468903997629 3186384175730050838999111)
                      ·
                        rfl

theorem cell23_6205461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 1, 1, 3].length) (baseStart_6205461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205461 prefixEnd_6205461 := by exact prefixLift 6205461
  have htrace : WordTrace (prefixWord ++ tailWord_6205461) baseStart_6205461 baseEnd_6205461 := by
    simpa [prefixWord, tailWord_6205461, baseEnd_6205461] using wordTrace_append hprefix tailTrace_6205461
  have hstable : (prefixWord ++ tailWord_6205461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205461).length < 2 ^ (prefixWord ++ tailWord_6205461).sum := by decide
  have hdescent : baseEnd_6205461 < baseStart_6205461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205500 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 4, 1, 3]
def baseStart_6205500 : Nat := 118140960795 + 6205500 * 2 ^ 59
def prefixEnd_6205500 : Nat := 4983230072969 + 3 ^ 40 * 6205500 * 2
def baseEnd_6205500 : Nat := 3186404201475576186411431

theorem tailTrace_6205500 : CollatzResearch.WordTrace tailWord_6205500 prefixEnd_6205500 3186404201475576186411431 := by
  unfold tailWord_6205500
  simp only [CollatzResearch.WordTrace]
  refine ⟨113166589509270394934462977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150888786012360526579283969 113166589509270394934462977)
  ·
    refine ⟨84874942131952796200847233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113166589509270394934462977 84874942131952796200847233)
    ·
      refine ⟨63656206598964597150635425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84874942131952796200847233 63656206598964597150635425)
      ·
        refine ⟨47742154949223447862976569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63656206598964597150635425 47742154949223447862976569)
        ·
          refine ⟨35806616211917585897232427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47742154949223447862976569 35806616211917585897232427)
          ·
            refine ⟨53709924317876378845848641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35806616211917585897232427 53709924317876378845848641)
            ·
              refine ⟨40282443238407284134386481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53709924317876378845848641 40282443238407284134386481)
              ·
                refine ⟨30211832428805463100789861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40282443238407284134386481 30211832428805463100789861)
                ·
                  refine ⟨5664718580401024331398099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30211832428805463100789861 5664718580401024331398099)
                  ·
                    refine ⟨8497077870601536497097149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5664718580401024331398099 8497077870601536497097149)
                    ·
                      refine ⟨3186404201475576186411431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8497077870601536497097149 3186404201475576186411431)
                      ·
                        rfl

theorem cell23_6205500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_6205500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205500 prefixEnd_6205500 := by exact prefixLift 6205500
  have htrace : WordTrace (prefixWord ++ tailWord_6205500) baseStart_6205500 baseEnd_6205500 := by
    simpa [prefixWord, tailWord_6205500, baseEnd_6205500] using wordTrace_append hprefix tailTrace_6205500
  have hstable : (prefixWord ++ tailWord_6205500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205500).length < 2 ^ (prefixWord ++ tailWord_6205500).sum := by decide
  have hdescent : baseEnd_6205500 < baseStart_6205500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205517 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_6205517 : Nat := 118140960795 + 6205517 * 2 ^ 59
def prefixEnd_6205517 : Nat := 4983230072969 + 3 ^ 40 * 6205517 * 2
def baseEnd_6205517 : Nat := 3186412930646702619898853

theorem tailTrace_6205517 : CollatzResearch.WordTrace tailWord_6205517 prefixEnd_6205517 3186412930646702619898853 := by
  unfold tailWord_6205517
  simp only [CollatzResearch.WordTrace]
  refine ⟨226333799059479201772294805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150889199372986134514863203 226333799059479201772294805)
  ·
    refine ⟨10609396830913087583076319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 226333799059479201772294805 10609396830913087583076319)
    ·
      refine ⟨15914095246369631374614479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10609396830913087583076319 15914095246369631374614479)
      ·
        refine ⟨23871142869554447061921719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15914095246369631374614479 23871142869554447061921719)
        ·
          refine ⟨35806714304331670592882579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23871142869554447061921719 35806714304331670592882579)
          ·
            refine ⟨53710071456497505889323869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35806714304331670592882579 53710071456497505889323869)
            ·
              refine ⟨20141276796186564708496451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53710071456497505889323869 20141276796186564708496451)
              ·
                refine ⟨30211915194279847062744677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20141276796186564708496451 30211915194279847062744677)
                ·
                  refine ⟨5664734098927471324264627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30211915194279847062744677 5664734098927471324264627)
                  ·
                    refine ⟨8497101148391206986396941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5664734098927471324264627 8497101148391206986396941)
                    ·
                      refine ⟨3186412930646702619898853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8497101148391206986396941 3186412930646702619898853)
                      ·
                        rfl

theorem cell23_6205517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_6205517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205517 prefixEnd_6205517 := by exact prefixLift 6205517
  have htrace : WordTrace (prefixWord ++ tailWord_6205517) baseStart_6205517 baseEnd_6205517 := by
    simpa [prefixWord, tailWord_6205517, baseEnd_6205517] using wordTrace_append hprefix tailTrace_6205517
  have hstable : (prefixWord ++ tailWord_6205517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205517).length < 2 ^ (prefixWord ++ tailWord_6205517).sum := by decide
  have hdescent : baseEnd_6205517 < baseStart_6205517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205543 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_6205543 : Nat := 118140960795 + 6205543 * 2 ^ 59
def prefixEnd_6205543 : Nat := 4983230072969 + 3 ^ 40 * 6205543 * 2
def baseEnd_6205543 : Nat := 3186426281143719518173733

theorem tailTrace_6205543 : CollatzResearch.WordTrace tailWord_6205543 prefixEnd_6205543 3186426281143719518173733 := by
  unfold tailWord_6205543
  simp only [CollatzResearch.WordTrace]
  refine ⟨226334747357385008212741283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150889831571590005475160855 226334747357385008212741283)
  ·
    refine ⟨339502121036077512319111925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226334747357385008212741283 339502121036077512319111925)
    ·
      refine ⟨31828323847132266779916743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 339502121036077512319111925 31828323847132266779916743)
      ·
        refine ⟨47742485770698400169875115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31828323847132266779916743 47742485770698400169875115)
        ·
          refine ⟨71613728656047600254812673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47742485770698400169875115 71613728656047600254812673)
          ·
            refine ⟨53710296492035700191109505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71613728656047600254812673 53710296492035700191109505)
            ·
              refine ⟨40282722369026775143332129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53710296492035700191109505 40282722369026775143332129)
              ·
                refine ⟨30212041776770081357499097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40282722369026775143332129 30212041776770081357499097)
                ·
                  refine ⟨22659031332577561018124323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30212041776770081357499097 22659031332577561018124323)
                  ·
                    refine ⟨33988546998866341527186485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22659031332577561018124323 33988546998866341527186485)
                    ·
                      refine ⟨3186426281143719518173733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33988546998866341527186485 3186426281143719518173733)
                      ·
                        rfl

theorem cell23_6205543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_6205543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205543 prefixEnd_6205543 := by exact prefixLift 6205543
  have htrace : WordTrace (prefixWord ++ tailWord_6205543) baseStart_6205543 baseEnd_6205543 := by
    simpa [prefixWord, tailWord_6205543, baseEnd_6205543] using wordTrace_append hprefix tailTrace_6205543
  have hstable : (prefixWord ++ tailWord_6205543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205543).length < 2 ^ (prefixWord ++ tailWord_6205543).sum := by decide
  have hdescent : baseEnd_6205543 < baseStart_6205543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205640 : List Nat := [2, 1, 3, 1, 2, 1, 1, 5, 3, 4]
def baseStart_6205640 : Nat := 118140960795 + 6205640 * 2 ^ 59
def prefixEnd_6205640 : Nat := 4983230072969 + 3 ^ 40 * 6205640 * 2
def baseEnd_6205640 : Nat := 1062158696255735212886929

theorem tailTrace_6205640 : CollatzResearch.WordTrace tailWord_6205640 prefixEnd_6205640 1062158696255735212886929 := by
  unfold tailWord_6205640
  simp only [CollatzResearch.WordTrace]
  refine ⟨113169142619016796889511187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150892190158689062519348249 113169142619016796889511187)
  ·
    refine ⟨169753713928525195334266781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113169142619016796889511187 169753713928525195334266781)
    ·
      refine ⟨63657642723196948250350043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169753713928525195334266781 63657642723196948250350043)
      ·
        refine ⟨95486464084795422375525065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63657642723196948250350043 95486464084795422375525065)
        ·
          refine ⟨71614848063596566781643799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95486464084795422375525065 71614848063596566781643799)
          ·
            refine ⟨107422272095394850172465699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71614848063596566781643799 107422272095394850172465699)
            ·
              refine ⟨161133408143092275258698549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107422272095394850172465699 161133408143092275258698549)
              ·
                refine ⟨15106257013414900805502989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161133408143092275258698549 15106257013414900805502989)
                ·
                  refine ⟨5664846380030587802063621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15106257013414900805502989 5664846380030587802063621)
                  ·
                    refine ⟨1062158696255735212886929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5664846380030587802063621 1062158696255735212886929)
                    ·
                      rfl

theorem cell23_6205640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_6205640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205640 prefixEnd_6205640 := by exact prefixLift 6205640
  have htrace : WordTrace (prefixWord ++ tailWord_6205640) baseStart_6205640 baseEnd_6205640 := by
    simpa [prefixWord, tailWord_6205640, baseEnd_6205640] using wordTrace_append hprefix tailTrace_6205640
  have hstable : (prefixWord ++ tailWord_6205640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205640).length < 2 ^ (prefixWord ++ tailWord_6205640).sum := by decide
  have hdescent : baseEnd_6205640 < baseStart_6205640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205674 : List Nat := [3, 1, 3, 1, 1, 2, 4, 3, 1, 4]
def baseStart_6205674 : Nat := 118140960795 + 6205674 * 2 ^ 59
def prefixEnd_6205674 : Nat := 4983230072969 + 3 ^ 40 * 6205674 * 2
def baseEnd_6205674 : Nat := 1062164515703152835211877

theorem tailTrace_6205674 : CollatzResearch.WordTrace tailWord_6205674 prefixEnd_6205674 1062164515703152835211877 := by
  unfold tailWord_6205674
  simp only [CollatzResearch.WordTrace]
  refine ⟨56584881329977604396440019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150893016879940278390506717 56584881329977604396440019)
  ·
    refine ⟨84877321994966406594660029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56584881329977604396440019 84877321994966406594660029)
    ·
      refine ⟨31828995748112402472997511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84877321994966406594660029 31828995748112402472997511)
      ·
        refine ⟨47743493622168603709496267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31828995748112402472997511 47743493622168603709496267)
        ·
          refine ⟨71615240433252905564244401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47743493622168603709496267 71615240433252905564244401)
          ·
            refine ⟨53711430324939679173183301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71615240433252905564244401 53711430324939679173183301)
            ·
              refine ⟨10070893185926189844971869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53711430324939679173183301 10070893185926189844971869)
              ·
                refine ⟨3776584944722321191864451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10070893185926189844971869 3776584944722321191864451)
                ·
                  refine ⟨5664877417083481787796677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3776584944722321191864451 5664877417083481787796677)
                  ·
                    refine ⟨1062164515703152835211877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5664877417083481787796677 1062164515703152835211877)
                    ·
                      rfl

theorem cell23_6205674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_6205674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205674 prefixEnd_6205674 := by exact prefixLift 6205674
  have htrace : WordTrace (prefixWord ++ tailWord_6205674) baseStart_6205674 baseEnd_6205674 := by
    simpa [prefixWord, tailWord_6205674, baseEnd_6205674] using wordTrace_append hprefix tailTrace_6205674
  have hstable : (prefixWord ++ tailWord_6205674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205674).length < 2 ^ (prefixWord ++ tailWord_6205674).sum := by decide
  have hdescent : baseEnd_6205674 < baseStart_6205674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205740 : List Nat := [2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 5]
def baseStart_6205740 : Nat := 118140960795 + 6205740 * 2 ^ 59
def prefixEnd_6205740 : Nat := 4983230072969 + 3 ^ 40 * 6205740 * 2
def baseEnd_6205740 : Nat := 3186527436832655247410327

theorem tailTrace_6205740 : CollatzResearch.WordTrace tailWord_6205740 prefixEnd_6205740 3186527436832655247410327 := by
  unfold tailWord_6205740
  simp only [CollatzResearch.WordTrace]
  refine ⟨113170966268835655428831337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150894621691780873905108449 113170966268835655428831337)
  ·
    refine ⟨84878224701626741571623503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113170966268835655428831337 84878224701626741571623503)
    ·
      refine ⟨127317337052440112357435255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84878224701626741571623503 127317337052440112357435255)
      ·
        refine ⟨190976005578660168536152883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127317337052440112357435255 190976005578660168536152883)
        ·
          refine ⟨286464008367990252804229325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190976005578660168536152883 286464008367990252804229325)
          ·
            refine ⟨107424003137996344801585997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286464008367990252804229325 107424003137996344801585997)
            ·
              refine ⟨40284001176748629300594749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107424003137996344801585997 40284001176748629300594749)
              ·
                refine ⟨15106500441280735987723031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40284001176748629300594749 15106500441280735987723031)
                ·
                  refine ⟨22659750661921103981584547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15106500441280735987723031 22659750661921103981584547)
                  ·
                    refine ⟨33989625992881655972376821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22659750661921103981584547 33989625992881655972376821)
                    ·
                      refine ⟨3186527436832655247410327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33989625992881655972376821 3186527436832655247410327)
                      ·
                        rfl

theorem cell23_6205740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_6205740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205740 prefixEnd_6205740 := by exact prefixLift 6205740
  have htrace : WordTrace (prefixWord ++ tailWord_6205740) baseStart_6205740 baseEnd_6205740 := by
    simpa [prefixWord, tailWord_6205740, baseEnd_6205740] using wordTrace_append hprefix tailTrace_6205740
  have hstable : (prefixWord ++ tailWord_6205740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205740).length < 2 ^ (prefixWord ++ tailWord_6205740).sum := by decide
  have hdescent : baseEnd_6205740 < baseStart_6205740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205743 : List Nat := [1, 1, 2, 1, 2, 1, 15]
def baseStart_6205743 : Nat := 118140960795 + 6205743 * 2 ^ 59
def prefixEnd_6205743 : Nat := 4983230072969 + 3 ^ 40 * 6205743 * 2
def baseEnd_6205743 : Nat := 39339863916970601674973

theorem tailTrace_6205743 : CollatzResearch.WordTrace tailWord_6205743 prefixEnd_6205743 39339863916970601674973 := by
  unfold tailWord_6205743
  simp only [CollatzResearch.WordTrace]
  refine ⟨226342041956660442370021883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150894694637773628246681255 226342041956660442370021883)
  ·
    refine ⟨339513062934990663555032825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226342041956660442370021883 339513062934990663555032825)
    ·
      refine ⟨254634797201242997666274619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339513062934990663555032825 254634797201242997666274619)
      ·
        refine ⟨381952195801864496499411929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254634797201242997666274619 381952195801864496499411929)
        ·
          refine ⟨286464146851398372374558947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 381952195801864496499411929 286464146851398372374558947)
          ·
            refine ⟨429696220277097558561838421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286464146851398372374558947 429696220277097558561838421)
            ·
              refine ⟨39339863916970601674973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 429696220277097558561838421 39339863916970601674973)
              ·
                rfl

theorem cell23_6205743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 15].length) (baseStart_6205743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205743 prefixEnd_6205743 := by exact prefixLift 6205743
  have htrace : WordTrace (prefixWord ++ tailWord_6205743) baseStart_6205743 baseEnd_6205743 := by
    simpa [prefixWord, tailWord_6205743, baseEnd_6205743] using wordTrace_append hprefix tailTrace_6205743
  have hstable : (prefixWord ++ tailWord_6205743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205743).length < 2 ^ (prefixWord ++ tailWord_6205743).sum := by decide
  have hdescent : baseEnd_6205743 < baseStart_6205743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205747 : List Nat := [1, 1, 1, 2, 5, 1, 2, 4, 2, 4]
def baseStart_6205747 : Nat := 118140960795 + 6205747 * 2 ^ 59
def prefixEnd_6205747 : Nat := 4983230072969 + 3 ^ 40 * 6205747 * 2
def baseEnd_6205747 : Nat := 1062177010399078906674265

theorem tailTrace_6205747 : CollatzResearch.WordTrace tailWord_6205747 prefixEnd_6205747 1062177010399078906674265 := by
  unfold tailWord_6205747
  simp only [CollatzResearch.WordTrace]
  refine ⟨226342187848645951053167495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150894791899097300702111663 226342187848645951053167495)
  ·
    refine ⟨339513281772968926579751243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226342187848645951053167495 339513281772968926579751243)
    ·
      refine ⟨509269922659453389869626865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339513281772968926579751243 509269922659453389869626865)
      ·
        refine ⟨381952441994590042402220149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 509269922659453389869626865 381952441994590042402220149)
        ·
          refine ⟨35808041436992816475208139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 381952441994590042402220149 35808041436992816475208139)
          ·
            refine ⟨53712062155489224712812209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35808041436992816475208139 53712062155489224712812209)
            ·
              refine ⟨40284046616616918534609157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53712062155489224712812209 40284046616616918534609157)
              ·
                refine ⟨7553258740615672225239217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40284046616616918534609157 7553258740615672225239217)
                ·
                  refine ⟨5664944055461754168929413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7553258740615672225239217 5664944055461754168929413)
                  ·
                    refine ⟨1062177010399078906674265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5664944055461754168929413 1062177010399078906674265)
                    ·
                      rfl

theorem cell23_6205747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 4].length) (baseStart_6205747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205747 prefixEnd_6205747 := by exact prefixLift 6205747
  have htrace : WordTrace (prefixWord ++ tailWord_6205747) baseStart_6205747 baseEnd_6205747 := by
    simpa [prefixWord, tailWord_6205747, baseEnd_6205747] using wordTrace_append hprefix tailTrace_6205747
  have hstable : (prefixWord ++ tailWord_6205747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205747).length < 2 ^ (prefixWord ++ tailWord_6205747).sum := by decide
  have hdescent : baseEnd_6205747 < baseStart_6205747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205788 : List Nat := [2, 2, 4, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_6205788 : Nat := 118140960795 + 6205788 * 2 ^ 59
def prefixEnd_6205788 : Nat := 4983230072969 + 3 ^ 40 * 6205788 * 2
def baseEnd_6205788 : Nat := 3186552083904071059610107

theorem tailTrace_6205788 : CollatzResearch.WordTrace tailWord_6205788 prefixEnd_6205788 3186552083904071059610107 := by
  unfold tailWord_6205788
  simp only [CollatzResearch.WordTrace]
  refine ⟨113171841620748707527705009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150895788827664943370273345 113171841620748707527705009)
  ·
    refine ⟨84878881215561530645778757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113171841620748707527705009 84878881215561530645778757)
    ·
      refine ⟨15914790227917786996083517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84878881215561530645778757 15914790227917786996083517)
      ·
        refine ⟨5968046335469170123531319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15914790227917786996083517 5968046335469170123531319)
        ·
          refine ⟨8952069503203755185296979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5968046335469170123531319 8952069503203755185296979)
          ·
            refine ⟨13428104254805632777945469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8952069503203755185296979 13428104254805632777945469)
            ·
              refine ⟨5035539095552112291729551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13428104254805632777945469 5035539095552112291729551)
              ·
                refine ⟨7553308643328168437594327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5035539095552112291729551 7553308643328168437594327)
                ·
                  refine ⟨11329962964992252656391491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7553308643328168437594327 11329962964992252656391491)
                  ·
                    refine ⟨16994944447488378984587237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11329962964992252656391491 16994944447488378984587237)
                    ·
                      refine ⟨3186552083904071059610107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16994944447488378984587237 3186552083904071059610107)
                      ·
                        rfl

theorem cell23_6205788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_6205788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205788 prefixEnd_6205788 := by exact prefixLift 6205788
  have htrace : WordTrace (prefixWord ++ tailWord_6205788) baseStart_6205788 baseEnd_6205788 := by
    simpa [prefixWord, tailWord_6205788, baseEnd_6205788] using wordTrace_append hprefix tailTrace_6205788
  have hstable : (prefixWord ++ tailWord_6205788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205788).length < 2 ^ (prefixWord ++ tailWord_6205788).sum := by decide
  have hdescent : baseEnd_6205788 < baseStart_6205788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205848 : List Nat := [2, 1, 2, 5, 1, 1, 4, 1, 1, 3, 2]
def baseStart_6205848 : Nat := 118140960795 + 6205848 * 2 ^ 59
def prefixEnd_6205848 : Nat := 4983230072969 + 3 ^ 40 * 6205848 * 2
def baseEnd_6205848 : Nat := 3186582892743340824859831

theorem tailTrace_6205848 : CollatzResearch.WordTrace tailWord_6205848 prefixEnd_6205848 3186582892743340824859831 := by
  unfold tailWord_6205848
  simp only [CollatzResearch.WordTrace]
  refine ⟨113172935810640022651297099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150897247747520030201729465 113172935810640022651297099)
  ·
    refine ⟨169759403715960033976945649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113172935810640022651297099 169759403715960033976945649)
    ·
      refine ⟨127319552786970025482709237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169759403715960033976945649 127319552786970025482709237)
      ·
        refine ⟨11936208073778439889003991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127319552786970025482709237 11936208073778439889003991)
        ·
          refine ⟨17904312110667659833505987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11936208073778439889003991 17904312110667659833505987)
          ·
            refine ⟨26856468166001489750258981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17904312110667659833505987 26856468166001489750258981)
            ·
              refine ⟨5035587781125279328173559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26856468166001489750258981 5035587781125279328173559)
              ·
                refine ⟨7553381671687918992260339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5035587781125279328173559 7553381671687918992260339)
                ·
                  refine ⟨11330072507531878488390509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7553381671687918992260339 11330072507531878488390509)
                  ·
                    refine ⟨4248777190324454433146441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11330072507531878488390509 4248777190324454433146441)
                    ·
                      refine ⟨3186582892743340824859831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4248777190324454433146441 3186582892743340824859831)
                      ·
                        rfl

theorem cell23_6205848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_6205848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205848 prefixEnd_6205848 := by exact prefixLift 6205848
  have htrace : WordTrace (prefixWord ++ tailWord_6205848) baseStart_6205848 baseEnd_6205848 := by
    simpa [prefixWord, tailWord_6205848, baseEnd_6205848] using wordTrace_append hprefix tailTrace_6205848
  have hstable : (prefixWord ++ tailWord_6205848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205848).length < 2 ^ (prefixWord ++ tailWord_6205848).sum := by decide
  have hdescent : baseEnd_6205848 < baseStart_6205848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205854 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_6205854 : Nat := 118140960795 + 6205854 * 2 ^ 59
def prefixEnd_6205854 : Nat := 4983230072969 + 3 ^ 40 * 6205854 * 2
def baseEnd_6205854 : Nat := 1062195324542422600461601

theorem tailTrace_6205854 : CollatzResearch.WordTrace tailWord_6205854 prefixEnd_6205854 1062195324542422600461601 := by
  unfold tailWord_6205854
  simp only [CollatzResearch.WordTrace]
  refine ⟨28293261307407288540914077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150897393639505538884875077 28293261307407288540914077)
  ·
    refine ⟨10609972990277733202842779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28293261307407288540914077 10609972990277733202842779)
    ·
      refine ⟨15914959485416599804264169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10609972990277733202842779 15914959485416599804264169)
      ·
        refine ⟨11936219614062449853198127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15914959485416599804264169 11936219614062449853198127)
        ·
          refine ⟨17904329421093674779797191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11936219614062449853198127 17904329421093674779797191)
          ·
            refine ⟨26856494131640512169695787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17904329421093674779797191 26856494131640512169695787)
            ·
              refine ⟨40284741197460768254543681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26856494131640512169695787 40284741197460768254543681)
              ·
                refine ⟨30213555898095576190907761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40284741197460768254543681 30213555898095576190907761)
                ·
                  refine ⟨22660166923571682143180821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30213555898095576190907761 22660166923571682143180821)
                  ·
                    refine ⟨1062195324542422600461601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22660166923571682143180821 1062195324542422600461601)
                    ·
                      rfl

theorem cell23_6205854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_6205854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205854 prefixEnd_6205854 := by exact prefixLift 6205854
  have htrace : WordTrace (prefixWord ++ tailWord_6205854) baseStart_6205854 baseEnd_6205854 := by
    simpa [prefixWord, tailWord_6205854, baseEnd_6205854] using wordTrace_append hprefix tailTrace_6205854
  have hstable : (prefixWord ++ tailWord_6205854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205854).length < 2 ^ (prefixWord ++ tailWord_6205854).sum := by decide
  have hdescent : baseEnd_6205854 < baseStart_6205854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205958 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_6205958 : Nat := 118140960795 + 6205958 * 2 ^ 59
def prefixEnd_6205958 : Nat := 4983230072969 + 3 ^ 40 * 6205958 * 2
def baseEnd_6205958 : Nat := 3186639375615335394484325

theorem tailTrace_6205958 : CollatzResearch.WordTrace tailWord_6205958 prefixEnd_6205958 3186639375615335394484325 := by
  unfold tailWord_6205958
  simp only [CollatzResearch.WordTrace]
  refine ⟨7073433864090047940284329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 150899922433921022726065685 7073433864090047940284329)
  ·
    refine ⟨5305075398067535955213247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7073433864090047940284329 5305075398067535955213247)
    ·
      refine ⟨7957613097101303932819871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5305075398067535955213247 7957613097101303932819871)
      ·
        refine ⟨11936419645651955899229807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7957613097101303932819871 11936419645651955899229807)
        ·
          refine ⟨17904629468477933848844711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11936419645651955899229807 17904629468477933848844711)
          ·
            refine ⟨26856944202716900773267067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17904629468477933848844711 26856944202716900773267067)
            ·
              refine ⟨40285416304075351159900601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26856944202716900773267067 40285416304075351159900601)
              ·
                refine ⟨30214062228056513369925451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40285416304075351159900601 30214062228056513369925451)
                ·
                  refine ⟨45321093342084770054888177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30214062228056513369925451 45321093342084770054888177)
                  ·
                    refine ⟨33990820006563577541166133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45321093342084770054888177 33990820006563577541166133)
                    ·
                      refine ⟨3186639375615335394484325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33990820006563577541166133 3186639375615335394484325)
                      ·
                        rfl

theorem cell23_6205958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_6205958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205958 prefixEnd_6205958 := by exact prefixLift 6205958
  have htrace : WordTrace (prefixWord ++ tailWord_6205958) baseStart_6205958 baseEnd_6205958 := by
    simpa [prefixWord, tailWord_6205958, baseEnd_6205958] using wordTrace_append hprefix tailTrace_6205958
  have hstable : (prefixWord ++ tailWord_6205958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205958).length < 2 ^ (prefixWord ++ tailWord_6205958).sum := by decide
  have hdescent : baseEnd_6205958 < baseStart_6205958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6205978 : List Nat := [3, 1, 1, 3, 1, 1, 6, 2, 1, 4]
def baseStart_6205978 : Nat := 118140960795 + 6205978 * 2 ^ 59
def prefixEnd_6205978 : Nat := 4983230072969 + 3 ^ 40 * 6205978 * 2
def baseEnd_6205978 : Nat := 1062216548409475105411411

theorem tailTrace_6205978 : CollatzResearch.WordTrace tailWord_6205978 prefixEnd_6205978 1062216548409475105411411 := by
  unfold tailWord_6205978
  simp only [CollatzResearch.WordTrace]
  refine ⟨56587653277702269376206647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150900408740539385003217725 56587653277702269376206647)
  ·
    refine ⟨84881479916553404064309971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56587653277702269376206647 84881479916553404064309971)
    ·
      refine ⟨127322219874830106096464957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84881479916553404064309971 127322219874830106096464957)
      ·
        refine ⟨47745832453061289786174359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127322219874830106096464957 47745832453061289786174359)
        ·
          refine ⟨71618748679591934679261539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47745832453061289786174359 71618748679591934679261539)
          ·
            refine ⟨107428123019387902018892309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71618748679591934679261539 107428123019387902018892309)
            ·
              refine ⟨5035693266533807907135577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107428123019387902018892309 5035693266533807907135577)
              ·
                refine ⟨3776769949900355930351683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5035693266533807907135577 3776769949900355930351683)
                ·
                  refine ⟨5665154924850533895527525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3776769949900355930351683 5665154924850533895527525)
                  ·
                    refine ⟨1062216548409475105411411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5665154924850533895527525 1062216548409475105411411)
                    ·
                      rfl

theorem cell23_6205978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 1, 4].length) (baseStart_6205978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6205978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6205978 prefixEnd_6205978 := by exact prefixLift 6205978
  have htrace : WordTrace (prefixWord ++ tailWord_6205978) baseStart_6205978 baseEnd_6205978 := by
    simpa [prefixWord, tailWord_6205978, baseEnd_6205978] using wordTrace_append hprefix tailTrace_6205978
  have hstable : (prefixWord ++ tailWord_6205978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6205978).length < 2 ^ (prefixWord ++ tailWord_6205978).sum := by decide
  have hdescent : baseEnd_6205978 < baseStart_6205978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6205978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206021 : List Nat := [1, 3, 1, 1, 1, 5, 4, 1, 1, 5]
def baseStart_6206021 : Nat := 118140960795 + 6206021 * 2 ^ 59
def prefixEnd_6206021 : Nat := 4983230072969 + 3 ^ 40 * 6206021 * 2
def baseEnd_6206021 : Nat := 1062223908298856215998845

theorem tailTrace_6206021 : CollatzResearch.WordTrace tailWord_6206021 prefixEnd_6206021 1062223908298856215998845 := by
  unfold tailWord_6206021
  simp only [CollatzResearch.WordTrace]
  refine ⟨226352181449653295848641917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150901454299768863899094611 226352181449653295848641917)
  ·
    refine ⟨84882068043619985943240719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226352181449653295848641917 84882068043619985943240719)
    ·
      refine ⟨127323102065429978914861079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84882068043619985943240719 127323102065429978914861079)
      ·
        refine ⟨190984653098144968372291619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127323102065429978914861079 190984653098144968372291619)
        ·
          refine ⟨286476979647217452558437429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190984653098144968372291619 286476979647217452558437429)
          ·
            refine ⟨26857216841926636177353509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 286476979647217452558437429 26857216841926636177353509)
            ·
              refine ⟨5035728157861244283253783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26857216841926636177353509 5035728157861244283253783)
              ·
                refine ⟨7553592236791866424880675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5035728157861244283253783 7553592236791866424880675)
                ·
                  refine ⟨11330388355187799637321013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7553592236791866424880675 11330388355187799637321013)
                  ·
                    refine ⟨1062223908298856215998845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11330388355187799637321013 1062223908298856215998845)
                    ·
                      rfl

theorem cell23_6206021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 1, 5].length) (baseStart_6206021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206021 prefixEnd_6206021 := by exact prefixLift 6206021
  have htrace : WordTrace (prefixWord ++ tailWord_6206021) baseStart_6206021 baseEnd_6206021 := by
    simpa [prefixWord, tailWord_6206021, baseEnd_6206021] using wordTrace_append hprefix tailTrace_6206021
  have hstable : (prefixWord ++ tailWord_6206021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206021).length < 2 ^ (prefixWord ++ tailWord_6206021).sum := by decide
  have hdescent : baseEnd_6206021 < baseStart_6206021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206024 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 1, 8, 2]
def baseStart_6206024 : Nat := 118140960795 + 6206024 * 2 ^ 59
def prefixEnd_6206024 : Nat := 4983230072969 + 3 ^ 40 * 6206024 * 2
def baseEnd_6206024 : Nat := 3186673265338532136259021

theorem tailTrace_6206024 : CollatzResearch.WordTrace tailWord_6206024 prefixEnd_6206024 3186673265338532136259021 := by
  unfold tailWord_6206024
  simp only [CollatzResearch.WordTrace]
  refine ⟨113176145434321213680500563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150901527245761618240667417 113176145434321213680500563)
  ·
    refine ⟨169764218151481820520750845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113176145434321213680500563 169764218151481820520750845)
    ·
      refine ⟨63661581806805682695281567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169764218151481820520750845 63661581806805682695281567)
      ·
        refine ⟨95492372710208524042922351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63661581806805682695281567 95492372710208524042922351)
        ·
          refine ⟨143238559065312786064383527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95492372710208524042922351 143238559065312786064383527)
          ·
            refine ⟨214857838597969179096575291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143238559065312786064383527 214857838597969179096575291)
            ·
              refine ⟨322286757896953768644862937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214857838597969179096575291 322286757896953768644862937)
              ·
                refine ⟨241715068422715326483647203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322286757896953768644862937 241715068422715326483647203)
                ·
                  refine ⟨362572602634072989725470805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241715068422715326483647203 362572602634072989725470805)
                  ·
                    refine ⟨4248897687118042848345361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 362572602634072989725470805 4248897687118042848345361)
                    ·
                      refine ⟨3186673265338532136259021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4248897687118042848345361 3186673265338532136259021)
                      ·
                        rfl

theorem cell23_6206024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_6206024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206024 prefixEnd_6206024 := by exact prefixLift 6206024
  have htrace : WordTrace (prefixWord ++ tailWord_6206024) baseStart_6206024 baseEnd_6206024 := by
    simpa [prefixWord, tailWord_6206024, baseEnd_6206024] using wordTrace_append hprefix tailTrace_6206024
  have hstable : (prefixWord ++ tailWord_6206024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206024).length < 2 ^ (prefixWord ++ tailWord_6206024).sum := by decide
  have hdescent : baseEnd_6206024 < baseStart_6206024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206058 : List Nat := [3, 1, 3, 2, 1, 1, 1, 4, 3, 2, 2]
def baseStart_6206058 : Nat := 118140960795 + 6206058 * 2 ^ 59
def prefixEnd_6206058 : Nat := 4983230072969 + 3 ^ 40 * 6206058 * 2
def baseEnd_6206058 : Nat := 3186690723680785003233865

theorem tailTrace_6206058 : CollatzResearch.WordTrace tailWord_6206058 prefixEnd_6206058 3186690723680785003233865 := by
  unfold tailWord_6206058
  simp only [CollatzResearch.WordTrace]
  refine ⟨56588382737629812791934707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150902353967012834111825885 56588382737629812791934707)
  ·
    refine ⟨84882574106444719187902061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56588382737629812791934707 84882574106444719187902061)
    ·
      refine ⟨31830965289916769695463273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84882574106444719187902061 31830965289916769695463273)
      ·
        refine ⟨23873223967437577271597455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31830965289916769695463273 23873223967437577271597455)
        ·
          refine ⟨35809835951156365907396183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23873223967437577271597455 35809835951156365907396183)
          ·
            refine ⟨53714753926734548861094275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35809835951156365907396183 53714753926734548861094275)
            ·
              refine ⟨80572130890101823291641413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53714753926734548861094275 80572130890101823291641413)
              ·
                refine ⟨15107274541894091867182765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80572130890101823291641413 15107274541894091867182765)
                ·
                  refine ⟨5665227953210284450193537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15107274541894091867182765 5665227953210284450193537)
                  ·
                    refine ⟨4248920964907713337645153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5665227953210284450193537 4248920964907713337645153)
                    ·
                      refine ⟨3186690723680785003233865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4248920964907713337645153 3186690723680785003233865)
                      ·
                        rfl

theorem cell23_6206058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_6206058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206058 prefixEnd_6206058 := by exact prefixLift 6206058
  have htrace : WordTrace (prefixWord ++ tailWord_6206058) baseStart_6206058 baseEnd_6206058 := by
    simpa [prefixWord, tailWord_6206058, baseEnd_6206058] using wordTrace_append hprefix tailTrace_6206058
  have hstable : (prefixWord ++ tailWord_6206058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206058).length < 2 ^ (prefixWord ++ tailWord_6206058).sum := by decide
  have hdescent : baseEnd_6206058 < baseStart_6206058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206064 : List Nat := [2, 1, 1, 1, 7, 1, 1, 9]
def baseStart_6206064 : Nat := 118140960795 + 6206064 * 2 ^ 59
def prefixEnd_6206064 : Nat := 4983230072969 + 3 ^ 40 * 6206064 * 2
def baseEnd_6206064 : Nat := 118025696465359702954031

theorem tailTrace_6206064 : CollatzResearch.WordTrace tailWord_6206064 prefixEnd_6206064 118025696465359702954031 := by
  unfold tailWord_6206064
  simp only [CollatzResearch.WordTrace]
  refine ⟨113176874894248757096228623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150902499858998342794971497 113176874894248757096228623)
  ·
    refine ⟨169765312341373135644342935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113176874894248757096228623 169765312341373135644342935)
    ·
      refine ⟨254647968512059703466514403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169765312341373135644342935 254647968512059703466514403)
      ·
        refine ⟨381971952768089555199771605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254647968512059703466514403 381971952768089555199771605)
        ·
          refine ⟨8952467643002098949994647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 381971952768089555199771605 8952467643002098949994647)
          ·
            refine ⟨13428701464503148424991971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8952467643002098949994647 13428701464503148424991971)
            ·
              refine ⟨20143052196754722637487957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13428701464503148424991971 20143052196754722637487957)
              ·
                refine ⟨118025696465359702954031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20143052196754722637487957 118025696465359702954031)
                ·
                  rfl

theorem cell23_6206064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 9].length) (baseStart_6206064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206064 prefixEnd_6206064 := by exact prefixLift 6206064
  have htrace : WordTrace (prefixWord ++ tailWord_6206064) baseStart_6206064 baseEnd_6206064 := by
    simpa [prefixWord, tailWord_6206064, baseEnd_6206064] using wordTrace_append hprefix tailTrace_6206064
  have hstable : (prefixWord ++ tailWord_6206064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206064).length < 2 ^ (prefixWord ++ tailWord_6206064).sum := by decide
  have hdescent : baseEnd_6206064 < baseStart_6206064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206069 : List Nat := [1, 3, 4, 2, 3, 1, 1, 3, 1, 1, 3]
def baseStart_6206069 : Nat := 118140960795 + 6206069 * 2 ^ 59
def prefixEnd_6206069 : Nat := 4983230072969 + 3 ^ 40 * 6206069 * 2
def baseEnd_6206069 : Nat := 3186696371967984460196315

theorem tailTrace_6206069 : CollatzResearch.WordTrace tailWord_6206069 prefixEnd_6206069 3186696371967984460196315 := by
  unfold tailWord_6206069
  simp only [CollatzResearch.WordTrace]
  refine ⟨226353932153479400046389261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150902621435652933364259507 226353932153479400046389261)
  ·
    refine ⟨84882724557554775017395973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226353932153479400046389261 84882724557554775017395973)
    ·
      refine ⟨15915510854541520315761745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84882724557554775017395973 15915510854541520315761745)
      ·
        refine ⟨11936633140906140236821309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15915510854541520315761745 11936633140906140236821309)
        ·
          refine ⟨4476237427839802588807991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11936633140906140236821309 4476237427839802588807991)
          ·
            refine ⟨6714356141759703883211987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4476237427839802588807991 6714356141759703883211987)
            ·
              refine ⟨10071534212639555824817981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6714356141759703883211987 10071534212639555824817981)
              ·
                refine ⟨3776825329739833434306743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10071534212639555824817981 3776825329739833434306743)
                ·
                  refine ⟨5665237994609750151460115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3776825329739833434306743 5665237994609750151460115)
                  ·
                    refine ⟨8497856991914625227190173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5665237994609750151460115 8497856991914625227190173)
                    ·
                      refine ⟨3186696371967984460196315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8497856991914625227190173 3186696371967984460196315)
                      ·
                        rfl

theorem cell23_6206069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_6206069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206069 prefixEnd_6206069 := by exact prefixLift 6206069
  have htrace : WordTrace (prefixWord ++ tailWord_6206069) baseStart_6206069 baseEnd_6206069 := by
    simpa [prefixWord, tailWord_6206069, baseEnd_6206069] using wordTrace_append hprefix tailTrace_6206069
  have hstable : (prefixWord ++ tailWord_6206069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206069).length < 2 ^ (prefixWord ++ tailWord_6206069).sum := by decide
  have hdescent : baseEnd_6206069 < baseStart_6206069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206094 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 2, 7]
def baseStart_6206094 : Nat := 118140960795 + 6206094 * 2 ^ 59
def prefixEnd_6206094 : Nat := 4983230072969 + 3 ^ 40 * 6206094 * 2
def baseEnd_6206094 : Nat := 1062236402994782287461233

theorem tailTrace_6206094 : CollatzResearch.WordTrace tailWord_6206094 prefixEnd_6206094 1062236402994782287461233 := by
  unfold tailWord_6206094
  simp only [CollatzResearch.WordTrace]
  refine ⟨28294355497298603664506167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150903229318925886210699557 28294355497298603664506167)
  ·
    refine ⟨42441533245947905496759251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28294355497298603664506167 42441533245947905496759251)
    ·
      refine ⟨63662299868921858245138877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42441533245947905496759251 63662299868921858245138877)
      ·
        refine ⟨23873362450845696841927079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63662299868921858245138877 23873362450845696841927079)
        ·
          refine ⟨35810043676268545262890619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23873362450845696841927079 35810043676268545262890619)
          ·
            refine ⟨53715065514402817894335929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35810043676268545262890619 53715065514402817894335929)
            ·
              refine ⟨40286299135802113420751947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53715065514402817894335929 40286299135802113420751947)
              ·
                refine ⟨60429448703703170131127921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40286299135802113420751947 60429448703703170131127921)
                ·
                  refine ⟨45322086527777377598345941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60429448703703170131127921 45322086527777377598345941)
                  ·
                    refine ⟨1062236402994782287461233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45322086527777377598345941 1062236402994782287461233)
                    ·
                      rfl

theorem cell23_6206094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_6206094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206094 prefixEnd_6206094 := by exact prefixLift 6206094
  have htrace : WordTrace (prefixWord ++ tailWord_6206094) baseStart_6206094 baseEnd_6206094 := by
    simpa [prefixWord, tailWord_6206094, baseEnd_6206094] using wordTrace_append hprefix tailTrace_6206094
  have hstable : (prefixWord ++ tailWord_6206094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206094).length < 2 ^ (prefixWord ++ tailWord_6206094).sum := by decide
  have hdescent : baseEnd_6206094 < baseStart_6206094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206097 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 10]
def baseStart_6206097 : Nat := 118140960795 + 6206097 * 2 ^ 59
def prefixEnd_6206097 : Nat := 4983230072969 + 3 ^ 40 * 6206097 * 2
def baseEnd_6206097 : Nat := 3186710749426310350646185

theorem tailTrace_6206097 : CollatzResearch.WordTrace tailWord_6206097 prefixEnd_6206097 3186710749426310350646185 := by
  unfold tailWord_6206097
  simp only [CollatzResearch.WordTrace]
  refine ⟨226354953397377960828408545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150903302264918640552272363 226354953397377960828408545)
  ·
    refine ⟨169766215048033470621306409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226354953397377960828408545 169766215048033470621306409)
    ·
      refine ⟨127324661286025102965979807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169766215048033470621306409 127324661286025102965979807)
      ·
        refine ⟨190986991929037654448969711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127324661286025102965979807 190986991929037654448969711)
        ·
          refine ⟨286480487893556481673454567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190986991929037654448969711 286480487893556481673454567)
          ·
            refine ⟨429720731840334722510181851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286480487893556481673454567 429720731840334722510181851)
            ·
              refine ⟨644581097760502083765272777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429720731840334722510181851 644581097760502083765272777)
              ·
                refine ⟨483435823320376562823954583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 644581097760502083765272777 483435823320376562823954583)
                ·
                  refine ⟨725153734980564844235931875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483435823320376562823954583 725153734980564844235931875)
                  ·
                    refine ⟨1087730602470847266353897813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 725153734980564844235931875 1087730602470847266353897813)
                    ·
                      refine ⟨3186710749426310350646185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1087730602470847266353897813 3186710749426310350646185)
                      ·
                        rfl

theorem cell23_6206097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_6206097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206097 prefixEnd_6206097 := by exact prefixLift 6206097
  have htrace : WordTrace (prefixWord ++ tailWord_6206097) baseStart_6206097 baseEnd_6206097 := by
    simpa [prefixWord, tailWord_6206097, baseEnd_6206097] using wordTrace_append hprefix tailTrace_6206097
  have hstable : (prefixWord ++ tailWord_6206097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206097).length < 2 ^ (prefixWord ++ tailWord_6206097).sum := by decide
  have hdescent : baseEnd_6206097 < baseStart_6206097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206107 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 5, 8]
def baseStart_6206107 : Nat := 118140960795 + 6206107 * 2 ^ 59
def prefixEnd_6206107 : Nat := 4983230072969 + 3 ^ 40 * 6206107 * 2
def baseEnd_6206107 : Nat := 1062238628077618437173713

theorem tailTrace_6206107 : CollatzResearch.WordTrace tailWord_6206107 prefixEnd_6206107 1062238628077618437173713 := by
  unfold tailWord_6206107
  simp only [CollatzResearch.WordTrace]
  refine ⟨226355318127341732536272575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150903545418227821690848383 226355318127341732536272575)
  ·
    refine ⟨339532977191012598804408863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226355318127341732536272575 339532977191012598804408863)
    ·
      refine ⟨509299465786518898206613295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339532977191012598804408863 509299465786518898206613295)
      ·
        refine ⟨763949198679778347309919943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509299465786518898206613295 763949198679778347309919943)
        ·
          refine ⟨1145923798019667520964879915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 763949198679778347309919943 1145923798019667520964879915)
          ·
            refine ⟨1718885697029501281447319873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1145923798019667520964879915 1718885697029501281447319873)
            ·
              refine ⟨1289164272772125961085489905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1718885697029501281447319873 1289164272772125961085489905)
              ·
                refine ⟨966873204579094470814117429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1289164272772125961085489905 966873204579094470814117429)
                ·
                  refine ⟨90644362929290106638823509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 966873204579094470814117429 90644362929290106638823509)
                  ·
                    refine ⟨1062238628077618437173713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90644362929290106638823509 1062238628077618437173713)
                    ·
                      rfl

theorem cell23_6206107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 8].length) (baseStart_6206107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206107 prefixEnd_6206107 := by exact prefixLift 6206107
  have htrace : WordTrace (prefixWord ++ tailWord_6206107) baseStart_6206107 baseEnd_6206107 := by
    simpa [prefixWord, tailWord_6206107, baseEnd_6206107] using wordTrace_append hprefix tailTrace_6206107
  have hstable : (prefixWord ++ tailWord_6206107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206107).length < 2 ^ (prefixWord ++ tailWord_6206107).sum := by decide
  have hdescent : baseEnd_6206107 < baseStart_6206107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206131 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 3, 4, 2]
def baseStart_6206131 : Nat := 118140960795 + 6206131 * 2 ^ 59
def prefixEnd_6206131 : Nat := 4983230072969 + 3 ^ 40 * 6206131 * 2
def baseEnd_6206131 : Nat := 3186728207768563217621029

theorem tailTrace_6206131 : CollatzResearch.WordTrace tailWord_6206131 prefixEnd_6206131 3186728207768563217621029 := by
  unfold tailWord_6206131
  simp only [CollatzResearch.WordTrace]
  refine ⟨226356193479254784635146247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150904128986169856423430831 226356193479254784635146247)
  ·
    refine ⟨339534290218882176952719371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226356193479254784635146247 339534290218882176952719371)
    ·
      refine ⟨509301435328323265429079057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339534290218882176952719371 509301435328323265429079057)
      ·
        refine ⟨381976076496242449071809293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 509301435328323265429079057 381976076496242449071809293)
        ·
          refine ⟨143241028686090918401928485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 381976076496242449071809293 143241028686090918401928485)
          ·
            refine ⟨26857692878642047200361591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143241028686090918401928485 26857692878642047200361591)
            ·
              refine ⟨40286539317963070800542387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26857692878642047200361591 40286539317963070800542387)
              ·
                refine ⟨60429808976944606200813581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40286539317963070800542387 60429808976944606200813581)
                ·
                  refine ⟨22661178366354227325305093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60429808976944606200813581 22661178366354227325305093)
                  ·
                    refine ⟨4248970943691417623494705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22661178366354227325305093 4248970943691417623494705)
                    ·
                      refine ⟨3186728207768563217621029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4248970943691417623494705 3186728207768563217621029)
                      ·
                        rfl

theorem cell23_6206131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 3, 4, 2].length) (baseStart_6206131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206131 prefixEnd_6206131 := by exact prefixLift 6206131
  have htrace : WordTrace (prefixWord ++ tailWord_6206131) baseStart_6206131 baseEnd_6206131 := by
    simpa [prefixWord, tailWord_6206131, baseEnd_6206131] using wordTrace_append hprefix tailTrace_6206131
  have hstable : (prefixWord ++ tailWord_6206131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206131).length < 2 ^ (prefixWord ++ tailWord_6206131).sum := by decide
  have hdescent : baseEnd_6206131 < baseStart_6206131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206241 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 1, 4, 3]
def baseStart_6206241 : Nat := 118140960795 + 6206241 * 2 ^ 59
def prefixEnd_6206241 : Nat := 4983230072969 + 3 ^ 40 * 6206241 * 2
def baseEnd_6206241 : Nat := 3186784690640557787245523

theorem tailTrace_6206241 : CollatzResearch.WordTrace tailWord_6206241 prefixEnd_6206241 3186784690640557787245523 := by
  unfold tailWord_6206241
  simp only [CollatzResearch.WordTrace]
  refine ⟨226360205508856273421650577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150906803672570848947767051 226360205508856273421650577)
  ·
    refine ⟨169770154131642205066237933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226360205508856273421650577 169770154131642205066237933)
    ·
      refine ⟨63663807799365826899839225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169770154131642205066237933 63663807799365826899839225)
      ·
        refine ⟨47747855849524370174879419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63663807799365826899839225 47747855849524370174879419)
        ·
          refine ⟨71621783774286555262319129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47747855849524370174879419 71621783774286555262319129)
          ·
            refine ⟨53716337830714916446739347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71621783774286555262319129 53716337830714916446739347)
            ·
              refine ⟨80574506746072374670109021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53716337830714916446739347 80574506746072374670109021)
              ·
                refine ⟨30215440029777140501290883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80574506746072374670109021 30215440029777140501290883)
                ·
                  refine ⟨45323160044665710751936325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30215440029777140501290883 45323160044665710751936325)
                  ·
                    refine ⟨8498092508374820765988061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45323160044665710751936325 8498092508374820765988061)
                    ·
                      refine ⟨3186784690640557787245523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8498092508374820765988061 3186784690640557787245523)
                      ·
                        rfl

theorem cell23_6206241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_6206241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206241 prefixEnd_6206241 := by exact prefixLift 6206241
  have htrace : WordTrace (prefixWord ++ tailWord_6206241) baseStart_6206241 baseEnd_6206241 := by
    simpa [prefixWord, tailWord_6206241, baseEnd_6206241] using wordTrace_append hprefix tailTrace_6206241
  have hstable : (prefixWord ++ tailWord_6206241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206241).length < 2 ^ (prefixWord ++ tailWord_6206241).sum := by decide
  have hdescent : baseEnd_6206241 < baseStart_6206241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206258 : List Nat := [3, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3]
def baseStart_6206258 : Nat := 118140960795 + 6206258 * 2 ^ 59
def prefixEnd_6206258 : Nat := 4983230072969 + 3 ^ 40 * 6206258 * 2
def baseEnd_6206258 : Nat := 3186793419811684220732945

theorem tailTrace_6206258 : CollatzResearch.WordTrace tailWord_6206258 prefixEnd_6206258 3186793419811684220732945 := by
  unfold tailWord_6206258
  simp only [CollatzResearch.WordTrace]
  refine ⟨56590206387448671331254857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150907217033196456883346285 56590206387448671331254857)
  ·
    refine ⟨42442654790586503498441143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56590206387448671331254857 42442654790586503498441143)
    ·
      refine ⟨63663982185879755247661715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42442654790586503498441143 63663982185879755247661715)
      ·
        refine ⟨95495973278819632871492573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63663982185879755247661715 95495973278819632871492573)
        ·
          refine ⟨35810989979557362326809715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95495973278819632871492573 35810989979557362326809715)
          ·
            refine ⟨53716484969336043490214573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35810989979557362326809715 53716484969336043490214573)
            ·
              refine ⟨20143681863501016308830465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53716484969336043490214573 20143681863501016308830465)
              ·
                refine ⟨15107761397625762231622849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20143681863501016308830465 15107761397625762231622849)
                ·
                  refine ⟨11330821048219321673717137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15107761397625762231622849 11330821048219321673717137)
                  ·
                    refine ⟨8498115786164491255287853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11330821048219321673717137 8498115786164491255287853)
                    ·
                      refine ⟨3186793419811684220732945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8498115786164491255287853 3186793419811684220732945)
                      ·
                        rfl

theorem cell23_6206258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_6206258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206258 prefixEnd_6206258 := by exact prefixLift 6206258
  have htrace : WordTrace (prefixWord ++ tailWord_6206258) baseStart_6206258 baseEnd_6206258 := by
    simpa [prefixWord, tailWord_6206258, baseEnd_6206258] using wordTrace_append hprefix tailTrace_6206258
  have hstable : (prefixWord ++ tailWord_6206258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206258).length < 2 ^ (prefixWord ++ tailWord_6206258).sum := by decide
  have hdescent : baseEnd_6206258 < baseStart_6206258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206261 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 8]
def baseStart_6206261 : Nat := 118140960795 + 6206261 * 2 ^ 59
def prefixEnd_6206261 : Nat := 4983230072969 + 3 ^ 40 * 6206261 * 2
def baseEnd_6206261 : Nat := 354088328917071967666159

theorem tailTrace_6206261 : CollatzResearch.WordTrace tailWord_6206261 prefixEnd_6206261 354088328917071967666159 := by
  unfold tailWord_6206261
  simp only [CollatzResearch.WordTrace]
  refine ⟨226360934968783816837378637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150907289979189211224919091 226360934968783816837378637)
  ·
    refine ⟨84885350613293931314016989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226360934968783816837378637 84885350613293931314016989)
    ·
      refine ⟨31832006479985224242756371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84885350613293931314016989 31832006479985224242756371)
      ·
        refine ⟨47748009719977836364134557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31832006479985224242756371 47748009719977836364134557)
        ·
          refine ⟨17905503644991688636550459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47748009719977836364134557 17905503644991688636550459)
          ·
            refine ⟨26858255467487532954825689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17905503644991688636550459 26858255467487532954825689)
            ·
              refine ⟨20143691600615649716119267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26858255467487532954825689 20143691600615649716119267)
              ·
                refine ⟨30215537400923474574178901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20143691600615649716119267 30215537400923474574178901)
                ·
                  refine ⟨354088328917071967666159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30215537400923474574178901 354088328917071967666159)
                  ·
                    rfl

theorem cell23_6206261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 8].length) (baseStart_6206261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206261 prefixEnd_6206261 := by exact prefixLift 6206261
  have htrace : WordTrace (prefixWord ++ tailWord_6206261) baseStart_6206261 baseEnd_6206261 := by
    simpa [prefixWord, tailWord_6206261, baseEnd_6206261] using wordTrace_append hprefix tailTrace_6206261
  have hstable : (prefixWord ++ tailWord_6206261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206261).length < 2 ^ (prefixWord ++ tailWord_6206261).sum := by decide
  have hdescent : baseEnd_6206261 < baseStart_6206261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206288 : List Nat := [2, 1, 1, 1, 1, 4, 2, 4, 3, 1, 3]
def baseStart_6206288 : Nat := 118140960795 + 6206288 * 2 ^ 59
def prefixEnd_6206288 : Nat := 4983230072969 + 3 ^ 40 * 6206288 * 2
def baseEnd_6206288 : Nat := 3186808824231319103357807

theorem tailTrace_6206288 : CollatzResearch.WordTrace tailWord_6206288 prefixEnd_6206288 3186808824231319103357807 := by
  unfold tailWord_6206288
  simp only [CollatzResearch.WordTrace]
  refine ⟨113180959869843000224305759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150907946493124000299074345 113180959869843000224305759)
  ·
    refine ⟨169771439804764500336458639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113180959869843000224305759 169771439804764500336458639)
    ·
      refine ⟨254657159707146750504687959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169771439804764500336458639 254657159707146750504687959)
      ·
        refine ⟨381985739560720125757031939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254657159707146750504687959 381985739560720125757031939)
        ·
          refine ⟨572978609341080188635547909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381985739560720125757031939 572978609341080188635547909)
          ·
            refine ⟨107433489251452535369165233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 572978609341080188635547909 107433489251452535369165233)
            ·
              refine ⟨80575116938589401526873925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107433489251452535369165233 80575116938589401526873925)
              ·
                refine ⟨15107834425985512786288861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80575116938589401526873925 15107834425985512786288861)
                ·
                  refine ⟨5665437909744567294858323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15107834425985512786288861 5665437909744567294858323)
                  ·
                    refine ⟨8498156864616850942287485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5665437909744567294858323 8498156864616850942287485)
                    ·
                      refine ⟨3186808824231319103357807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8498156864616850942287485 3186808824231319103357807)
                      ·
                        rfl

theorem cell23_6206288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 3, 1, 3].length) (baseStart_6206288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206288 prefixEnd_6206288 := by exact prefixLift 6206288
  have htrace : WordTrace (prefixWord ++ tailWord_6206288) baseStart_6206288 baseEnd_6206288 := by
    simpa [prefixWord, tailWord_6206288, baseEnd_6206288] using wordTrace_append hprefix tailTrace_6206288
  have hstable : (prefixWord ++ tailWord_6206288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206288).length < 2 ^ (prefixWord ++ tailWord_6206288).sum := by decide
  have hdescent : baseEnd_6206288 < baseStart_6206288 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206331 : List Nat := [1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 5]
def baseStart_6206331 : Nat := 118140960795 + 6206331 * 2 ^ 59
def prefixEnd_6206331 : Nat := 4983230072969 + 3 ^ 40 * 6206331 * 2
def baseEnd_6206331 : Nat := 3186830903899462435120109

theorem tailTrace_6206331 : CollatzResearch.WordTrace tailWord_6206331 prefixEnd_6206331 3186830903899462435120109 := by
  unfold tailWord_6206331
  simp only [CollatzResearch.WordTrace]
  refine ⟨226363488078530218792426847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150908992052353479194951231 226363488078530218792426847)
  ·
    refine ⟨339545232117795328188640271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226363488078530218792426847 339545232117795328188640271)
    ·
      refine ⟨509317848176692992282960407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339545232117795328188640271 509317848176692992282960407)
      ·
        refine ⟨763976772265039488424440611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509317848176692992282960407 763976772265039488424440611)
        ·
          refine ⟨1145965158397559232636660917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 763976772265039488424440611 1145965158397559232636660917)
          ·
            refine ⟨107434233599771178059686961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1145965158397559232636660917 107434233599771178059686961)
            ·
              refine ⟨80575675199828383544765221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107434233599771178059686961 80575675199828383544765221)
              ·
                refine ⟨15107939099967821914643479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80575675199828383544765221 15107939099967821914643479)
                ·
                  refine ⟨22661908649951732871965219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15107939099967821914643479 22661908649951732871965219)
                  ·
                    refine ⟨33992862974927599307947829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22661908649951732871965219 33992862974927599307947829)
                    ·
                      refine ⟨3186830903899462435120109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33992862974927599307947829 3186830903899462435120109)
                      ·
                        rfl

theorem cell23_6206331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 5].length) (baseStart_6206331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206331 prefixEnd_6206331 := by exact prefixLift 6206331
  have htrace : WordTrace (prefixWord ++ tailWord_6206331) baseStart_6206331 baseEnd_6206331 := by
    simpa [prefixWord, tailWord_6206331, baseEnd_6206331] using wordTrace_append hprefix tailTrace_6206331
  have hstable : (prefixWord ++ tailWord_6206331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206331).length < 2 ^ (prefixWord ++ tailWord_6206331).sum := by decide
  have hdescent : baseEnd_6206331 < baseStart_6206331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206345 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 5, 2, 2]
def baseStart_6206345 : Nat := 118140960795 + 6206345 * 2 ^ 59
def prefixEnd_6206345 : Nat := 4983230072969 + 3 ^ 40 * 6206345 * 2
def baseEnd_6206345 : Nat := 3186838092628625380345045

theorem tailTrace_6206345 : CollatzResearch.WordTrace tailWord_6206345 prefixEnd_6206345 3186838092628625380345045 := by
  unfold tailWord_6206345
  simp only [CollatzResearch.WordTrace]
  refine ⟨226363998700479499183436489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150909332466986332788957659 226363998700479499183436489)
  ·
    refine ⟨169772999025359624387577367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226363998700479499183436489 169772999025359624387577367)
    ·
      refine ⟨254659498538039436581366051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169772999025359624387577367 254659498538039436581366051)
      ·
        refine ⟨381989247807059154872049077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254659498538039436581366051 381989247807059154872049077)
        ·
          refine ⟨35811491981911795769254601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 381989247807059154872049077 35811491981911795769254601)
          ·
            refine ⟨26858618986433846826940951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35811491981911795769254601 26858618986433846826940951)
            ·
              refine ⟨40287928479650770240411427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26858618986433846826940951 40287928479650770240411427)
              ·
                refine ⟨60431892719476155360617141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40287928479650770240411427 60431892719476155360617141)
                ·
                  refine ⟨5665489942450889565057857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60431892719476155360617141 5665489942450889565057857)
                  ·
                    refine ⟨4249117456838167173793393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5665489942450889565057857 4249117456838167173793393)
                    ·
                      refine ⟨3186838092628625380345045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4249117456838167173793393 3186838092628625380345045)
                      ·
                        rfl

theorem cell23_6206345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 5, 2, 2].length) (baseStart_6206345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206345 prefixEnd_6206345 := by exact prefixLift 6206345
  have htrace : WordTrace (prefixWord ++ tailWord_6206345) baseStart_6206345 baseEnd_6206345 := by
    simpa [prefixWord, tailWord_6206345, baseEnd_6206345] using wordTrace_append hprefix tailTrace_6206345
  have hstable : (prefixWord ++ tailWord_6206345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206345).length < 2 ^ (prefixWord ++ tailWord_6206345).sum := by decide
  have hdescent : baseEnd_6206345 < baseStart_6206345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206348 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 3, 2, 3]
def baseStart_6206348 : Nat := 118140960795 + 6206348 * 2 ^ 59
def prefixEnd_6206348 : Nat := 4983230072969 + 3 ^ 40 * 6206348 * 2
def baseEnd_6206348 : Nat := 3186839633070588868607531

theorem tailTrace_6206348 : CollatzResearch.WordTrace tailWord_6206348 prefixEnd_6206348 3186839633070588868607531 := by
  unfold tailWord_6206348
  simp only [CollatzResearch.WordTrace]
  refine ⟨113182054059734315347897849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150909405412979087130530465 113182054059734315347897849)
  ·
    refine ⟨84886540544800736510923387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113182054059734315347897849 84886540544800736510923387)
    ·
      refine ⟨127329810817201104766385081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84886540544800736510923387 127329810817201104766385081)
      ·
        refine ⟨95497358112900828574788811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127329810817201104766385081 95497358112900828574788811)
        ·
          refine ⟨143246037169351242862183217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95497358112900828574788811 143246037169351242862183217)
          ·
            refine ⟨107434527877013432146637413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143246037169351242862183217 107434527877013432146637413)
            ·
              refine ⟨20143973976940018527494515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107434527877013432146637413 20143973976940018527494515)
              ·
                refine ⟨30215960965410027791241773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20143973976940018527494515 30215960965410027791241773)
                ·
                  refine ⟨11330985362028760421715665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30215960965410027791241773 11330985362028760421715665)
                  ·
                    refine ⟨8498239021521570316286749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11330985362028760421715665 8498239021521570316286749)
                    ·
                      refine ⟨3186839633070588868607531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8498239021521570316286749 3186839633070588868607531)
                      ·
                        rfl

theorem cell23_6206348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_6206348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206348 prefixEnd_6206348 := by exact prefixLift 6206348
  have htrace : WordTrace (prefixWord ++ tailWord_6206348) baseStart_6206348 baseEnd_6206348 := by
    simpa [prefixWord, tailWord_6206348, baseEnd_6206348] using wordTrace_append hprefix tailTrace_6206348
  have hstable : (prefixWord ++ tailWord_6206348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206348).length < 2 ^ (prefixWord ++ tailWord_6206348).sum := by decide
  have hdescent : baseEnd_6206348 < baseStart_6206348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206365 : List Nat := [1, 4, 2, 1, 2, 1, 3, 3, 1, 2, 3]
def baseStart_6206365 : Nat := 118140960795 + 6206365 * 2 ^ 59
def prefixEnd_6206365 : Nat := 4983230072969 + 3 ^ 40 * 6206365 * 2
def baseEnd_6206365 : Nat := 3186848362241715302094953

theorem tailTrace_6206365 : CollatzResearch.WordTrace tailWord_6206365 prefixEnd_6206365 3186848362241715302094953 := by
  unfold tailWord_6206365
  simp only [CollatzResearch.WordTrace]
  refine ⟨226364728160407042599164549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150909818773604695066109699 226364728160407042599164549)
  ·
    refine ⟨42443386530076320487343353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226364728160407042599164549 42443386530076320487343353)
    ·
      refine ⟨31832539897557240365507515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42443386530076320487343353 31832539897557240365507515)
      ·
        refine ⟨47748809846335860548261273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31832539897557240365507515 47748809846335860548261273)
        ·
          refine ⟨35811607384751895411195955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47748809846335860548261273 35811607384751895411195955)
          ·
            refine ⟨53717411077127843116793933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35811607384751895411195955 53717411077127843116793933)
            ·
              refine ⟨20144029153922941168797725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53717411077127843116793933 20144029153922941168797725)
              ·
                refine ⟨7554010932721102938299147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20144029153922941168797725 7554010932721102938299147)
                ·
                  refine ⟨11331016399081654407448721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7554010932721102938299147 11331016399081654407448721)
                  ·
                    refine ⟨8498262299311240805586541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11331016399081654407448721 8498262299311240805586541)
                    ·
                      refine ⟨3186848362241715302094953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8498262299311240805586541 3186848362241715302094953)
                      ·
                        rfl

theorem cell23_6206365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_6206365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206365 prefixEnd_6206365 := by exact prefixLift 6206365
  have htrace : WordTrace (prefixWord ++ tailWord_6206365) baseStart_6206365 baseEnd_6206365 := by
    simpa [prefixWord, tailWord_6206365, baseEnd_6206365] using wordTrace_append hprefix tailTrace_6206365
  have hstable : (prefixWord ++ tailWord_6206365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206365).length < 2 ^ (prefixWord ++ tailWord_6206365).sum := by decide
  have hdescent : baseEnd_6206365 < baseStart_6206365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206446 : List Nat := [4, 1, 2, 1, 4, 2, 2, 1, 2, 1, 3]
def baseStart_6206446 : Nat := 118140960795 + 6206446 * 2 ^ 59
def prefixEnd_6206446 : Nat := 4983230072969 + 3 ^ 40 * 6206446 * 2
def baseEnd_6206446 : Nat := 3186889954174729485182081

theorem tailTrace_6206446 : CollatzResearch.WordTrace tailWord_6206446 prefixEnd_6206446 3186889954174729485182081 := by
  unfold tailWord_6206446
  simp only [CollatzResearch.WordTrace]
  refine ⟨28295960309139199179107899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150911788315409062288575461 28295960309139199179107899)
  ·
    refine ⟨42443940463708798768661849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28295960309139199179107899 42443940463708798768661849)
    ·
      refine ⟨31832955347781599076496387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42443940463708798768661849 31832955347781599076496387)
      ·
        refine ⟨47749433021672398614744581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31832955347781599076496387 47749433021672398614744581)
        ·
          refine ⟨8953018691563574740264609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47749433021672398614744581 8953018691563574740264609)
          ·
            refine ⟨6714764018672681055198457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8953018691563574740264609 6714764018672681055198457)
            ·
              refine ⟨5036073014004510791398843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6714764018672681055198457 5036073014004510791398843)
              ·
                refine ⟨7554109521006766187098265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5036073014004510791398843 7554109521006766187098265)
                ·
                  refine ⟨5665582140755074640323699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7554109521006766187098265 5665582140755074640323699)
                  ·
                    refine ⟨8498373211132611960485549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5665582140755074640323699 8498373211132611960485549)
                    ·
                      refine ⟨3186889954174729485182081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8498373211132611960485549 3186889954174729485182081)
                      ·
                        rfl

theorem cell23_6206446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_6206446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206446 prefixEnd_6206446 := by exact prefixLift 6206446
  have htrace : WordTrace (prefixWord ++ tailWord_6206446) baseStart_6206446 baseEnd_6206446 := by
    simpa [prefixWord, tailWord_6206446, baseEnd_6206446] using wordTrace_append hprefix tailTrace_6206446
  have hstable : (prefixWord ++ tailWord_6206446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206446).length < 2 ^ (prefixWord ++ tailWord_6206446).sum := by decide
  have hdescent : baseEnd_6206446 < baseStart_6206446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206492 : List Nat := [2, 2, 3, 1, 4, 1, 1, 4, 5]
def baseStart_6206492 : Nat := 118140960795 + 6206492 * 2 ^ 59
def prefixEnd_6206492 : Nat := 4983230072969 + 3 ^ 40 * 6206492 * 2
def baseEnd_6206492 : Nat := 354101508253870700578541

theorem tailTrace_6206492 : CollatzResearch.WordTrace tailWord_6206492 prefixEnd_6206492 354101508253870700578541 := by
  unfold tailWord_6206492
  simp only [CollatzResearch.WordTrace]
  refine ⟨113184680115473471644518865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150912906820631295526025153 113184680115473471644518865)
  ·
    refine ⟨84888510086605103733389149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113184680115473471644518865 84888510086605103733389149)
    ·
      refine ⟨31833191282476913900020931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84888510086605103733389149 31833191282476913900020931)
      ·
        refine ⟨47749786923715370850031397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31833191282476913900020931 47749786923715370850031397)
        ·
          refine ⟨8953085048196632034380887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47749786923715370850031397 8953085048196632034380887)
          ·
            refine ⟨13429627572294948051571331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8953085048196632034380887 13429627572294948051571331)
            ·
              refine ⟨20144441358442422077356997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13429627572294948051571331 20144441358442422077356997)
              ·
                refine ⟨3777082754707954139504437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20144441358442422077356997 3777082754707954139504437)
                ·
                  refine ⟨354101508253870700578541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3777082754707954139504437 354101508253870700578541)
                  ·
                    rfl

theorem cell23_6206492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 5].length) (baseStart_6206492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206492 prefixEnd_6206492 := by exact prefixLift 6206492
  have htrace : WordTrace (prefixWord ++ tailWord_6206492) baseStart_6206492 baseEnd_6206492 := by
    simpa [prefixWord, tailWord_6206492, baseEnd_6206492] using wordTrace_append hprefix tailTrace_6206492
  have hstable : (prefixWord ++ tailWord_6206492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206492).length < 2 ^ (prefixWord ++ tailWord_6206492).sum := by decide
  have hdescent : baseEnd_6206492 < baseStart_6206492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206495 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 2, 5, 2]
def baseStart_6206495 : Nat := 118140960795 + 6206495 * 2 ^ 59
def prefixEnd_6206495 : Nat := 4983230072969 + 3 ^ 40 * 6206495 * 2
def baseEnd_6206495 : Nat := 3186915114726799793469355

theorem tailTrace_6206495 : CollatzResearch.WordTrace tailWord_6206495 prefixEnd_6206495 3186915114726799793469355 := by
  unfold tailWord_6206495
  simp only [CollatzResearch.WordTrace]
  refine ⟨226369469649936074801396939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150912979766624049867597959 226369469649936074801396939)
  ·
    refine ⟨339554204474904112202095409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226369469649936074801396939 339554204474904112202095409)
    ·
      refine ⟨254665653356178084151571557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339554204474904112202095409 254665653356178084151571557)
      ·
        refine ⟨47749810004283390778419667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254665653356178084151571557 47749810004283390778419667)
        ·
          refine ⟨71624715006425086167629501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47749810004283390778419667 71624715006425086167629501)
          ·
            refine ⟨26859268127409407312861063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71624715006425086167629501 26859268127409407312861063)
            ·
              refine ⟨40288902191114110969291595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26859268127409407312861063 40288902191114110969291595)
              ·
                refine ⟨60433353286671166453937393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40288902191114110969291595 60433353286671166453937393)
                ·
                  refine ⟨45325014965003374840453045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60433353286671166453937393 45325014965003374840453045)
                  ·
                    refine ⟨4249220152969066391292473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45325014965003374840453045 4249220152969066391292473)
                    ·
                      refine ⟨3186915114726799793469355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4249220152969066391292473 3186915114726799793469355)
                      ·
                        rfl

theorem cell23_6206495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_6206495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206495 prefixEnd_6206495 := by exact prefixLift 6206495
  have htrace : WordTrace (prefixWord ++ tailWord_6206495) baseStart_6206495 baseEnd_6206495 := by
    simpa [prefixWord, tailWord_6206495, baseEnd_6206495] using wordTrace_append hprefix tailTrace_6206495
  have hstable : (prefixWord ++ tailWord_6206495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206495).length < 2 ^ (prefixWord ++ tailWord_6206495).sum := by decide
  have hdescent : baseEnd_6206495 < baseStart_6206495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206508 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 4]
def baseStart_6206508 : Nat := 118140960795 + 6206508 * 2 ^ 59
def prefixEnd_6206508 : Nat := 4983230072969 + 3 ^ 40 * 6206508 * 2
def baseEnd_6206508 : Nat := 3186921789975308242606795

theorem tailTrace_6206508 : CollatzResearch.WordTrace tailWord_6206508 prefixEnd_6206508 3186921789975308242606795 := by
  unfold tailWord_6206508
  simp only [CollatzResearch.WordTrace]
  refine ⟨113184971899444489010810089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150913295865925985347746785 113184971899444489010810089)
  ·
    refine ⟨84888728924583366758107567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113184971899444489010810089 84888728924583366758107567)
    ·
      refine ⟨127333093386875050137161351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84888728924583366758107567 127333093386875050137161351)
      ·
        refine ⟨190999640080312575205742027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127333093386875050137161351 190999640080312575205742027)
        ·
          refine ⟨286499460120468862808613041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 190999640080312575205742027 286499460120468862808613041)
          ·
            refine ⟨214874595090351647106459781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286499460120468862808613041 214874595090351647106459781)
            ·
              refine ⟨40288986579440933832461209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 214874595090351647106459781 40288986579440933832461209)
              ·
                refine ⟨30216739934580700374345907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40288986579440933832461209 30216739934580700374345907)
                ·
                  refine ⟨45325109901871050561518861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30216739934580700374345907 45325109901871050561518861)
                  ·
                    refine ⟨16996916213201643960569573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45325109901871050561518861 16996916213201643960569573)
                    ·
                      refine ⟨3186921789975308242606795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16996916213201643960569573 3186921789975308242606795)
                      ·
                        rfl

theorem cell23_6206508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_6206508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206508 prefixEnd_6206508 := by exact prefixLift 6206508
  have htrace : WordTrace (prefixWord ++ tailWord_6206508) baseStart_6206508 baseEnd_6206508 := by
    simpa [prefixWord, tailWord_6206508, baseEnd_6206508] using wordTrace_append hprefix tailTrace_6206508
  have hstable : (prefixWord ++ tailWord_6206508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206508).length < 2 ^ (prefixWord ++ tailWord_6206508).sum := by decide
  have hdescent : baseEnd_6206508 < baseStart_6206508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206525 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 1, 3, 4]
def baseStart_6206525 : Nat := 118140960795 + 6206525 * 2 ^ 59
def prefixEnd_6206525 : Nat := 4983230072969 + 3 ^ 40 * 6206525 * 2
def baseEnd_6206525 : Nat := 3186930519146434676094217

theorem tailTrace_6206525 : CollatzResearch.WordTrace tailWord_6206525 prefixEnd_6206525 3186930519146434676094217 := by
  unfold tailWord_6206525
  simp only [CollatzResearch.WordTrace]
  refine ⟨226370563839827389924989029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150913709226551593283326019 226370563839827389924989029)
  ·
    refine ⟨42444480719967635610935443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226370563839827389924989029 42444480719967635610935443)
    ·
      refine ⟨63666721079951453416403165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42444480719967635610935443 63666721079951453416403165)
      ·
        refine ⟨23875020404981795031151187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63666721079951453416403165 23875020404981795031151187)
        ·
          refine ⟨35812530607472692546726781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23875020404981795031151187 35812530607472692546726781)
          ·
            refine ⟨13429698977802259705022543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35812530607472692546726781 13429698977802259705022543)
            ·
              refine ⟨20144548466703389557533815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13429698977802259705022543 20144548466703389557533815)
              ·
                refine ⟨30216822700055084336300723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20144548466703389557533815 30216822700055084336300723)
                ·
                  refine ⟨45325234050082626504451085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30216822700055084336300723 45325234050082626504451085)
                  ·
                    refine ⟨16996962768780984939169157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45325234050082626504451085 16996962768780984939169157)
                    ·
                      refine ⟨3186930519146434676094217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16996962768780984939169157 3186930519146434676094217)
                      ·
                        rfl

theorem cell23_6206525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_6206525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206525 prefixEnd_6206525 := by exact prefixLift 6206525
  have htrace : WordTrace (prefixWord ++ tailWord_6206525) baseStart_6206525 baseEnd_6206525 := by
    simpa [prefixWord, tailWord_6206525, baseEnd_6206525] using wordTrace_append hprefix tailTrace_6206525
  have hstable : (prefixWord ++ tailWord_6206525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206525).length < 2 ^ (prefixWord ++ tailWord_6206525).sum := by decide
  have hdescent : baseEnd_6206525 < baseStart_6206525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206538 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_6206538 : Nat := 118140960795 + 6206538 * 2 ^ 59
def prefixEnd_6206538 : Nat := 4983230072969 + 3 ^ 40 * 6206538 * 2
def baseEnd_6206538 : Nat := 3186937194394943125231657

theorem tailTrace_6206538 : CollatzResearch.WordTrace tailWord_6206538 prefixEnd_6206538 3186937194394943125231657 := by
  unfold tailWord_6206538
  simp only [CollatzResearch.WordTrace]
  refine ⟨56592759497195073286303067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150914025325853528763474845 56592759497195073286303067)
  ·
    refine ⟨84889139245792609929454601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56592759497195073286303067 84889139245792609929454601)
    ·
      refine ⟨63666854434344457447090951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84889139245792609929454601 63666854434344457447090951)
      ·
        refine ⟨95500281651516686170636427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63666854434344457447090951 95500281651516686170636427)
        ·
          refine ⟨143250422477275029255954641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95500281651516686170636427 143250422477275029255954641)
          ·
            refine ⟨107437816857956271941965981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143250422477275029255954641 107437816857956271941965981)
            ·
              refine ⟨40289181321733601978237243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107437816857956271941965981 40289181321733601978237243)
              ·
                refine ⟨60433771982600402967355865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40289181321733601978237243 60433771982600402967355865)
                ·
                  refine ⟨45325328986950302225516899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60433771982600402967355865 45325328986950302225516899)
                  ·
                    refine ⟨67987993480425453338275349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45325328986950302225516899 67987993480425453338275349)
                    ·
                      refine ⟨3186937194394943125231657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67987993480425453338275349 3186937194394943125231657)
                      ·
                        rfl

theorem cell23_6206538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_6206538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206538 prefixEnd_6206538 := by exact prefixLift 6206538
  have htrace : WordTrace (prefixWord ++ tailWord_6206538) baseStart_6206538 baseEnd_6206538 := by
    simpa [prefixWord, tailWord_6206538, baseEnd_6206538] using wordTrace_append hprefix tailTrace_6206538
  have hstable : (prefixWord ++ tailWord_6206538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206538).length < 2 ^ (prefixWord ++ tailWord_6206538).sum := by decide
  have hdescent : baseEnd_6206538 < baseStart_6206538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206545 : List Nat := [1, 2, 2, 1, 3, 1, 2, 4, 2, 2, 3]
def baseStart_6206545 : Nat := 118140960795 + 6206545 * 2 ^ 59
def prefixEnd_6206545 : Nat := 4983230072969 + 3 ^ 40 * 6206545 * 2
def baseEnd_6206545 : Nat := 3186940788759524597844125

theorem tailTrace_6206545 : CollatzResearch.WordTrace tailWord_6206545 prefixEnd_6206545 3186940788759524597844125 := by
  unfold tailWord_6206545
  simp only [CollatzResearch.WordTrace]
  refine ⟨226371293299754933340717089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150914195533169955560478059 226371293299754933340717089)
  ·
    refine ⟨169778469974816200005537817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226371293299754933340717089 169778469974816200005537817)
    ·
      refine ⟨127333852481112150004153363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169778469974816200005537817 127333852481112150004153363)
      ·
        refine ⟨191000778721668225006230045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127333852481112150004153363 191000778721668225006230045)
        ·
          refine ⟨71625292020625584377336267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191000778721668225006230045 71625292020625584377336267)
          ·
            refine ⟨107437938030938376566004401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71625292020625584377336267 107437938030938376566004401)
            ·
              refine ⟨80578453523203782424503301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107437938030938376566004401 80578453523203782424503301)
              ·
                refine ⟨15108460035600709204594369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80578453523203782424503301 15108460035600709204594369)
                ·
                  refine ⟨11331345026700531903445777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15108460035600709204594369 11331345026700531903445777)
                  ·
                    refine ⟨8498508770025398927584333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11331345026700531903445777 8498508770025398927584333)
                    ·
                      refine ⟨3186940788759524597844125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8498508770025398927584333 3186940788759524597844125)
                      ·
                        rfl

theorem cell23_6206545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_6206545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206545 prefixEnd_6206545 := by exact prefixLift 6206545
  have htrace : WordTrace (prefixWord ++ tailWord_6206545) baseStart_6206545 baseEnd_6206545 := by
    simpa [prefixWord, tailWord_6206545, baseEnd_6206545] using wordTrace_append hprefix tailTrace_6206545
  have hstable : (prefixWord ++ tailWord_6206545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206545).length < 2 ^ (prefixWord ++ tailWord_6206545).sum := by decide
  have hdescent : baseEnd_6206545 < baseStart_6206545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206552 : List Nat := [2, 1, 2, 2, 1, 3, 1, 6, 1, 4]
def baseStart_6206552 : Nat := 118140960795 + 6206552 * 2 ^ 59
def prefixEnd_6206552 : Nat := 4983230072969 + 3 ^ 40 * 6206552 * 2
def baseEnd_6206552 : Nat := 1062314794374702023485531

theorem tailTrace_6206552 : CollatzResearch.WordTrace tailWord_6206552 prefixEnd_6206552 1062314794374702023485531 := by
  unfold tailWord_6206552
  simp only [CollatzResearch.WordTrace]
  refine ⟨113185774305364786768110955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150914365740486382357481273 113185774305364786768110955)
  ·
    refine ⟨169778661458047180152166433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113185774305364786768110955 169778661458047180152166433)
    ·
      refine ⟨127333996093535385114124825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169778661458047180152166433 127333996093535385114124825)
      ·
        refine ⟨95500497070151538835593619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127333996093535385114124825 95500497070151538835593619)
        ·
          refine ⟨143250745605227308253390429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95500497070151538835593619 143250745605227308253390429)
          ·
            refine ⟨53719029601960240595021411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143250745605227308253390429 53719029601960240595021411)
            ·
              refine ⟨80578544402940360892532117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53719029601960240595021411 80578544402940360892532117)
              ·
                refine ⟨3777119268887829416837443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 80578544402940360892532117 3777119268887829416837443)
                ·
                  refine ⟨5665678903331744125256165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3777119268887829416837443 5665678903331744125256165)
                  ·
                    refine ⟨1062314794374702023485531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5665678903331744125256165 1062314794374702023485531)
                    ·
                      rfl

theorem cell23_6206552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 1, 4].length) (baseStart_6206552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206552 prefixEnd_6206552 := by exact prefixLift 6206552
  have htrace : WordTrace (prefixWord ++ tailWord_6206552) baseStart_6206552 baseEnd_6206552 := by
    simpa [prefixWord, tailWord_6206552, baseEnd_6206552] using wordTrace_append hprefix tailTrace_6206552
  have hstable : (prefixWord ++ tailWord_6206552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206552).length < 2 ^ (prefixWord ++ tailWord_6206552).sum := by decide
  have hdescent : baseEnd_6206552 < baseStart_6206552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206562 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_6206562 : Nat := 118140960795 + 6206562 * 2 ^ 59
def prefixEnd_6206562 : Nat := 4983230072969 + 3 ^ 40 * 6206562 * 2
def baseEnd_6206562 : Nat := 3186949517930651031331547

theorem tailTrace_6206562 : CollatzResearch.WordTrace tailWord_6206562 prefixEnd_6206562 3186949517930651031331547 := by
  unfold tailWord_6206562
  simp only [CollatzResearch.WordTrace]
  refine ⟨56592978335173336311021485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150914608893795563496057293 56592978335173336311021485)
  ·
    refine ⟨21222366875690001116633057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56592978335173336311021485 21222366875690001116633057)
    ·
      refine ⟨15916775156767500837474793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21222366875690001116633057 15916775156767500837474793)
      ·
        refine ⟨11937581367575625628106095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15916775156767500837474793 11937581367575625628106095)
        ·
          refine ⟨17906372051363438442159143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11937581367575625628106095 17906372051363438442159143)
          ·
            refine ⟨26859558077045157663238715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17906372051363438442159143 26859558077045157663238715)
            ·
              refine ⟨40289337115567736494858073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26859558077045157663238715 40289337115567736494858073)
              ·
                refine ⟨30217002836675802371143555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40289337115567736494858073 30217002836675802371143555)
                ·
                  refine ⟨45325504255013703556715333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30217002836675802371143555 45325504255013703556715333)
                  ·
                    refine ⟨8498532047815069416884125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45325504255013703556715333 8498532047815069416884125)
                    ·
                      refine ⟨3186949517930651031331547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8498532047815069416884125 3186949517930651031331547)
                      ·
                        rfl

theorem cell23_6206562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_6206562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206562 prefixEnd_6206562 := by exact prefixLift 6206562
  have htrace : WordTrace (prefixWord ++ tailWord_6206562) baseStart_6206562 baseEnd_6206562 := by
    simpa [prefixWord, tailWord_6206562, baseEnd_6206562] using wordTrace_append hprefix tailTrace_6206562
  have hstable : (prefixWord ++ tailWord_6206562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206562).length < 2 ^ (prefixWord ++ tailWord_6206562).sum := by decide
  have hdescent : baseEnd_6206562 < baseStart_6206562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206595 : List Nat := [1, 1, 1, 3, 3, 2, 1, 5, 1, 5]
def baseStart_6206595 : Nat := 118140960795 + 6206595 * 2 ^ 59
def prefixEnd_6206595 : Nat := 4983230072969 + 3 ^ 40 * 6206595 * 2
def baseEnd_6206595 : Nat := 1062322154264083134072965

theorem tailTrace_6206595 : CollatzResearch.WordTrace tailWord_6206595 prefixEnd_6206595 1062322154264083134072965 := by
  unfold tailWord_6206595
  simp only [CollatzResearch.WordTrace]
  refine ⟨226373116949573791880037239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150915411299715861253358159 226373116949573791880037239)
  ·
    refine ⟨339559675424360687820055859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226373116949573791880037239 339559675424360687820055859)
    ·
      refine ⟨509339513136541031730083789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339559675424360687820055859 509339513136541031730083789)
      ·
        refine ⟨191002317426202886898781421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 509339513136541031730083789 191002317426202886898781421)
        ·
          refine ⟨71625869034826082587043033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191002317426202886898781421 71625869034826082587043033)
          ·
            refine ⟨53719401776119561940282275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71625869034826082587043033 53719401776119561940282275)
            ·
              refine ⟨80579102664179342910423413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53719401776119561940282275 80579102664179342910423413)
              ·
                refine ⟨7554290874766813397852195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 80579102664179342910423413 7554290874766813397852195)
                ·
                  refine ⟨11331436312150220096778293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7554290874766813397852195 11331436312150220096778293)
                  ·
                    refine ⟨1062322154264083134072965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11331436312150220096778293 1062322154264083134072965)
                    ·
                      rfl

theorem cell23_6206595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 5].length) (baseStart_6206595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206595 prefixEnd_6206595 := by exact prefixLift 6206595
  have htrace : WordTrace (prefixWord ++ tailWord_6206595) baseStart_6206595 baseEnd_6206595 := by
    simpa [prefixWord, tailWord_6206595, baseEnd_6206595] using wordTrace_append hprefix tailTrace_6206595
  have hstable : (prefixWord ++ tailWord_6206595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206595).length < 2 ^ (prefixWord ++ tailWord_6206595).sum := by decide
  have hdescent : baseEnd_6206595 < baseStart_6206595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206608 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 5, 6]
def baseStart_6206608 : Nat := 118140960795 + 6206608 * 2 ^ 59
def prefixEnd_6206608 : Nat := 4983230072969 + 3 ^ 40 * 6206608 * 2
def baseEnd_6206608 : Nat := 1062324379346919283785445

theorem tailTrace_6206608 : CollatzResearch.WordTrace tailWord_6206608 prefixEnd_6206608 1062324379346919283785445 := by
  unfold tailWord_6206608
  simp only [CollatzResearch.WordTrace]
  refine ⟨113186795549263347550130239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150915727399017796733506985 113186795549263347550130239)
  ·
    refine ⟨169780193323895021325195359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113186795549263347550130239 169780193323895021325195359)
    ·
      refine ⟨254670289985842531987793039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169780193323895021325195359 254670289985842531987793039)
      ·
        refine ⟨382005434978763797981689559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254670289985842531987793039 382005434978763797981689559)
        ·
          refine ⟨573008152468145696972534339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382005434978763797981689559 573008152468145696972534339)
          ·
            refine ⟨859512228702218545458801509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573008152468145696972534339 859512228702218545458801509)
            ·
              refine ⟨161158542881665977273525283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 859512228702218545458801509 161158542881665977273525283)
              ·
                refine ⟨241737814322498965910287925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161158542881665977273525283 241737814322498965910287925)
                ·
                  refine ⟨22662920092734278054089493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 241737814322498965910287925 22662920092734278054089493)
                  ·
                    refine ⟨1062324379346919283785445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22662920092734278054089493 1062324379346919283785445)
                    ·
                      rfl

theorem cell23_6206608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 5, 6].length) (baseStart_6206608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206608 prefixEnd_6206608 := by exact prefixLift 6206608
  have htrace : WordTrace (prefixWord ++ tailWord_6206608) baseStart_6206608 baseEnd_6206608 := by
    simpa [prefixWord, tailWord_6206608, baseEnd_6206608] using wordTrace_append hprefix tailTrace_6206608
  have hstable : (prefixWord ++ tailWord_6206608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206608).length < 2 ^ (prefixWord ++ tailWord_6206608).sum := by decide
  have hdescent : baseEnd_6206608 < baseStart_6206608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206625 : List Nat := [1, 2, 3, 3, 1, 1, 2, 3, 1, 6]
def baseStart_6206625 : Nat := 118140960795 + 6206625 * 2 ^ 59
def prefixEnd_6206625 : Nat := 4983230072969 + 3 ^ 40 * 6206625 * 2
def baseEnd_6206625 : Nat := 1062327289070628094947919

theorem tailTrace_6206625 : CollatzResearch.WordTrace tailWord_6206625 prefixEnd_6206625 1062327289070628094947919 := by
  unfold tailWord_6206625
  simp only [CollatzResearch.WordTrace]
  refine ⟨226374211139465107003629329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150916140759643404669086219 226374211139465107003629329)
  ·
    refine ⟨169780658354598830252721997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226374211139465107003629329 169780658354598830252721997)
    ·
      refine ⟨63667746882974561344770749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169780658354598830252721997 63667746882974561344770749)
      ·
        refine ⟨23875405081115460504289031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63667746882974561344770749 23875405081115460504289031)
        ·
          refine ⟨35813107621673190756433547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23875405081115460504289031 35813107621673190756433547)
          ·
            refine ⟨53719661432509786134650321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35813107621673190756433547 53719661432509786134650321)
            ·
              refine ⟨40289746074382339600987741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53719661432509786134650321 40289746074382339600987741)
              ·
                refine ⟨15108654777893377350370403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40289746074382339600987741 15108654777893377350370403)
                ·
                  refine ⟨22662982166840066025555605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15108654777893377350370403 22662982166840066025555605)
                  ·
                    refine ⟨1062327289070628094947919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22662982166840066025555605 1062327289070628094947919)
                    ·
                      rfl

theorem cell23_6206625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_6206625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206625 prefixEnd_6206625 := by exact prefixLift 6206625
  have htrace : WordTrace (prefixWord ++ tailWord_6206625) baseStart_6206625 baseEnd_6206625 := by
    simpa [prefixWord, tailWord_6206625, baseEnd_6206625] using wordTrace_append hprefix tailTrace_6206625
  have hstable : (prefixWord ++ tailWord_6206625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206625).length < 2 ^ (prefixWord ++ tailWord_6206625).sum := by decide
  have hdescent : baseEnd_6206625 < baseStart_6206625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206649 : List Nat := [1, 2, 1, 4, 1, 4, 3, 1, 1, 1, 4]
def baseStart_6206649 : Nat := 118140960795 + 6206649 * 2 ^ 59
def prefixEnd_6206649 : Nat := 4983230072969 + 3 ^ 40 * 6206649 * 2
def baseEnd_6206649 : Nat := 3186994190747592190943647

theorem tailTrace_6206649 : CollatzResearch.WordTrace tailWord_6206649 prefixEnd_6206649 3186994190747592190943647 := by
  unfold tailWord_6206649
  simp only [CollatzResearch.WordTrace]
  refine ⟨226375086491378159102503001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150916724327585439401668667 226375086491378159102503001)
  ·
    refine ⟨169781314868533619326877251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226375086491378159102503001 169781314868533619326877251)
    ·
      refine ⟨254671972302800428990315877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169781314868533619326877251 254671972302800428990315877)
      ·
        refine ⟨47750994806775080435684227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254671972302800428990315877 47750994806775080435684227)
        ·
          refine ⟨71626492210162620653526341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47750994806775080435684227 71626492210162620653526341)
          ·
            refine ⟨13429967289405491372536189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71626492210162620653526341 13429967289405491372536189)
            ·
              refine ⟨5036237733527059264701071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13429967289405491372536189 5036237733527059264701071)
              ·
                refine ⟨7554356600290588897051607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5036237733527059264701071 7554356600290588897051607)
                ·
                  refine ⟨11331534900435883345577411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7554356600290588897051607 11331534900435883345577411)
                  ·
                    refine ⟨16997302350653825018366117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11331534900435883345577411 16997302350653825018366117)
                    ·
                      refine ⟨3186994190747592190943647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16997302350653825018366117 3186994190747592190943647)
                      ·
                        rfl

theorem cell23_6206649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_6206649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206649 prefixEnd_6206649 := by exact prefixLift 6206649
  have htrace : WordTrace (prefixWord ++ tailWord_6206649) baseStart_6206649 baseEnd_6206649 := by
    simpa [prefixWord, tailWord_6206649, baseEnd_6206649] using wordTrace_append hprefix tailTrace_6206649
  have hstable : (prefixWord ++ tailWord_6206649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206649).length < 2 ^ (prefixWord ++ tailWord_6206649).sum := by decide
  have hdescent : baseEnd_6206649 < baseStart_6206649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206652 : List Nat := [2, 2, 2, 3, 2, 1, 3, 1, 1, 1, 5]
def baseStart_6206652 : Nat := 118140960795 + 6206652 * 2 ^ 59
def prefixEnd_6206652 : Nat := 4983230072969 + 3 ^ 40 * 6206652 * 2
def baseEnd_6206652 : Nat := 3186995731189555679206133

theorem tailTrace_6206652 : CollatzResearch.WordTrace tailWord_6206652 prefixEnd_6206652 3186995731189555679206133 := by
  unfold tailWord_6206652
  simp only [CollatzResearch.WordTrace]
  refine ⟨113187597955183645307431105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150916797273578193743241473 113187597955183645307431105)
  ·
    refine ⟨84890698466387733980573329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113187597955183645307431105 84890698466387733980573329)
    ·
      refine ⟨63668023849790800485429997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84890698466387733980573329 63668023849790800485429997)
      ·
        refine ⟨23875508943671550182036249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63668023849790800485429997 23875508943671550182036249)
        ·
          refine ⟨17906631707753662636527187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23875508943671550182036249 17906631707753662636527187)
          ·
            refine ⟨26859947561630493954790781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17906631707753662636527187 26859947561630493954790781)
            ·
              refine ⟨10072480335611435233046543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26859947561630493954790781 10072480335611435233046543)
              ·
                refine ⟨15108720503417152849569815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10072480335611435233046543 15108720503417152849569815)
                ·
                  refine ⟨22663080755125729274354723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15108720503417152849569815 22663080755125729274354723)
                  ·
                    refine ⟨33994621132688593911532085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22663080755125729274354723 33994621132688593911532085)
                    ·
                      refine ⟨3186995731189555679206133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33994621132688593911532085 3186995731189555679206133)
                      ·
                        rfl

theorem cell23_6206652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_6206652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206652 prefixEnd_6206652 := by exact prefixLift 6206652
  have htrace : WordTrace (prefixWord ++ tailWord_6206652) baseStart_6206652 baseEnd_6206652 := by
    simpa [prefixWord, tailWord_6206652, baseEnd_6206652] using wordTrace_append hprefix tailTrace_6206652
  have hstable : (prefixWord ++ tailWord_6206652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206652).length < 2 ^ (prefixWord ++ tailWord_6206652).sum := by decide
  have hdescent : baseEnd_6206652 < baseStart_6206652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206660 : List Nat := [2, 3, 3, 1, 3, 2, 2, 2, 1, 1, 3]
def baseStart_6206660 : Nat := 118140960795 + 6206660 * 2 ^ 59
def prefixEnd_6206660 : Nat := 4983230072969 + 3 ^ 40 * 6206660 * 2
def baseEnd_6206660 : Nat := 3186999839034791647906097

theorem tailTrace_6206660 : CollatzResearch.WordTrace tailWord_6206660 prefixEnd_6206660 3186999839034791647906097 := by
  unfold tailWord_6206660
  simp only [CollatzResearch.WordTrace]
  refine ⟨113187743847169153990576717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150916991796225538654102289 113187743847169153990576717)
  ·
    refine ⟨42445403942688432746466269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113187743847169153990576717 42445403942688432746466269)
    ·
      refine ⟨15917026478508162279924851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42445403942688432746466269 15917026478508162279924851)
      ·
        refine ⟨23875539717762243419887277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15917026478508162279924851 23875539717762243419887277)
        ·
          refine ⟨8953327394160841282457729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23875539717762243419887277 8953327394160841282457729)
          ·
            refine ⟨6714995545620630961843297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8953327394160841282457729 6714995545620630961843297)
            ·
              refine ⟨5036246659215473221382473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6714995545620630961843297 5036246659215473221382473)
              ·
                refine ⟨3777184994411604916036855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5036246659215473221382473 3777184994411604916036855)
                ·
                  refine ⟨5665777491617407374055283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3777184994411604916036855 5665777491617407374055283)
                  ·
                    refine ⟨8498666237426111061082925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5665777491617407374055283 8498666237426111061082925)
                    ·
                      refine ⟨3186999839034791647906097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8498666237426111061082925 3186999839034791647906097)
                      ·
                        rfl

theorem cell23_6206660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_6206660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206660 prefixEnd_6206660 := by exact prefixLift 6206660
  have htrace : WordTrace (prefixWord ++ tailWord_6206660) baseStart_6206660 baseEnd_6206660 := by
    simpa [prefixWord, tailWord_6206660, baseEnd_6206660] using wordTrace_append hprefix tailTrace_6206660
  have hstable : (prefixWord ++ tailWord_6206660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206660).length < 2 ^ (prefixWord ++ tailWord_6206660).sum := by decide
  have hdescent : baseEnd_6206660 < baseStart_6206660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206682 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3]
def baseStart_6206682 : Nat := 118140960795 + 6206682 * 2 ^ 59
def prefixEnd_6206682 : Nat := 4983230072969 + 3 ^ 40 * 6206682 * 2
def baseEnd_6206682 : Nat := 3187011135609190561830995

theorem tailTrace_6206682 : CollatzResearch.WordTrace tailWord_6206682 prefixEnd_6206682 3187011135609190561830995 := by
  unfold tailWord_6206682
  simp only [CollatzResearch.WordTrace]
  refine ⟨56594072525064651434613575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150917526733505737158969533 56594072525064651434613575)
  ·
    refine ⟨84891108787596977151920363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56594072525064651434613575 84891108787596977151920363)
    ·
      refine ⟨127336663181395465727880545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84891108787596977151920363 127336663181395465727880545)
      ·
        refine ⟨95502497386046599295910409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127336663181395465727880545 95502497386046599295910409)
        ·
          refine ⟨71626873039534949471932807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95502497386046599295910409 71626873039534949471932807)
          ·
            refine ⟨107440309559302424207899211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71626873039534949471932807 107440309559302424207899211)
            ·
              refine ⟨161160464338953636311848817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107440309559302424207899211 161160464338953636311848817)
              ·
                refine ⟨120870348254215227233886613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161160464338953636311848817 120870348254215227233886613)
                ·
                  refine ⟨5665797574416338776588435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120870348254215227233886613 5665797574416338776588435)
                  ·
                    refine ⟨8498696361624508164882653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5665797574416338776588435 8498696361624508164882653)
                    ·
                      refine ⟨3187011135609190561830995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8498696361624508164882653 3187011135609190561830995)
                      ·
                        rfl

theorem cell23_6206682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_6206682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206682 prefixEnd_6206682 := by exact prefixLift 6206682
  have htrace : WordTrace (prefixWord ++ tailWord_6206682) baseStart_6206682 baseEnd_6206682 := by
    simpa [prefixWord, tailWord_6206682, baseEnd_6206682] using wordTrace_append hprefix tailTrace_6206682
  have hstable : (prefixWord ++ tailWord_6206682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206682).length < 2 ^ (prefixWord ++ tailWord_6206682).sum := by decide
  have hdescent : baseEnd_6206682 < baseStart_6206682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206703 : List Nat := [1, 1, 2, 1, 8, 1, 2, 1, 1, 2, 3]
def baseStart_6206703 : Nat := 118140960795 + 6206703 * 2 ^ 59
def prefixEnd_6206703 : Nat := 4983230072969 + 3 ^ 40 * 6206703 * 2
def baseEnd_6206703 : Nat := 3187021918702934979668399

theorem tailTrace_6206703 : CollatzResearch.WordTrace tailWord_6206703 prefixEnd_6206703 3187021918702934979668399 := by
  unfold tailWord_6206703
  simp only [CollatzResearch.WordTrace]
  refine ⟨226377056033182526324968763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150918037355455017549979175 226377056033182526324968763)
  ·
    refine ⟨339565584049773789487453145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226377056033182526324968763 339565584049773789487453145)
    ·
      refine ⟨254674188037330342115589859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339565584049773789487453145 254674188037330342115589859)
      ·
        refine ⟨382011282055995513173384789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254674188037330342115589859 382011282055995513173384789)
        ·
          refine ⟨4476694711593697420000603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 382011282055995513173384789 4476694711593697420000603)
          ·
            refine ⟨6715042067390546130000905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4476694711593697420000603 6715042067390546130000905)
            ·
              refine ⟨5036281550542909597500679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6715042067390546130000905 5036281550542909597500679)
              ·
                refine ⟨7554422325814364396251019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5036281550542909597500679 7554422325814364396251019)
                ·
                  refine ⟨11331633488721546594376529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7554422325814364396251019 11331633488721546594376529)
                  ·
                    refine ⟨8498725116541159945782397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11331633488721546594376529 8498725116541159945782397)
                    ·
                      refine ⟨3187021918702934979668399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8498725116541159945782397 3187021918702934979668399)
                      ·
                        rfl

theorem cell23_6206703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 1, 2, 3].length) (baseStart_6206703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206703 prefixEnd_6206703 := by exact prefixLift 6206703
  have htrace : WordTrace (prefixWord ++ tailWord_6206703) baseStart_6206703 baseEnd_6206703 := by
    simpa [prefixWord, tailWord_6206703, baseEnd_6206703] using wordTrace_append hprefix tailTrace_6206703
  have hstable : (prefixWord ++ tailWord_6206703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206703).length < 2 ^ (prefixWord ++ tailWord_6206703).sum := by decide
  have hdescent : baseEnd_6206703 < baseStart_6206703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206772 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_6206772 : Nat := 118140960795 + 6206772 * 2 ^ 59
def prefixEnd_6206772 : Nat := 4983230072969 + 3 ^ 40 * 6206772 * 2
def baseEnd_6206772 : Nat := 3187057348868095209705581

theorem tailTrace_6206772 : CollatzResearch.WordTrace tailWord_6206772 prefixEnd_6206772 3187057348868095209705581 := by
  unfold tailWord_6206772
  simp only [CollatzResearch.WordTrace]
  refine ⟨113189786334966275554615285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150919715113288367406153713 113189786334966275554615285)
  ·
    refine ⟨10611542468903088333245183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 113189786334966275554615285 10611542468903088333245183)
    ·
      refine ⟨15917313703354632499867775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10611542468903088333245183 15917313703354632499867775)
      ·
        refine ⟨23875970555031948749801663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15917313703354632499867775 23875970555031948749801663)
        ·
          refine ⟨35813955832547923124702495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23875970555031948749801663 35813955832547923124702495)
          ·
            refine ⟨53720933748821884687053743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35813955832547923124702495 53720933748821884687053743)
            ·
              refine ⟨80581400623232827030580615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53720933748821884687053743 80581400623232827030580615)
              ·
                refine ⟨120872100934849240545870923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80581400623232827030580615 120872100934849240545870923)
                ·
                  refine ⟨181308151402273860818806385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120872100934849240545870923 181308151402273860818806385)
                  ·
                    refine ⟨135981113551705395614104789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 181308151402273860818806385 135981113551705395614104789)
                    ·
                      refine ⟨3187057348868095209705581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 135981113551705395614104789 3187057348868095209705581)
                      ·
                        rfl

theorem cell23_6206772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_6206772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206772 prefixEnd_6206772 := by exact prefixLift 6206772
  have htrace : WordTrace (prefixWord ++ tailWord_6206772) baseStart_6206772 baseEnd_6206772 := by
    simpa [prefixWord, tailWord_6206772, baseEnd_6206772] using wordTrace_append hprefix tailTrace_6206772
  have hstable : (prefixWord ++ tailWord_6206772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206772).length < 2 ^ (prefixWord ++ tailWord_6206772).sum := by decide
  have hdescent : baseEnd_6206772 < baseStart_6206772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206829 : List Nat := [1, 5, 1, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_6206829 : Nat := 118140960795 + 6206829 * 2 ^ 59
def prefixEnd_6206829 : Nat := 4983230072969 + 3 ^ 40 * 6206829 * 2
def baseEnd_6206829 : Nat := 3187086617265401486692819

theorem tailTrace_6206829 : CollatzResearch.WordTrace tailWord_6206829 prefixEnd_6206829 3187086617265401486692819 := by
  unfold tailWord_6206829
  simp only [CollatzResearch.WordTrace]
  refine ⟨226381651630726049844055541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150921101087150699896037027 226381651630726049844055541)
  ·
    refine ⟨21223279840380567172880207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 226381651630726049844055541 21223279840380567172880207)
    ·
      refine ⟨31834919760570850759320311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21223279840380567172880207 31834919760570850759320311)
      ·
        refine ⟨47752379640856276138980467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31834919760570850759320311 47752379640856276138980467)
        ·
          refine ⟨71628569461284414208470701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47752379640856276138980467 71628569461284414208470701)
          ·
            refine ⟨26860713547981655328176513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71628569461284414208470701 26860713547981655328176513)
            ·
              refine ⟨20145535160986241496132385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26860713547981655328176513 20145535160986241496132385)
              ·
                refine ⟨15109151370739681122099289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20145535160986241496132385 15109151370739681122099289)
                ·
                  refine ⟨11331863528054760841574467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15109151370739681122099289 11331863528054760841574467)
                  ·
                    refine ⟨16997795292082141262361701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11331863528054760841574467 16997795292082141262361701)
                    ·
                      refine ⟨3187086617265401486692819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16997795292082141262361701 3187086617265401486692819)
                      ·
                        rfl

theorem cell23_6206829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_6206829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206829 prefixEnd_6206829 := by exact prefixLift 6206829
  have htrace : WordTrace (prefixWord ++ tailWord_6206829) baseStart_6206829 baseEnd_6206829 := by
    simpa [prefixWord, tailWord_6206829, baseEnd_6206829] using wordTrace_append hprefix tailTrace_6206829
  have hstable : (prefixWord ++ tailWord_6206829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206829).length < 2 ^ (prefixWord ++ tailWord_6206829).sum := by decide
  have hdescent : baseEnd_6206829 < baseStart_6206829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206830 : List Nat := [4, 1, 2, 4, 1, 2, 2, 2, 5]
def baseStart_6206830 : Nat := 118140960795 + 6206830 * 2 ^ 59
def prefixEnd_6206830 : Nat := 4983230072969 + 3 ^ 40 * 6206830 * 2
def baseEnd_6206830 : Nat := 354120792305117331420035

theorem tailTrace_6206830 : CollatzResearch.WordTrace tailWord_6206830 prefixEnd_6206830 354120792305117331420035 := by
  unfold tailWord_6206830
  simp only [CollatzResearch.WordTrace]
  refine ⟨28297711012965303376855243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150921125402481618009894629 28297711012965303376855243)
  ·
    refine ⟨42446566519447955065282865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28297711012965303376855243 42446566519447955065282865)
    ·
      refine ⟨31834924889585966298962149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42446566519447955065282865 31834924889585966298962149)
      ·
        refine ⟨5969048416797368681055403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31834924889585966298962149 5969048416797368681055403)
        ·
          refine ⟨8953572625196053021583105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5969048416797368681055403 8953572625196053021583105)
          ·
            refine ⟨6715179468897039766187329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8953572625196053021583105 6715179468897039766187329)
            ·
              refine ⟨5036384601672779824640497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6715179468897039766187329 5036384601672779824640497)
              ·
                refine ⟨3777288451254584868480373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5036384601672779824640497 3777288451254584868480373)
                ·
                  refine ⟨354120792305117331420035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3777288451254584868480373 354120792305117331420035)
                  ·
                    rfl

theorem cell23_6206830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_6206830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206830 prefixEnd_6206830 := by exact prefixLift 6206830
  have htrace : WordTrace (prefixWord ++ tailWord_6206830) baseStart_6206830 baseEnd_6206830 := by
    simpa [prefixWord, tailWord_6206830, baseEnd_6206830] using wordTrace_append hprefix tailTrace_6206830
  have hstable : (prefixWord ++ tailWord_6206830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206830).length < 2 ^ (prefixWord ++ tailWord_6206830).sum := by decide
  have hdescent : baseEnd_6206830 < baseStart_6206830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206916 : List Nat := [2, 3, 3, 2, 1, 1, 1, 4, 1, 5]
def baseStart_6206916 : Nat := 118140960795 + 6206916 * 2 ^ 59
def prefixEnd_6206916 : Nat := 4983230072969 + 3 ^ 40 * 6206916 * 2
def baseEnd_6206916 : Nat := 1062377096694114215434973

theorem tailTrace_6206916 : CollatzResearch.WordTrace tailWord_6206916 prefixEnd_6206916 1062377096694114215434973 := by
  unfold tailWord_6206916
  simp only [CollatzResearch.WordTrace]
  refine ⟨113192412390705431851236301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150923216520940575801648401 113192412390705431851236301)
  ·
    refine ⟨42447154646514536944213613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113192412390705431851236301 42447154646514536944213613)
    ·
      refine ⟨15917682992442951354080105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42447154646514536944213613 15917682992442951354080105)
      ·
        refine ⟨11938262244332213515560079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15917682992442951354080105 11938262244332213515560079)
        ·
          refine ⟨17907393366498320273340119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11938262244332213515560079 17907393366498320273340119)
          ·
            refine ⟨26861090049747480410010179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17907393366498320273340119 26861090049747480410010179)
            ·
              refine ⟨40291635074621220615015269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26861090049747480410010179 40291635074621220615015269)
              ·
                refine ⟨7554681576491478865315363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40291635074621220615015269 7554681576491478865315363)
                ·
                  refine ⟨11332022364737218297973045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7554681576491478865315363 11332022364737218297973045)
                  ·
                    refine ⟨1062377096694114215434973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11332022364737218297973045 1062377096694114215434973)
                    ·
                      rfl

theorem cell23_6206916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_6206916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206916 prefixEnd_6206916 := by exact prefixLift 6206916
  have htrace : WordTrace (prefixWord ++ tailWord_6206916) baseStart_6206916 baseEnd_6206916 := by
    simpa [prefixWord, tailWord_6206916, baseEnd_6206916] using wordTrace_append hprefix tailTrace_6206916
  have hstable : (prefixWord ++ tailWord_6206916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206916).length < 2 ^ (prefixWord ++ tailWord_6206916).sum := by decide
  have hdescent : baseEnd_6206916 < baseStart_6206916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206919 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 2, 6, 2]
def baseStart_6206919 : Nat := 118140960795 + 6206919 * 2 ^ 59
def prefixEnd_6206919 : Nat := 4983230072969 + 3 ^ 40 * 6206919 * 2
def baseEnd_6206919 : Nat := 3187132830524306134567405

theorem tailTrace_6206919 : CollatzResearch.WordTrace tailWord_6206919 prefixEnd_6206919 3187132830524306134567405 := by
  unfold tailWord_6206919
  simp only [CollatzResearch.WordTrace]
  refine ⟨226384934200399995214831811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150923289466933330143221207 226384934200399995214831811)
  ·
    refine ⟨339577401300599992822247717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226384934200399995214831811 339577401300599992822247717)
    ·
      refine ⟨63670762743862498654171447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 339577401300599992822247717 63670762743862498654171447)
      ·
        refine ⟨95506144115793747981257171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63670762743862498654171447 95506144115793747981257171)
        ·
          refine ⟨143259216173690621971885757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95506144115793747981257171 143259216173690621971885757)
          ·
            refine ⟨53722206065133983239457159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143259216173690621971885757 53722206065133983239457159)
            ·
              refine ⟨80583309097700974859185739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53722206065133983239457159 80583309097700974859185739)
              ·
                refine ⟨120874963646551462288778609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80583309097700974859185739 120874963646551462288778609)
                ·
                  refine ⟨90656222734913596716583957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120874963646551462288778609 90656222734913596716583957)
                  ·
                    refine ⟨4249510440699074846089873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90656222734913596716583957 4249510440699074846089873)
                    ·
                      refine ⟨3187132830524306134567405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4249510440699074846089873 3187132830524306134567405)
                      ·
                        rfl

theorem cell23_6206919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_6206919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206919 prefixEnd_6206919 := by exact prefixLift 6206919
  have htrace : WordTrace (prefixWord ++ tailWord_6206919) baseStart_6206919 baseEnd_6206919 := by
    simpa [prefixWord, tailWord_6206919, baseEnd_6206919] using wordTrace_append hprefix tailTrace_6206919
  have hstable : (prefixWord ++ tailWord_6206919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206919).length < 2 ^ (prefixWord ++ tailWord_6206919).sum := by decide
  have hdescent : baseEnd_6206919 < baseStart_6206919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206936 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 5, 2, 2]
def baseStart_6206936 : Nat := 118140960795 + 6206936 * 2 ^ 59
def prefixEnd_6206936 : Nat := 4983230072969 + 3 ^ 40 * 6206936 * 2
def baseEnd_6206936 : Nat := 3187141559695432568054827

theorem tailTrace_6206936 : CollatzResearch.WordTrace tailWord_6206936 prefixEnd_6206936 3187141559695432568054827 := by
  unfold tailWord_6206936
  simp only [CollatzResearch.WordTrace]
  refine ⟨113192777120669203559100331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150923702827558938078800441 113192777120669203559100331)
  ·
    refine ⟨169789165681003805338650497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113192777120669203559100331 169789165681003805338650497)
    ·
      refine ⟨127341874260752854003987873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169789165681003805338650497 127341874260752854003987873)
      ·
        refine ⟨95506405695564640502990905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127341874260752854003987873 95506405695564640502990905)
        ·
          refine ⟨71629804271673480377243179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95506405695564640502990905 71629804271673480377243179)
          ·
            refine ⟨107444706407510220565864769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71629804271673480377243179 107444706407510220565864769)
            ·
              refine ⟨80583529805632665424398577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107444706407510220565864769 80583529805632665424398577)
              ·
                refine ⟨60437647354224499068298933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80583529805632665424398577 60437647354224499068298933)
                ·
                  refine ⟨5666029439458546787653025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60437647354224499068298933 5666029439458546787653025)
                  ·
                    refine ⟨4249522079593910090739769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5666029439458546787653025 4249522079593910090739769)
                    ·
                      refine ⟨3187141559695432568054827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4249522079593910090739769 3187141559695432568054827)
                      ·
                        rfl

theorem cell23_6206936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_6206936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206936 prefixEnd_6206936 := by exact prefixLift 6206936
  have htrace : WordTrace (prefixWord ++ tailWord_6206936) baseStart_6206936 baseEnd_6206936 := by
    simpa [prefixWord, tailWord_6206936, baseEnd_6206936] using wordTrace_append hprefix tailTrace_6206936
  have hstable : (prefixWord ++ tailWord_6206936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206936).length < 2 ^ (prefixWord ++ tailWord_6206936).sum := by decide
  have hdescent : baseEnd_6206936 < baseStart_6206936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206949 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 1, 1, 6]
def baseStart_6206949 : Nat := 118140960795 + 6206949 * 2 ^ 59
def prefixEnd_6206949 : Nat := 4983230072969 + 3 ^ 40 * 6206949 * 2
def baseEnd_6206949 : Nat := 3187148234943941017192267

theorem tailTrace_6206949 : CollatzResearch.WordTrace tailWord_6206949 prefixEnd_6206949 3187148234943941017192267 := by
  unfold tailWord_6206949
  simp only [CollatzResearch.WordTrace]
  refine ⟨226386028390291310338423901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150924018926860873558949267 226386028390291310338423901)
  ·
    refine ⟨84894760646359241376908963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226386028390291310338423901 84894760646359241376908963)
    ·
      refine ⟨127342140969538862065363445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84894760646359241376908963 127342140969538862065363445)
      ·
        refine ⟨11938325715894268318627823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127342140969538862065363445 11938325715894268318627823)
        ·
          refine ⟨17907488573841402477941735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11938325715894268318627823 17907488573841402477941735)
          ·
            refine ⟨26861232860762103716912603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17907488573841402477941735 26861232860762103716912603)
            ·
              refine ⟨40291849291143155575368905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26861232860762103716912603 40291849291143155575368905)
              ·
                refine ⟨30218886968357366681526679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40291849291143155575368905 30218886968357366681526679)
                ·
                  refine ⟨45328330452536050022290019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30218886968357366681526679 45328330452536050022290019)
                  ·
                    refine ⟨67992495678804075033435029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45328330452536050022290019 67992495678804075033435029)
                    ·
                      refine ⟨3187148234943941017192267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67992495678804075033435029 3187148234943941017192267)
                      ·
                        rfl

theorem cell23_6206949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_6206949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206949 prefixEnd_6206949 := by exact prefixLift 6206949
  have htrace : WordTrace (prefixWord ++ tailWord_6206949) baseStart_6206949 baseEnd_6206949 := by
    simpa [prefixWord, tailWord_6206949, baseEnd_6206949] using wordTrace_append hprefix tailTrace_6206949
  have hstable : (prefixWord ++ tailWord_6206949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206949).length < 2 ^ (prefixWord ++ tailWord_6206949).sum := by decide
  have hdescent : baseEnd_6206949 < baseStart_6206949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206969 : List Nat := [1, 2, 1, 3, 1, 2, 1, 5, 1, 3, 3]
def baseStart_6206969 : Nat := 118140960795 + 6206969 * 2 ^ 59
def prefixEnd_6206969 : Nat := 4983230072969 + 3 ^ 40 * 6206969 * 2
def baseEnd_6206969 : Nat := 3187158504557030938942175

theorem tailTrace_6206969 : CollatzResearch.WordTrace tailWord_6206969 prefixEnd_6206969 3187158504557030938942175 := by
  unfold tailWord_6206969
  simp only [CollatzResearch.WordTrace]
  refine ⟨226386757850218853754151961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150924505233479235836101307 226386757850218853754151961)
  ·
    refine ⟨169790068387664140315613971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226386757850218853754151961 169790068387664140315613971)
    ·
      refine ⟨254685102581496210473420957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169790068387664140315613971 254685102581496210473420957)
      ·
        refine ⟨95506913468061078927532859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254685102581496210473420957 95506913468061078927532859)
        ·
          refine ⟨143260370202091618391299289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95506913468061078927532859 143260370202091618391299289)
          ·
            refine ⟨107445277651568713793474467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143260370202091618391299289 107445277651568713793474467)
            ·
              refine ⟨161167916477353070690211701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107445277651568713793474467 161167916477353070690211701)
              ·
                refine ⟨15109492169751850377207347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161167916477353070690211701 15109492169751850377207347)
                ·
                  refine ⟨22664238254627775565811021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15109492169751850377207347 22664238254627775565811021)
                  ·
                    refine ⟨8499089345485415837179133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22664238254627775565811021 8499089345485415837179133)
                    ·
                      refine ⟨3187158504557030938942175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8499089345485415837179133 3187158504557030938942175)
                      ·
                        rfl

theorem cell23_6206969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_6206969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206969 prefixEnd_6206969 := by exact prefixLift 6206969
  have htrace : WordTrace (prefixWord ++ tailWord_6206969) baseStart_6206969 baseEnd_6206969 := by
    simpa [prefixWord, tailWord_6206969, baseEnd_6206969] using wordTrace_append hprefix tailTrace_6206969
  have hstable : (prefixWord ++ tailWord_6206969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206969).length < 2 ^ (prefixWord ++ tailWord_6206969).sum := by decide
  have hdescent : baseEnd_6206969 < baseStart_6206969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206973 : List Nat := [1, 4, 1, 1, 1, 6, 1, 2, 1, 2, 3]
def baseStart_6206973 : Nat := 118140960795 + 6206973 * 2 ^ 59
def prefixEnd_6206973 : Nat := 4983230072969 + 3 ^ 40 * 6206973 * 2
def baseEnd_6206973 : Nat := 3187160558479648923292157

theorem tailTrace_6206973 : CollatzResearch.WordTrace tailWord_6206973 prefixEnd_6206973 3187160558479648923292157 := by
  unfold tailWord_6206973
  simp only [CollatzResearch.WordTrace]
  refine ⟨226386903742204362437297573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150924602494802908291531715 226386903742204362437297573)
  ·
    refine ⟨42447544451663317956993295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226386903742204362437297573 42447544451663317956993295)
    ·
      refine ⟨63671316677494976935489943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42447544451663317956993295 63671316677494976935489943)
      ·
        refine ⟨95506975016242465403234915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63671316677494976935489943 95506975016242465403234915)
        ·
          refine ⟨143260462524363698104852373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95506975016242465403234915 143260462524363698104852373)
          ·
            refine ⟨6715334180829548348664955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 143260462524363698104852373 6715334180829548348664955)
            ·
              refine ⟨10073001271244322522997433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6715334180829548348664955 10073001271244322522997433)
              ·
                refine ⟨7554750953433241892248075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10073001271244322522997433 7554750953433241892248075)
                ·
                  refine ⟨11332126430149862838372113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7554750953433241892248075 11332126430149862838372113)
                  ·
                    refine ⟨8499094822612397128779085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11332126430149862838372113 8499094822612397128779085)
                    ·
                      refine ⟨3187160558479648923292157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8499094822612397128779085 3187160558479648923292157)
                      ·
                        rfl

theorem cell23_6206973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_6206973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206973 prefixEnd_6206973 := by exact prefixLift 6206973
  have htrace : WordTrace (prefixWord ++ tailWord_6206973) baseStart_6206973 baseEnd_6206973 := by
    simpa [prefixWord, tailWord_6206973, baseEnd_6206973] using wordTrace_append hprefix tailTrace_6206973
  have hstable : (prefixWord ++ tailWord_6206973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206973).length < 2 ^ (prefixWord ++ tailWord_6206973).sum := by decide
  have hdescent : baseEnd_6206973 < baseStart_6206973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206986 : List Nat := [3, 1, 2, 2, 2, 3, 1, 2, 1, 3, 3]
def baseStart_6206986 : Nat := 118140960795 + 6206986 * 2 ^ 59
def prefixEnd_6206986 : Nat := 4983230072969 + 3 ^ 40 * 6206986 * 2
def baseEnd_6206986 : Nat := 3187167233728157372429597

theorem tailTrace_6206986 : CollatzResearch.WordTrace tailWord_6206986 prefixEnd_6206986 3187167233728157372429597 := by
  unfold tailWord_6206986
  simp only [CollatzResearch.WordTrace]
  refine ⟨56596844472789316414380203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150924918594104843771680541 56596844472789316414380203)
  ·
    refine ⟨84895266709183974621570305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56596844472789316414380203 84895266709183974621570305)
    ·
      refine ⟨63671450031887980966177729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84895266709183974621570305 63671450031887980966177729)
      ·
        refine ⟨47753587523915985724633297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63671450031887980966177729 47753587523915985724633297)
        ·
          refine ⟨35815190642936989293474973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47753587523915985724633297 35815190642936989293474973)
          ·
            refine ⟨13430696491101370985053115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35815190642936989293474973 13430696491101370985053115)
            ·
              refine ⟨20146044736652056477579673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13430696491101370985053115 20146044736652056477579673)
              ·
                refine ⟨15109533552489042358184755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20146044736652056477579673 15109533552489042358184755)
                ·
                  refine ⟨22664300328733563537277133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15109533552489042358184755 22664300328733563537277133)
                  ·
                    refine ⟨8499112623275086326478925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22664300328733563537277133 8499112623275086326478925)
                    ·
                      refine ⟨3187167233728157372429597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8499112623275086326478925 3187167233728157372429597)
                      ·
                        rfl

theorem cell23_6206986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_6206986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206986 prefixEnd_6206986 := by exact prefixLift 6206986
  have htrace : WordTrace (prefixWord ++ tailWord_6206986) baseStart_6206986 baseEnd_6206986 := by
    simpa [prefixWord, tailWord_6206986, baseEnd_6206986] using wordTrace_append hprefix tailTrace_6206986
  have hstable : (prefixWord ++ tailWord_6206986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206986).length < 2 ^ (prefixWord ++ tailWord_6206986).sum := by decide
  have hdescent : baseEnd_6206986 < baseStart_6206986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6206990 : List Nat := [4, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3]
def baseStart_6206990 : Nat := 118140960795 + 6206990 * 2 ^ 59
def prefixEnd_6206990 : Nat := 4983230072969 + 3 ^ 40 * 6206990 * 2
def baseEnd_6206990 : Nat := 3187169287650775356779579

theorem tailTrace_6206990 : CollatzResearch.WordTrace tailWord_6206990 prefixEnd_6206990 3187169287650775356779579 := by
  unfold tailWord_6206990
  simp only [CollatzResearch.WordTrace]
  refine ⟨28298440472892846792583303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150925015855428516227110949 28298440472892846792583303)
  ·
    refine ⟨42447660709339270188874955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28298440472892846792583303 42447660709339270188874955)
    ·
      refine ⟨63671491064008905283312433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42447660709339270188874955 63671491064008905283312433)
      ·
        refine ⟨47753618298006678962484325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63671491064008905283312433 47753618298006678962484325)
        ·
          refine ⟨8953803430876252305465811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47753618298006678962484325 8953803430876252305465811)
          ·
            refine ⟨13430705146314378458198717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8953803430876252305465811 13430705146314378458198717)
            ·
              refine ⟨5036514429867891921824519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13430705146314378458198717 5036514429867891921824519)
              ·
                refine ⟨7554771644801837882736779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5036514429867891921824519 7554771644801837882736779)
                ·
                  refine ⟨11332157467202756824105169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7554771644801837882736779 11332157467202756824105169)
                  ·
                    refine ⟨8499118100402067618078877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11332157467202756824105169 8499118100402067618078877)
                    ·
                      refine ⟨3187169287650775356779579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8499118100402067618078877 3187169287650775356779579)
                      ·
                        rfl

theorem cell23_6206990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_6206990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6206990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6206990 prefixEnd_6206990 := by exact prefixLift 6206990
  have htrace : WordTrace (prefixWord ++ tailWord_6206990) baseStart_6206990 baseEnd_6206990 := by
    simpa [prefixWord, tailWord_6206990, baseEnd_6206990] using wordTrace_append hprefix tailTrace_6206990
  have hstable : (prefixWord ++ tailWord_6206990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6206990).length < 2 ^ (prefixWord ++ tailWord_6206990).sum := by decide
  have hdescent : baseEnd_6206990 < baseStart_6206990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6206990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207009 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_6207009 : Nat := 118140960795 + 6207009 * 2 ^ 59
def prefixEnd_6207009 : Nat := 4983230072969 + 3 ^ 40 * 6207009 * 2
def baseEnd_6207009 : Nat := 3187179043783210782441991

theorem tailTrace_6207009 : CollatzResearch.WordTrace tailWord_6207009 prefixEnd_6207009 3187179043783210782441991 := by
  unfold tailWord_6207009
  simp only [CollatzResearch.WordTrace]
  refine ⟨226388216770073940585608081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150925477846715960390405387 226388216770073940585608081)
  ·
    refine ⟨169791162577555455439206061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226388216770073940585608081 169791162577555455439206061)
    ·
      refine ⟨63671685966583295789702273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169791162577555455439206061 63671685966583295789702273)
      ·
        refine ⟨47753764474937471842276705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63671685966583295789702273 47753764474937471842276705)
        ·
          refine ⟨35815323356203103881707529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47753764474937471842276705 35815323356203103881707529)
          ·
            refine ⟨26861492517152327911280647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35815323356203103881707529 26861492517152327911280647)
            ·
              refine ⟨40292238775728491866920971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26861492517152327911280647 40292238775728491866920971)
              ·
                refine ⟨60438358163592737800381457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40292238775728491866920971 60438358163592737800381457)
                ·
                  refine ⟨45328768622694553350286093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60438358163592737800381457 45328768622694553350286093)
                  ·
                    refine ⟨16998288233510457506357285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45328768622694553350286093 16998288233510457506357285)
                    ·
                      refine ⟨3187179043783210782441991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16998288233510457506357285 3187179043783210782441991)
                      ·
                        rfl

theorem cell23_6207009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_6207009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207009 prefixEnd_6207009 := by exact prefixLift 6207009
  have htrace : WordTrace (prefixWord ++ tailWord_6207009) baseStart_6207009 baseEnd_6207009 := by
    simpa [prefixWord, tailWord_6207009, baseEnd_6207009] using wordTrace_append hprefix tailTrace_6207009
  have hstable : (prefixWord ++ tailWord_6207009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207009).length < 2 ^ (prefixWord ++ tailWord_6207009).sum := by decide
  have hdescent : baseEnd_6207009 < baseStart_6207009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207047 : List Nat := [1, 1, 4, 1, 5, 2, 2, 1, 1, 3, 2]
def baseStart_6207047 : Nat := 118140960795 + 6207047 * 2 ^ 59
def prefixEnd_6207047 : Nat := 4983230072969 + 3 ^ 40 * 6207047 * 2
def baseEnd_6207047 : Nat := 3187198556048081633766817

theorem tailTrace_6207047 : CollatzResearch.WordTrace tailWord_6207047 prefixEnd_6207047 3187198556048081633766817 := by
  unfold tailWord_6207047
  simp only [CollatzResearch.WordTrace]
  refine ⟨226389602743936273075491395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150926401829290848716994263 226389602743936273075491395)
  ·
    refine ⟨339584404115904409613237093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226389602743936273075491395 339584404115904409613237093)
    ·
      refine ⟨63672075771732076802481955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 339584404115904409613237093 63672075771732076802481955)
      ·
        refine ⟨95508113657598115203722933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63672075771732076802481955 95508113657598115203722933)
        ·
          refine ⟨8953885655399823300349025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 95508113657598115203722933 8953885655399823300349025)
          ·
            refine ⟨6715414241549867475261769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8953885655399823300349025 6715414241549867475261769)
            ·
              refine ⟨5036560681162400606446327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6715414241549867475261769 5036560681162400606446327)
              ·
                refine ⟨7554841021743600909669491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5036560681162400606446327 7554841021743600909669491)
                ·
                  refine ⟨11332261532615401364504237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7554841021743600909669491 11332261532615401364504237)
                  ·
                    refine ⟨4249598074730775511689089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11332261532615401364504237 4249598074730775511689089)
                    ·
                      refine ⟨3187198556048081633766817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4249598074730775511689089 3187198556048081633766817)
                      ·
                        rfl

theorem cell23_6207047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_6207047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207047 prefixEnd_6207047 := by exact prefixLift 6207047
  have htrace : WordTrace (prefixWord ++ tailWord_6207047) baseStart_6207047 baseEnd_6207047 := by
    simpa [prefixWord, tailWord_6207047, baseEnd_6207047] using wordTrace_append hprefix tailTrace_6207047
  have hstable : (prefixWord ++ tailWord_6207047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207047).length < 2 ^ (prefixWord ++ tailWord_6207047).sum := by decide
  have hdescent : baseEnd_6207047 < baseStart_6207047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207076 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 2, 3, 3]
def baseStart_6207076 : Nat := 118140960795 + 6207076 * 2 ^ 59
def prefixEnd_6207076 : Nat := 4983230072969 + 3 ^ 40 * 6207076 * 2
def baseEnd_6207076 : Nat := 3187213446987062020304183

theorem tailTrace_6207076 : CollatzResearch.WordTrace tailWord_6207076 prefixEnd_6207076 3187213446987062020304183 := by
  unfold tailWord_6207076
  simp only [CollatzResearch.WordTrace]
  refine ⟨113195330230415605514148541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150927106973887474018864721 113195330230415605514148541)
  ·
    refine ⟨42448248836405852067805703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113195330230415605514148541 42448248836405852067805703)
    ·
      refine ⟨63672373254608778101708555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42448248836405852067805703 63672373254608778101708555)
      ·
        refine ⟨95508559881913167152562833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63672373254608778101708555 95508559881913167152562833)
        ·
          refine ⟨71631419911434875364422125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95508559881913167152562833 71631419911434875364422125)
          ·
            refine ⟨26861782466788078261658297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71631419911434875364422125 26861782466788078261658297)
            ·
              refine ⟨20146336850091058696243723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26861782466788078261658297 20146336850091058696243723)
              ·
                refine ⟨30219505275136588044365585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20146336850091058696243723 30219505275136588044365585)
                ·
                  refine ⟨22664628956352441033274189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30219505275136588044365585 22664628956352441033274189)
                  ·
                    refine ⟨8499235858632165387477821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22664628956352441033274189 8499235858632165387477821)
                    ·
                      refine ⟨3187213446987062020304183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8499235858632165387477821 3187213446987062020304183)
                      ·
                        rfl

theorem cell23_6207076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_6207076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207076 prefixEnd_6207076 := by exact prefixLift 6207076
  have htrace : WordTrace (prefixWord ++ tailWord_6207076) baseStart_6207076 baseEnd_6207076 := by
    simpa [prefixWord, tailWord_6207076, baseEnd_6207076] using wordTrace_append hprefix tailTrace_6207076
  have hstable : (prefixWord ++ tailWord_6207076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207076).length < 2 ^ (prefixWord ++ tailWord_6207076).sum := by decide
  have hdescent : baseEnd_6207076 < baseStart_6207076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207077 : List Nat := [1, 3, 1, 3, 3, 2, 3, 1, 2, 2, 2]
def baseStart_6207077 : Nat := 118140960795 + 6207077 * 2 ^ 59
def prefixEnd_6207077 : Nat := 4983230072969 + 3 ^ 40 * 6207077 * 2
def baseEnd_6207077 : Nat := 3187213960467716516391679

theorem tailTrace_6207077 : CollatzResearch.WordTrace tailWord_6207077 prefixEnd_6207077 3187213960467716516391679 := by
  unfold tailWord_6207077
  simp only [CollatzResearch.WordTrace]
  refine ⟨226390696933827588199083485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150927131289218392132722323 226390696933827588199083485)
  ·
    refine ⟨84896511350185345574656307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226390696933827588199083485 84896511350185345574656307)
    ·
      refine ⟨127344767025278018361984461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84896511350185345574656307 127344767025278018361984461)
      ·
        refine ⟨47754287634479256885744173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127344767025278018361984461 47754287634479256885744173)
        ·
          refine ⟨17907857862929721332154065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47754287634479256885744173 17907857862929721332154065)
          ·
            refine ⟨13430893397197290999115549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17907857862929721332154065 13430893397197290999115549)
            ·
              refine ⟨5036585023948984124668331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13430893397197290999115549 5036585023948984124668331)
              ·
                refine ⟨7554877535923476187002497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5036585023948984124668331 7554877535923476187002497)
                ·
                  refine ⟨5666158151942607140251873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7554877535923476187002497 5666158151942607140251873)
                  ·
                    refine ⟨4249618613956955355188905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5666158151942607140251873 4249618613956955355188905)
                    ·
                      refine ⟨3187213960467716516391679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4249618613956955355188905 3187213960467716516391679)
                      ·
                        rfl

theorem cell23_6207077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_6207077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207077 prefixEnd_6207077 := by exact prefixLift 6207077
  have htrace : WordTrace (prefixWord ++ tailWord_6207077) baseStart_6207077 baseEnd_6207077 := by
    simpa [prefixWord, tailWord_6207077, baseEnd_6207077] using wordTrace_append hprefix tailTrace_6207077
  have hstable : (prefixWord ++ tailWord_6207077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207077).length < 2 ^ (prefixWord ++ tailWord_6207077).sum := by decide
  have hdescent : baseEnd_6207077 < baseStart_6207077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207079 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 1, 7]
def baseStart_6207079 : Nat := 118140960795 + 6207079 * 2 ^ 59
def prefixEnd_6207079 : Nat := 4983230072969 + 3 ^ 40 * 6207079 * 2
def baseEnd_6207079 : Nat := 1062404995809675169522223

theorem tailTrace_6207079 : CollatzResearch.WordTrace tailWord_6207079 prefixEnd_6207079 1062404995809675169522223 := by
  unfold tailWord_6207079
  simp only [CollatzResearch.WordTrace]
  refine ⟨226390769879820342540656291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150927179919880228360437527 226390769879820342540656291)
  ·
    refine ⟨339586154819730513810984437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226390769879820342540656291 339586154819730513810984437)
    ·
      refine ⟨31836202014349735669779791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 339586154819730513810984437 31836202014349735669779791)
      ·
        refine ⟨47754303021524603504669687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31836202014349735669779791 47754303021524603504669687)
        ·
          refine ⟨71631454532286905257004531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47754303021524603504669687 71631454532286905257004531)
          ·
            refine ⟨107447181798430357885506797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71631454532286905257004531 107447181798430357885506797)
            ·
              refine ⟨40292693174411384207065049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107447181798430357885506797 40292693174411384207065049)
              ·
                refine ⟨30219519880808538155298787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40292693174411384207065049 30219519880808538155298787)
                ·
                  refine ⟨45329279821212807232948181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30219519880808538155298787 45329279821212807232948181)
                  ·
                    refine ⟨1062404995809675169522223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45329279821212807232948181 1062404995809675169522223)
                    ·
                      rfl

theorem cell23_6207079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_6207079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207079 prefixEnd_6207079 := by exact prefixLift 6207079
  have htrace : WordTrace (prefixWord ++ tailWord_6207079) baseStart_6207079 baseEnd_6207079 := by
    simpa [prefixWord, tailWord_6207079, baseEnd_6207079] using wordTrace_append hprefix tailTrace_6207079
  have hstable : (prefixWord ++ tailWord_6207079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207079).length < 2 ^ (prefixWord ++ tailWord_6207079).sum := by decide
  have hdescent : baseEnd_6207079 < baseStart_6207079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207099 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 4]
def baseStart_6207099 : Nat := 118140960795 + 6207099 * 2 ^ 59
def prefixEnd_6207099 : Nat := 4983230072969 + 3 ^ 40 * 6207099 * 2
def baseEnd_6207099 : Nat := 3187225257042115430316577

theorem tailTrace_6207099 : CollatzResearch.WordTrace tailWord_6207099 prefixEnd_6207099 3187225257042115430316577 := by
  unfold tailWord_6207099
  simp only [CollatzResearch.WordTrace]
  refine ⟨226391499339747885956384351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150927666226498590637589567 226391499339747885956384351)
  ·
    refine ⟨339587249009621828934576527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226391499339747885956384351 339587249009621828934576527)
    ·
      refine ⟨509380873514432743401864791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339587249009621828934576527 509380873514432743401864791)
      ·
        refine ⟨764071310271649115102797187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509380873514432743401864791 764071310271649115102797187)
        ·
          refine ⟨1146106965407473672654195781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764071310271649115102797187 1146106965407473672654195781)
          ·
            refine ⟨214895056013901313622661709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1146106965407473672654195781 214895056013901313622661709)
            ·
              refine ⟨80585646005212992608498141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214895056013901313622661709 80585646005212992608498141)
              ·
                refine ⟨30219617251954872228186803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80585646005212992608498141 30219617251954872228186803)
                ·
                  refine ⟨45329425877932308342280205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30219617251954872228186803 45329425877932308342280205)
                  ·
                    refine ⟨16998534704224615628355077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45329425877932308342280205 16998534704224615628355077)
                    ·
                      refine ⟨3187225257042115430316577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16998534704224615628355077 3187225257042115430316577)
                      ·
                        rfl

theorem cell23_6207099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 4].length) (baseStart_6207099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207099 prefixEnd_6207099 := by exact prefixLift 6207099
  have htrace : WordTrace (prefixWord ++ tailWord_6207099) baseStart_6207099 baseEnd_6207099 := by
    simpa [prefixWord, tailWord_6207099, baseEnd_6207099] using wordTrace_append hprefix tailTrace_6207099
  have hstable : (prefixWord ++ tailWord_6207099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207099).length < 2 ^ (prefixWord ++ tailWord_6207099).sum := by decide
  have hdescent : baseEnd_6207099 < baseStart_6207099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207116 : List Nat := [2, 2, 1, 2, 1, 1, 5, 2, 2, 1, 4]
def baseStart_6207116 : Nat := 118140960795 + 6207116 * 2 ^ 59
def prefixEnd_6207116 : Nat := 4983230072969 + 3 ^ 40 * 6207116 * 2
def baseEnd_6207116 : Nat := 3187233986213241863803999

theorem tailTrace_6207116 : CollatzResearch.WordTrace tailWord_6207116 prefixEnd_6207116 3187233986213241863803999 := by
  unfold tailWord_6207116
  simp only [CollatzResearch.WordTrace]
  refine ⟨113196059690343148929876601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150928079587124198573168801 113196059690343148929876601)
  ·
    refine ⟨84897044767757361697407451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113196059690343148929876601 84897044767757361697407451)
    ·
      refine ⟨127345567151636042546111177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84897044767757361697407451 127345567151636042546111177)
      ·
        refine ⟨95509175363727031909583383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127345567151636042546111177 95509175363727031909583383)
        ·
          refine ⟨143263763045590547864375075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95509175363727031909583383 143263763045590547864375075)
          ·
            refine ⟨214895644568385821796562613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143263763045590547864375075 214895644568385821796562613)
            ·
              refine ⟨20146466678286170793427745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 214895644568385821796562613 20146466678286170793427745)
              ·
                refine ⟨15109850008714628095070809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20146466678286170793427745 15109850008714628095070809)
                ·
                  refine ⟨11332387506535971071303107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15109850008714628095070809 11332387506535971071303107)
                  ·
                    refine ⟨16998581259803956606954661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11332387506535971071303107 16998581259803956606954661)
                    ·
                      refine ⟨3187233986213241863803999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16998581259803956606954661 3187233986213241863803999)
                      ·
                        rfl

theorem cell23_6207116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_6207116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207116 prefixEnd_6207116 := by exact prefixLift 6207116
  have htrace : WordTrace (prefixWord ++ tailWord_6207116) baseStart_6207116 baseEnd_6207116 := by
    simpa [prefixWord, tailWord_6207116, baseEnd_6207116] using wordTrace_append hprefix tailTrace_6207116
  have hstable : (prefixWord ++ tailWord_6207116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207116).length < 2 ^ (prefixWord ++ tailWord_6207116).sum := by decide
  have hdescent : baseEnd_6207116 < baseStart_6207116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207129 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 2, 4, 4]
def baseStart_6207129 : Nat := 118140960795 + 6207129 * 2 ^ 59
def prefixEnd_6207129 : Nat := 4983230072969 + 3 ^ 40 * 6207129 * 2
def baseEnd_6207129 : Nat := 3187240661461750312941439

theorem tailTrace_6207129 : CollatzResearch.WordTrace tailWord_6207129 prefixEnd_6207129 3187240661461750312941439 := by
  unfold tailWord_6207129
  simp only [CollatzResearch.WordTrace]
  refine ⟨226392593529639201079976441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150928395686426134053317627 226392593529639201079976441)
  ·
    refine ⟨169794445147229400809982331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226392593529639201079976441 169794445147229400809982331)
    ·
      refine ⟨254691667720844101214973497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169794445147229400809982331 254691667720844101214973497)
      ·
        refine ⟨191018750790633075911230123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254691667720844101214973497 191018750790633075911230123)
        ·
          refine ⟨286528126185949613866845185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191018750790633075911230123 286528126185949613866845185)
          ·
            refine ⟨214896094639462210400133889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286528126185949613866845185 214896094639462210400133889)
            ·
              refine ⟨161172070979596657800100417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214896094639462210400133889 161172070979596657800100417)
              ·
                refine ⟨120879053234697493350075313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161172070979596657800100417 120879053234697493350075313)
                ·
                  refine ⟨90659289926023120012556485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120879053234697493350075313 90659289926023120012556485)
                  ·
                    refine ⟨16998616861129335002354341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90659289926023120012556485 16998616861129335002354341)
                    ·
                      refine ⟨3187240661461750312941439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16998616861129335002354341 3187240661461750312941439)
                      ·
                        rfl

theorem cell23_6207129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_6207129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207129 prefixEnd_6207129 := by exact prefixLift 6207129
  have htrace : WordTrace (prefixWord ++ tailWord_6207129) baseStart_6207129 baseEnd_6207129 := by
    simpa [prefixWord, tailWord_6207129, baseEnd_6207129] using wordTrace_append hprefix tailTrace_6207129
  have hstable : (prefixWord ++ tailWord_6207129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207129).length < 2 ^ (prefixWord ++ tailWord_6207129).sum := by decide
  have hdescent : baseEnd_6207129 < baseStart_6207129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207179 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 5]
def baseStart_6207179 : Nat := 118140960795 + 6207179 * 2 ^ 59
def prefixEnd_6207179 : Nat := 4983230072969 + 3 ^ 40 * 6207179 * 2
def baseEnd_6207179 : Nat := 3187266335494475117316209

theorem tailTrace_6207179 : CollatzResearch.WordTrace tailWord_6207179 prefixEnd_6207179 3187266335494475117316209 := by
  unfold tailWord_6207179
  simp only [CollatzResearch.WordTrace]
  refine ⟨226394417179458059619296591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150929611452972039746197727 226394417179458059619296591)
  ·
    refine ⟨339591625769187089428944887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226394417179458059619296591 339591625769187089428944887)
    ·
      refine ⟨509387438653780634143417331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339591625769187089428944887 509387438653780634143417331)
      ·
        refine ⟨764081157980670951215125997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509387438653780634143417331 764081157980670951215125997)
        ·
          refine ⟨286530434242751606705672249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 764081157980670951215125997 286530434242751606705672249)
          ·
            refine ⟨214897825682063705029254187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286530434242751606705672249 214897825682063705029254187)
            ·
              refine ⟨322346738523095557543881281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214897825682063705029254187 322346738523095557543881281)
              ·
                refine ⟨241760053892321668157910961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322346738523095557543881281 241760053892321668157910961)
                ·
                  refine ⟨181320040419241251118433221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241760053892321668157910961 181320040419241251118433221)
                  ·
                    refine ⟨33997507578607734584706229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 181320040419241251118433221 33997507578607734584706229)
                    ·
                      refine ⟨3187266335494475117316209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33997507578607734584706229 3187266335494475117316209)
                      ·
                        rfl

theorem cell23_6207179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 5].length) (baseStart_6207179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207179 prefixEnd_6207179 := by exact prefixLift 6207179
  have htrace : WordTrace (prefixWord ++ tailWord_6207179) baseStart_6207179 baseEnd_6207179 := by
    simpa [prefixWord, tailWord_6207179, baseEnd_6207179] using wordTrace_append hprefix tailTrace_6207179
  have hstable : (prefixWord ++ tailWord_6207179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207179).length < 2 ^ (prefixWord ++ tailWord_6207179).sum := by decide
  have hdescent : baseEnd_6207179 < baseStart_6207179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207210 : List Nat := [3, 1, 3, 1, 1, 1, 5, 1, 2, 3, 2]
def baseStart_6207210 : Nat := 118140960795 + 6207210 * 2 ^ 59
def prefixEnd_6207210 : Nat := 4983230072969 + 3 ^ 40 * 6207210 * 2
def baseEnd_6207210 : Nat := 3187282253394764496028567

theorem tailTrace_6207210 : CollatzResearch.WordTrace tailWord_6207210 prefixEnd_6207210 3187282253394764496028567 := by
  unfold tailWord_6207210
  simp only [CollatzResearch.WordTrace]
  refine ⟨56598886960586437978418771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150930365228230501275783389 56598886960586437978418771)
  ·
    refine ⟨84898330440879656967628157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56598886960586437978418771 84898330440879656967628157)
    ·
      refine ⟨31836873915329871362860559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84898330440879656967628157 31836873915329871362860559)
      ·
        refine ⟨47755310872994807044290839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31836873915329871362860559 47755310872994807044290839)
        ·
          refine ⟨71632966309492210566436259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47755310872994807044290839 71632966309492210566436259)
          ·
            refine ⟨107449449464238315849654389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71632966309492210566436259 107449449464238315849654389)
            ·
              refine ⟨10073385887272342110905099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107449449464238315849654389 10073385887272342110905099)
              ·
                refine ⟨15110078830908513166357649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10073385887272342110905099 15110078830908513166357649)
                ·
                  refine ⟨11332559123181384874768237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15110078830908513166357649 11332559123181384874768237)
                  ·
                    refine ⟨4249709671193019328038089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11332559123181384874768237 4249709671193019328038089)
                    ·
                      refine ⟨3187282253394764496028567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4249709671193019328038089 3187282253394764496028567)
                      ·
                        rfl

theorem cell23_6207210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_6207210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207210 prefixEnd_6207210 := by exact prefixLift 6207210
  have htrace : WordTrace (prefixWord ++ tailWord_6207210) baseStart_6207210 baseEnd_6207210 := by
    simpa [prefixWord, tailWord_6207210, baseEnd_6207210] using wordTrace_append hprefix tailTrace_6207210
  have hstable : (prefixWord ++ tailWord_6207210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207210).length < 2 ^ (prefixWord ++ tailWord_6207210).sum := by decide
  have hdescent : baseEnd_6207210 < baseStart_6207210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207217 : List Nat := [1, 2, 2, 2, 2, 4, 2, 3, 1, 1, 3]
def baseStart_6207217 : Nat := 118140960795 + 6207217 * 2 ^ 59
def prefixEnd_6207217 : Nat := 4983230072969 + 3 ^ 40 * 6207217 * 2
def baseEnd_6207217 : Nat := 3187285847759345968641035

theorem tailTrace_6207217 : CollatzResearch.WordTrace tailWord_6207217 prefixEnd_6207217 3187285847759345968641035 := by
  unfold tailWord_6207217
  simp only [CollatzResearch.WordTrace]
  refine ⟨226395803153320392109179905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150930535435546928072786603 226395803153320392109179905)
  ·
    refine ⟨169796852364990294081884929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226395803153320392109179905 169796852364990294081884929)
    ·
      refine ⟨127347639273742720561413697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169796852364990294081884929 127347639273742720561413697)
      ·
        refine ⟨95510729455307040421060273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127347639273742720561413697 95510729455307040421060273)
        ·
          refine ⟨71633047091480280315795205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95510729455307040421060273 71633047091480280315795205)
          ·
            refine ⟨13431196329652552559211601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71633047091480280315795205 13431196329652552559211601)
            ·
              refine ⟨10073397247239414419408701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13431196329652552559211601 10073397247239414419408701)
              ·
                refine ⟨3777523967714780407278263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10073397247239414419408701 3777523967714780407278263)
                ·
                  refine ⟨5666285951572170610917395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3777523967714780407278263 5666285951572170610917395)
                  ·
                    refine ⟨8499428927358255916376093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5666285951572170610917395 8499428927358255916376093)
                    ·
                      refine ⟨3187285847759345968641035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8499428927358255916376093 3187285847759345968641035)
                      ·
                        rfl

theorem cell23_6207217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 1, 1, 3].length) (baseStart_6207217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207217 prefixEnd_6207217 := by exact prefixLift 6207217
  have htrace : WordTrace (prefixWord ++ tailWord_6207217) baseStart_6207217 baseEnd_6207217 := by
    simpa [prefixWord, tailWord_6207217, baseEnd_6207217] using wordTrace_append hprefix tailTrace_6207217
  have hstable : (prefixWord ++ tailWord_6207217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207217).length < 2 ^ (prefixWord ++ tailWord_6207217).sum := by decide
  have hdescent : baseEnd_6207217 < baseStart_6207217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207226 : List Nat := [3, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5]
def baseStart_6207226 : Nat := 118140960795 + 6207226 * 2 ^ 59
def prefixEnd_6207226 : Nat := 4983230072969 + 3 ^ 40 * 6207226 * 2
def baseEnd_6207226 : Nat := 3187290469085236433428493

theorem tailTrace_6207226 : CollatzResearch.WordTrace tailWord_6207226 prefixEnd_6207226 3187290469085236433428493 := by
  unfold tailWord_6207226
  simp only [CollatzResearch.WordTrace]
  refine ⟨56599032852571946661564383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150930754273525191097505021 56599032852571946661564383)
  ·
    refine ⟨84898549278857919992346575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56599032852571946661564383 84898549278857919992346575)
    ·
      refine ⟨127347823918286879988519863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84898549278857919992346575 127347823918286879988519863)
      ·
        refine ⟨191021735877430319982779795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127347823918286879988519863 191021735877430319982779795)
        ·
          refine ⟨286532603816145479974169693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191021735877430319982779795 286532603816145479974169693)
          ·
            refine ⟨107449726431054554990313635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286532603816145479974169693 107449726431054554990313635)
            ·
              refine ⟨161174589646581832485470453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107449726431054554990313635 161174589646581832485470453)
              ·
                refine ⟨15110117779367046795512855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 161174589646581832485470453 15110117779367046795512855)
                ·
                  refine ⟨22665176669050570193269283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15110117779367046795512855 22665176669050570193269283)
                  ·
                    refine ⟨33997765003575855289903925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22665176669050570193269283 33997765003575855289903925)
                    ·
                      refine ⟨3187290469085236433428493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33997765003575855289903925 3187290469085236433428493)
                      ·
                        rfl

theorem cell23_6207226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_6207226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207226 prefixEnd_6207226 := by exact prefixLift 6207226
  have htrace : WordTrace (prefixWord ++ tailWord_6207226) baseStart_6207226 baseEnd_6207226 := by
    simpa [prefixWord, tailWord_6207226, baseEnd_6207226] using wordTrace_append hprefix tailTrace_6207226
  have hstable : (prefixWord ++ tailWord_6207226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207226).length < 2 ^ (prefixWord ++ tailWord_6207226).sum := by decide
  have hdescent : baseEnd_6207226 < baseStart_6207226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207250 : List Nat := [3, 2, 4, 1, 1, 1, 3, 1, 1, 6]
def baseStart_6207250 : Nat := 118140960795 + 6207250 * 2 ^ 59
def prefixEnd_6207250 : Nat := 4983230072969 + 3 ^ 40 * 6207250 * 2
def baseEnd_6207250 : Nat := 1062434264206981446509461

theorem tailTrace_6207250 : CollatzResearch.WordTrace tailWord_6207250 prefixEnd_6207250 1062434264206981446509461 := by
  unfold tailWord_6207250
  simp only [CollatzResearch.WordTrace]
  refine ⟨56599251690550209686282801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150931337841467225830087469 56599251690550209686282801)
  ·
    refine ⟨42449438767912657264712101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56599251690550209686282801 42449438767912657264712101)
    ·
      refine ⟨7959269768983623237133519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42449438767912657264712101 7959269768983623237133519)
      ·
        refine ⟨11938904653475434855700279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7959269768983623237133519 11938904653475434855700279)
        ·
          refine ⟨17908356980213152283550419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11938904653475434855700279 17908356980213152283550419)
          ·
            refine ⟨26862535470319728425325629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17908356980213152283550419 26862535470319728425325629)
            ·
              refine ⟨10073450801369898159497111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26862535470319728425325629 10073450801369898159497111)
              ·
                refine ⟨15110176202054847239245667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10073450801369898159497111 15110176202054847239245667)
                ·
                  refine ⟨22665264303082270858868501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15110176202054847239245667 22665264303082270858868501)
                  ·
                    refine ⟨1062434264206981446509461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22665264303082270858868501 1062434264206981446509461)
                    ·
                      rfl

theorem cell23_6207250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_6207250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207250 prefixEnd_6207250 := by exact prefixLift 6207250
  have htrace : WordTrace (prefixWord ++ tailWord_6207250) baseStart_6207250 baseEnd_6207250 := by
    simpa [prefixWord, tailWord_6207250, baseEnd_6207250] using wordTrace_append hprefix tailTrace_6207250
  have hstable : (prefixWord ++ tailWord_6207250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207250).length < 2 ^ (prefixWord ++ tailWord_6207250).sum := by decide
  have hdescent : baseEnd_6207250 < baseStart_6207250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207253 : List Nat := [1, 3, 2, 1, 2, 3, 3, 1, 1, 2, 4]
def baseStart_6207253 : Nat := 118140960795 + 6207253 * 2 ^ 59
def prefixEnd_6207253 : Nat := 4983230072969 + 3 ^ 40 * 6207253 * 2
def baseEnd_6207253 : Nat := 3187304333062907827790869

theorem tailTrace_6207253 : CollatzResearch.WordTrace tailWord_6207253 prefixEnd_6207253 3187304333062907827790869 := by
  unfold tailWord_6207253
  simp only [CollatzResearch.WordTrace]
  refine ⟨226397116181189970257490413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150931410787459980171660275 226397116181189970257490413)
  ·
    refine ⟨84898918567946238846558905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226397116181189970257490413 84898918567946238846558905)
    ·
      refine ⟨63674188925959679134919179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84898918567946238846558905 63674188925959679134919179)
      ·
        refine ⟨95511283388939518702378769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63674188925959679134919179 95511283388939518702378769)
        ·
          refine ⟨71633462541704639026784077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95511283388939518702378769 71633462541704639026784077)
          ·
            refine ⟨26862548453139239635044029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71633462541704639026784077 26862548453139239635044029)
            ·
              refine ⟨10073455669927214863141511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26862548453139239635044029 10073455669927214863141511)
              ·
                refine ⟨15110183504890822294712267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10073455669927214863141511 15110183504890822294712267)
                ·
                  refine ⟨22665275257336233442068401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15110183504890822294712267 22665275257336233442068401)
                  ·
                    refine ⟨16998956443002175081551301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22665275257336233442068401 16998956443002175081551301)
                    ·
                      refine ⟨3187304333062907827790869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16998956443002175081551301 3187304333062907827790869)
                      ·
                        rfl

theorem cell23_6207253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_6207253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207253 prefixEnd_6207253 := by exact prefixLift 6207253
  have htrace : WordTrace (prefixWord ++ tailWord_6207253) baseStart_6207253 baseEnd_6207253 := by
    simpa [prefixWord, tailWord_6207253, baseEnd_6207253] using wordTrace_append hprefix tailTrace_6207253
  have hstable : (prefixWord ++ tailWord_6207253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207253).length < 2 ^ (prefixWord ++ tailWord_6207253).sum := by decide
  have hdescent : baseEnd_6207253 < baseStart_6207253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207260 : List Nat := [2, 2, 3, 1, 1, 2, 4, 2, 1, 2, 3]
def baseStart_6207260 : Nat := 118140960795 + 6207260 * 2 ^ 59
def prefixEnd_6207260 : Nat := 4983230072969 + 3 ^ 40 * 6207260 * 2
def baseEnd_6207260 : Nat := 3187307927427489300403337

theorem tailTrace_6207260 : CollatzResearch.WordTrace tailWord_6207260 prefixEnd_6207260 3187307927427489300403337 := by
  unfold tailWord_6207260
  simp only [CollatzResearch.WordTrace]
  refine ⟨113198685746082305226497617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150931580994776406968663489 113198685746082305226497617)
  ·
    refine ⟨84899014309561728919873213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113198685746082305226497617 84899014309561728919873213)
    ·
      refine ⟨31837130366085648344952455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84899014309561728919873213 31837130366085648344952455)
      ·
        refine ⟨47755695549128472517428683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31837130366085648344952455 47755695549128472517428683)
        ·
          refine ⟨71633543323692708776143025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47755695549128472517428683 71633543323692708776143025)
          ·
            refine ⟨53725157492769531582107269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71633543323692708776143025 53725157492769531582107269)
            ·
              refine ⟨10073467029894287171645113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53725157492769531582107269 10073467029894287171645113)
              ·
                refine ⟨7555100272420715378733835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10073467029894287171645113 7555100272420715378733835)
                ·
                  refine ⟨11332650408631073068100753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7555100272420715378733835 11332650408631073068100753)
                  ·
                    refine ⟨8499487806473304801075565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11332650408631073068100753 8499487806473304801075565)
                    ·
                      refine ⟨3187307927427489300403337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8499487806473304801075565 3187307927427489300403337)
                      ·
                        rfl

theorem cell23_6207260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_6207260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207260 prefixEnd_6207260 := by exact prefixLift 6207260
  have htrace : WordTrace (prefixWord ++ tailWord_6207260) baseStart_6207260 baseEnd_6207260 := by
    simpa [prefixWord, tailWord_6207260, baseEnd_6207260] using wordTrace_append hprefix tailTrace_6207260
  have hstable : (prefixWord ++ tailWord_6207260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207260).length < 2 ^ (prefixWord ++ tailWord_6207260).sum := by decide
  have hdescent : baseEnd_6207260 < baseStart_6207260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207290 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3]
def baseStart_6207290 : Nat := 118140960795 + 6207290 * 2 ^ 59
def prefixEnd_6207290 : Nat := 4983230072969 + 3 ^ 40 * 6207290 * 2
def baseEnd_6207290 : Nat := 3187323331847124183028199

theorem tailTrace_6207290 : CollatzResearch.WordTrace tailWord_6207290 prefixEnd_6207290 3187323331847124183028199 := by
  unfold tailWord_6207290
  simp only [CollatzResearch.WordTrace]
  refine ⟨56599616420513981394146831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150932310454703950384391549 56599616420513981394146831)
  ·
    refine ⟨84899424630770972091220247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56599616420513981394146831 84899424630770972091220247)
    ·
      refine ⟨127349136946156458136830371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84899424630770972091220247 127349136946156458136830371)
      ·
        refine ⟨191023705419234687205245557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127349136946156458136830371 191023705419234687205245557)
        ·
          refine ⟨17908472383053251925491771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191023705419234687205245557 17908472383053251925491771)
          ·
            refine ⟨26862708574579877888237657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17908472383053251925491771 26862708574579877888237657)
            ·
              refine ⟨20147031430934908416178243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26862708574579877888237657 20147031430934908416178243)
              ·
                refine ⟨30220547146402362624267365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20147031430934908416178243 30220547146402362624267365)
                ·
                  refine ⟨5666352589950442992050131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30220547146402362624267365 5666352589950442992050131)
                  ·
                    refine ⟨8499528884925664488075197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5666352589950442992050131 8499528884925664488075197)
                    ·
                      refine ⟨3187323331847124183028199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8499528884925664488075197 3187323331847124183028199)
                      ·
                        rfl

theorem cell23_6207290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3].length) (baseStart_6207290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207290 prefixEnd_6207290 := by exact prefixLift 6207290
  have htrace : WordTrace (prefixWord ++ tailWord_6207290) baseStart_6207290 baseEnd_6207290 := by
    simpa [prefixWord, tailWord_6207290, baseEnd_6207290] using wordTrace_append hprefix tailTrace_6207290
  have hstable : (prefixWord ++ tailWord_6207290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207290).length < 2 ^ (prefixWord ++ tailWord_6207290).sum := by decide
  have hdescent : baseEnd_6207290 < baseStart_6207290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207306 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 1, 8]
def baseStart_6207306 : Nat := 118140960795 + 6207306 * 2 ^ 59
def prefixEnd_6207306 : Nat := 4983230072969 + 3 ^ 40 * 6207306 * 2
def baseEnd_6207306 : Nat := 1062443849179198706809375

theorem tailTrace_6207306 : CollatzResearch.WordTrace tailWord_6207306 prefixEnd_6207306 1062443849179198706809375 := by
  unfold tailWord_6207306
  simp only [CollatzResearch.WordTrace]
  refine ⟨56599762312499490077292443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150932699499998640206113181 56599762312499490077292443)
  ·
    refine ⟨84899643468749235115938665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56599762312499490077292443 84899643468749235115938665)
    ·
      refine ⟨63674732601561926336953999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84899643468749235115938665 63674732601561926336953999)
      ·
        refine ⟨95512098902342889505430999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63674732601561926336953999 95512098902342889505430999)
        ·
          refine ⟨143268148353514334258146499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95512098902342889505430999 143268148353514334258146499)
          ·
            refine ⟨214902222530271501387219749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143268148353514334258146499 214902222530271501387219749)
            ·
              refine ⟨40294166724425906510103703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 214902222530271501387219749 40294166724425906510103703)
              ·
                refine ⟨60441250086638859765155555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40294166724425906510103703 60441250086638859765155555)
                ·
                  refine ⟨90661875129958289647733333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60441250086638859765155555 90661875129958289647733333)
                  ·
                    refine ⟨1062443849179198706809375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90661875129958289647733333 1062443849179198706809375)
                    ·
                      rfl

theorem cell23_6207306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_6207306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207306 prefixEnd_6207306 := by exact prefixLift 6207306
  have htrace : WordTrace (prefixWord ++ tailWord_6207306) baseStart_6207306 baseEnd_6207306 := by
    simpa [prefixWord, tailWord_6207306, baseEnd_6207306] using wordTrace_append hprefix tailTrace_6207306
  have hstable : (prefixWord ++ tailWord_6207306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207306).length < 2 ^ (prefixWord ++ tailWord_6207306).sum := by decide
  have hdescent : baseEnd_6207306 < baseStart_6207306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207317 : List Nat := [1, 3, 2, 2, 2, 2, 3, 2, 1, 3, 2]
def baseStart_6207317 : Nat := 118140960795 + 6207317 * 2 ^ 59
def prefixEnd_6207317 : Nat := 4983230072969 + 3 ^ 40 * 6207317 * 2
def baseEnd_6207317 : Nat := 3187337195824795577390575

theorem tailTrace_6207317 : CollatzResearch.WordTrace tailWord_6207317 prefixEnd_6207317 3187337195824795577390575 := by
  unfold tailWord_6207317
  simp only [CollatzResearch.WordTrace]
  refine ⟨226399450452958109187820205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150932966968638739458546803 226399450452958109187820205)
  ·
    refine ⟨84899793919859290945432577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226399450452958109187820205 84899793919859290945432577)
    ·
      refine ⟨63674845439894468209074433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84899793919859290945432577 63674845439894468209074433)
      ·
        refine ⟨47756134079920851156805825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63674845439894468209074433 47756134079920851156805825)
        ·
          refine ⟨35817100559940638367604369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47756134079920851156805825 35817100559940638367604369)
          ·
            refine ⟨26862825419955478775703277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35817100559940638367604369 26862825419955478775703277)
            ·
              refine ⟨10073559532483304540888729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26862825419955478775703277 10073559532483304540888729)
              ·
                refine ⟨7555169649362478405666547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10073559532483304540888729 7555169649362478405666547)
                ·
                  refine ⟨11332754474043717608499821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7555169649362478405666547 11332754474043717608499821)
                  ·
                    refine ⟨4249782927766394103187433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11332754474043717608499821 4249782927766394103187433)
                    ·
                      refine ⟨3187337195824795577390575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4249782927766394103187433 3187337195824795577390575)
                      ·
                        rfl

theorem cell23_6207317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_6207317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207317 prefixEnd_6207317 := by exact prefixLift 6207317
  have htrace : WordTrace (prefixWord ++ tailWord_6207317) baseStart_6207317 baseEnd_6207317 := by
    simpa [prefixWord, tailWord_6207317, baseEnd_6207317] using wordTrace_append hprefix tailTrace_6207317
  have hstable : (prefixWord ++ tailWord_6207317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207317).length < 2 ^ (prefixWord ++ tailWord_6207317).sum := by decide
  have hdescent : baseEnd_6207317 < baseStart_6207317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207356 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_6207356 : Nat := 118140960795 + 6207356 * 2 ^ 59
def prefixEnd_6207356 : Nat := 4983230072969 + 3 ^ 40 * 6207356 * 2
def baseEnd_6207356 : Nat := 3187357221570320924802895

theorem tailTrace_6207356 : CollatzResearch.WordTrace tailWord_6207356 prefixEnd_6207356 3187357221570320924802895 := by
  unfold tailWord_6207356
  simp only [CollatzResearch.WordTrace]
  refine ⟨113200436449908409424244961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150933915266544545898993281 113200436449908409424244961)
  ·
    refine ⟨84900327337431307068183721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113200436449908409424244961 84900327337431307068183721)
    ·
      refine ⟨63675245503073480301137791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84900327337431307068183721 63675245503073480301137791)
      ·
        refine ⟨95512868254610220451706687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63675245503073480301137791 95512868254610220451706687)
        ·
          refine ⟨143269302381915330677560031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95512868254610220451706687 143269302381915330677560031)
          ·
            refine ⟨214903953572872996016340047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143269302381915330677560031 214903953572872996016340047)
            ·
              refine ⟨322355930359309494024510071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214903953572872996016340047 322355930359309494024510071)
              ·
                refine ⟨483533895538964241036765107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322355930359309494024510071 483533895538964241036765107)
                ·
                  refine ⟨725300843308446361555147661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 483533895538964241036765107 725300843308446361555147661)
                  ·
                    refine ⟨271987816240667385583180373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 725300843308446361555147661 271987816240667385583180373)
                    ·
                      refine ⟨3187357221570320924802895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 271987816240667385583180373 3187357221570320924802895)
                      ·
                        rfl

theorem cell23_6207356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_6207356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207356 prefixEnd_6207356 := by exact prefixLift 6207356
  have htrace : WordTrace (prefixWord ++ tailWord_6207356) baseStart_6207356 baseEnd_6207356 := by
    simpa [prefixWord, tailWord_6207356, baseEnd_6207356] using wordTrace_append hprefix tailTrace_6207356
  have hstable : (prefixWord ++ tailWord_6207356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207356).length < 2 ^ (prefixWord ++ tailWord_6207356).sum := by decide
  have hdescent : baseEnd_6207356 < baseStart_6207356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207363 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 3]
def baseStart_6207363 : Nat := 118140960795 + 6207363 * 2 ^ 59
def prefixEnd_6207363 : Nat := 4983230072969 + 3 ^ 40 * 6207363 * 2
def baseEnd_6207363 : Nat := 3187360815934902397415363

theorem tailTrace_6207363 : CollatzResearch.WordTrace tailWord_6207363 prefixEnd_6207363 3187360815934902397415363 := by
  unfold tailWord_6207363
  simp only [CollatzResearch.WordTrace]
  refine ⟨226401128210791459043994743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150934085473860972695996495 226401128210791459043994743)
  ·
    refine ⟨339601692316187188565992115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226401128210791459043994743 339601692316187188565992115)
    ·
      refine ⟨509402538474280782848988173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339601692316187188565992115 509402538474280782848988173)
      ·
        refine ⟨191025951927855293568370565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 509402538474280782848988173 191025951927855293568370565)
        ·
          refine ⟨35817365986472867544069481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191025951927855293568370565 35817365986472867544069481)
          ·
            refine ⟨26863024489854650658052111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35817365986472867544069481 26863024489854650658052111)
            ·
              refine ⟨40294536734781975987078167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26863024489854650658052111 40294536734781975987078167)
              ·
                refine ⟨60441805102172963980617251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40294536734781975987078167 60441805102172963980617251)
                ·
                  refine ⟨90662707653259445970925877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60441805102172963980617251 90662707653259445970925877)
                  ·
                    refine ⟨8499628842493073059774301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90662707653259445970925877 8499628842493073059774301)
                    ·
                      refine ⟨3187360815934902397415363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8499628842493073059774301 3187360815934902397415363)
                      ·
                        rfl

theorem cell23_6207363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_6207363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207363 prefixEnd_6207363 := by exact prefixLift 6207363
  have htrace : WordTrace (prefixWord ++ tailWord_6207363) baseStart_6207363 baseEnd_6207363 := by
    simpa [prefixWord, tailWord_6207363, baseEnd_6207363] using wordTrace_append hprefix tailTrace_6207363
  have hstable : (prefixWord ++ tailWord_6207363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207363).length < 2 ^ (prefixWord ++ tailWord_6207363).sum := by decide
  have hdescent : baseEnd_6207363 < baseStart_6207363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207370 : List Nat := [3, 1, 2, 4, 2, 1, 1, 2, 7]
def baseStart_6207370 : Nat := 118140960795 + 6207370 * 2 ^ 59
def prefixEnd_6207370 : Nat := 4983230072969 + 3 ^ 40 * 6207370 * 2
def baseEnd_6207370 : Nat := 354151601144387096669759

theorem tailTrace_6207370 : CollatzResearch.WordTrace tailWord_6207370 prefixEnd_6207370 354151601144387096669759 := by
  unfold tailWord_6207370
  simp only [CollatzResearch.WordTrace]
  refine ⟨56600345880441524809874891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150934255681177399492999709 56600345880441524809874891)
  ·
    refine ⟨84900518820662287214812337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56600345880441524809874891 84900518820662287214812337)
    ·
      refine ⟨63675389115496715411109253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84900518820662287214812337 63675389115496715411109253)
      ·
        refine ⟨11939135459155634139582985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63675389115496715411109253 11939135459155634139582985)
        ·
          refine ⟨8954351594366725604687239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11939135459155634139582985 8954351594366725604687239)
          ·
            refine ⟨13431527391550088407030859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8954351594366725604687239 13431527391550088407030859)
            ·
              refine ⟨20147291087325132610546289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13431527391550088407030859 20147291087325132610546289)
              ·
                refine ⟨15110468315493849457909717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20147291087325132610546289 15110468315493849457909717)
                ·
                  refine ⟨354151601144387096669759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15110468315493849457909717 354151601144387096669759)
                  ·
                    rfl

theorem cell23_6207370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 7].length) (baseStart_6207370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207370 prefixEnd_6207370 := by exact prefixLift 6207370
  have htrace : WordTrace (prefixWord ++ tailWord_6207370) baseStart_6207370 baseEnd_6207370 := by
    simpa [prefixWord, tailWord_6207370, baseEnd_6207370] using wordTrace_append hprefix tailTrace_6207370
  have hstable : (prefixWord ++ tailWord_6207370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207370).length < 2 ^ (prefixWord ++ tailWord_6207370).sum := by decide
  have hdescent : baseEnd_6207370 < baseStart_6207370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207376 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 7]
def baseStart_6207376 : Nat := 118140960795 + 6207376 * 2 ^ 59
def prefixEnd_6207376 : Nat := 4983230072969 + 3 ^ 40 * 6207376 * 2
def baseEnd_6207376 : Nat := 3187367491183410846552803

theorem tailTrace_6207376 : CollatzResearch.WordTrace tailWord_6207376 prefixEnd_6207376 3187367491183410846552803 := by
  unfold tailWord_6207376
  simp only [CollatzResearch.WordTrace]
  refine ⟨113200801179872181132108991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150934401573162908176145321 113200801179872181132108991)
  ·
    refine ⟨169801201769808271698163487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113200801179872181132108991 169801201769808271698163487)
    ·
      refine ⟨254701802654712407547245231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169801201769808271698163487 254701802654712407547245231)
      ·
        refine ⟨382052703982068611320867847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254701802654712407547245231 382052703982068611320867847)
        ·
          refine ⟨573079055973102916981301771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382052703982068611320867847 573079055973102916981301771)
          ·
            refine ⟨859618583959654375471952657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573079055973102916981301771 859618583959654375471952657)
            ·
              refine ⟨644713937969740781603964493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 859618583959654375471952657 644713937969740781603964493)
              ·
                refine ⟨241767726738652793101486685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 644713937969740781603964493 241767726738652793101486685)
                ·
                  refine ⟨90662897526994797413057507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241767726738652793101486685 90662897526994797413057507)
                  ·
                    refine ⟨135994346290492196119586261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90662897526994797413057507 135994346290492196119586261)
                    ·
                      refine ⟨3187367491183410846552803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 135994346290492196119586261 3187367491183410846552803)
                      ·
                        rfl

theorem cell23_6207376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_6207376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207376 prefixEnd_6207376 := by exact prefixLift 6207376
  have htrace : WordTrace (prefixWord ++ tailWord_6207376) baseStart_6207376 baseEnd_6207376 := by
    simpa [prefixWord, tailWord_6207376, baseEnd_6207376] using wordTrace_append hprefix tailTrace_6207376
  have hstable : (prefixWord ++ tailWord_6207376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207376).length < 2 ^ (prefixWord ++ tailWord_6207376).sum := by decide
  have hdescent : baseEnd_6207376 < baseStart_6207376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207383 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 1, 7]
def baseStart_6207383 : Nat := 118140960795 + 6207383 * 2 ^ 59
def prefixEnd_6207383 : Nat := 4983230072969 + 3 ^ 40 * 6207383 * 2
def baseEnd_6207383 : Nat := 1062457028515997439721757

theorem tailTrace_6207383 : CollatzResearch.WordTrace tailWord_6207383 prefixEnd_6207383 1062457028515997439721757 := by
  unfold tailWord_6207383
  simp only [CollatzResearch.WordTrace]
  refine ⟨226401857670719002459722803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150934571780479334973148535 226401857670719002459722803)
  ·
    refine ⟨339602786506078503689584205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226401857670719002459722803 339602786506078503689584205)
    ·
      refine ⟨127351044939779438883594077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339602786506078503689584205 127351044939779438883594077)
      ·
        refine ⟨47756641852417289581347779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127351044939779438883594077 47756641852417289581347779)
        ·
          refine ⟨71634962778625934372021669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47756641852417289581347779 71634962778625934372021669)
          ·
            refine ⟨13431555520992362694754063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71634962778625934372021669 13431555520992362694754063)
            ·
              refine ⟨20147333281488544042131095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13431555520992362694754063 20147333281488544042131095)
              ·
                refine ⟨30220999922232816063196643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20147333281488544042131095 30220999922232816063196643)
                ·
                  refine ⟨45331499883349224094794965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30220999922232816063196643 45331499883349224094794965)
                  ·
                    refine ⟨1062457028515997439721757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45331499883349224094794965 1062457028515997439721757)
                    ·
                      rfl

theorem cell23_6207383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_6207383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207383 prefixEnd_6207383 := by exact prefixLift 6207383
  have htrace : WordTrace (prefixWord ++ tailWord_6207383) baseStart_6207383 baseEnd_6207383 := by
    simpa [prefixWord, tailWord_6207383, baseEnd_6207383] using wordTrace_append hprefix tailTrace_6207383
  have hstable : (prefixWord ++ tailWord_6207383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207383).length < 2 ^ (prefixWord ++ tailWord_6207383).sum := by decide
  have hdescent : baseEnd_6207383 < baseStart_6207383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207423 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 3]
def baseStart_6207423 : Nat := 118140960795 + 6207423 * 2 ^ 59
def prefixEnd_6207423 : Nat := 4983230072969 + 3 ^ 40 * 6207423 * 2
def baseEnd_6207423 : Nat := 3187391624774172162665087

theorem tailTrace_6207423 : CollatzResearch.WordTrace tailWord_6207423 prefixEnd_6207423 3187391624774172162665087 := by
  unfold tailWord_6207423
  simp only [CollatzResearch.WordTrace]
  refine ⟨226403316590574089291178923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150935544393716059527452615 226403316590574089291178923)
  ·
    refine ⟨339604974885861133936768385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226403316590574089291178923 339604974885861133936768385)
    ·
      refine ⟨254703731164395850452576289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339604974885861133936768385 254703731164395850452576289)
      ·
        refine ⟨191027798373296887839432217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254703731164395850452576289 191027798373296887839432217)
        ·
          refine ⟨143270848779972665879574163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191027798373296887839432217 143270848779972665879574163)
          ·
            refine ⟨214906273169958998819361245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143270848779972665879574163 214906273169958998819361245)
            ·
              refine ⟨80589852438734624557260467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214906273169958998819361245 80589852438734624557260467)
              ·
                refine ⟨120884778658101936835890701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80589852438734624557260467 120884778658101936835890701)
                ·
                  refine ⟨45331791996788226313459013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120884778658101936835890701 45331791996788226313459013)
                  ·
                    refine ⟨8499710999397792433773565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45331791996788226313459013 8499710999397792433773565)
                    ·
                      refine ⟨3187391624774172162665087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8499710999397792433773565 3187391624774172162665087)
                      ·
                        rfl

theorem cell23_6207423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_6207423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207423 prefixEnd_6207423 := by exact prefixLift 6207423
  have htrace : WordTrace (prefixWord ++ tailWord_6207423) baseStart_6207423 baseEnd_6207423 := by
    simpa [prefixWord, tailWord_6207423, baseEnd_6207423] using wordTrace_append hprefix tailTrace_6207423
  have hstable : (prefixWord ++ tailWord_6207423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207423).length < 2 ^ (prefixWord ++ tailWord_6207423).sum := by decide
  have hdescent : baseEnd_6207423 < baseStart_6207423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207480 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 3, 5, 2]
def baseStart_6207480 : Nat := 118140960795 + 6207480 * 2 ^ 59
def prefixEnd_6207480 : Nat := 4983230072969 + 3 ^ 40 * 6207480 * 2
def baseEnd_6207480 : Nat := 3187420893171478439652325

theorem tailTrace_6207480 : CollatzResearch.WordTrace tailWord_6207480 prefixEnd_6207480 3187420893171478439652325 := by
  unfold tailWord_6207480
  simp only [CollatzResearch.WordTrace]
  refine ⟨113202697775683794013001947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150936930367578392017335929 113202697775683794013001947)
  ·
    refine ⟨169804046663525691019502921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113202697775683794013001947 169804046663525691019502921)
    ·
      refine ⟨127353034997644268264627191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169804046663525691019502921 127353034997644268264627191)
      ·
        refine ⟨191029552496466402396940787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127353034997644268264627191 191029552496466402396940787)
        ·
          refine ⟨286544328744699603595411181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191029552496466402396940787 286544328744699603595411181)
          ·
            refine ⟨107454123279262351348279193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286544328744699603595411181 107454123279262351348279193)
            ·
              refine ⟨80590592459446763511209395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107454123279262351348279193 80590592459446763511209395)
              ·
                refine ⟨120885888689170145266814093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80590592459446763511209395 120885888689170145266814093)
                ·
                  refine ⟨45332208258438804475055285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 120885888689170145266814093 45332208258438804475055285)
                  ·
                    refine ⟨4249894524228637919536433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45332208258438804475055285 4249894524228637919536433)
                    ·
                      refine ⟨3187420893171478439652325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4249894524228637919536433 3187420893171478439652325)
                      ·
                        rfl

theorem cell23_6207480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 3, 5, 2].length) (baseStart_6207480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207480 prefixEnd_6207480 := by exact prefixLift 6207480
  have htrace : WordTrace (prefixWord ++ tailWord_6207480) baseStart_6207480 baseEnd_6207480 := by
    simpa [prefixWord, tailWord_6207480, baseEnd_6207480] using wordTrace_append hprefix tailTrace_6207480
  have hstable : (prefixWord ++ tailWord_6207480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207480).length < 2 ^ (prefixWord ++ tailWord_6207480).sum := by decide
  have hdescent : baseEnd_6207480 < baseStart_6207480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207521 : List Nat := [1, 2, 3, 2, 4, 1, 1, 4, 1, 1, 3]
def baseStart_6207521 : Nat := 118140960795 + 6207521 * 2 ^ 59
def prefixEnd_6207521 : Nat := 4983230072969 + 3 ^ 40 * 6207521 * 2
def baseEnd_6207521 : Nat := 3187441945878312779239637

theorem tailTrace_6207521 : CollatzResearch.WordTrace tailWord_6207521 prefixEnd_6207521 3187441945878312779239637 := by
  unfold tailWord_6207521
  simp only [CollatzResearch.WordTrace]
  refine ⟨226406890944219052028246417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150937927296146034685497611 226406890944219052028246417)
  ·
    refine ⟨169805168208164289021184813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226406890944219052028246417 169805168208164289021184813)
    ·
      refine ⟨63676938078061608382944305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169805168208164289021184813 63676938078061608382944305)
      ·
        refine ⟨47757703558546206287208229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63676938078061608382944305 47757703558546206287208229)
        ·
          refine ⟨8954569417227413678851543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47757703558546206287208229 8954569417227413678851543)
          ·
            refine ⟨13431854125841120518277315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8954569417227413678851543 13431854125841120518277315)
            ·
              refine ⟨20147781188761680777415973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13431854125841120518277315 20147781188761680777415973)
              ·
                refine ⟨3777708972892815145765495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20147781188761680777415973 3777708972892815145765495)
                ·
                  refine ⟨5666563459339222718648243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3777708972892815145765495 5666563459339222718648243)
                  ·
                    refine ⟨8499845189008834077972365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5666563459339222718648243 8499845189008834077972365)
                    ·
                      refine ⟨3187441945878312779239637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8499845189008834077972365 3187441945878312779239637)
                      ·
                        rfl

theorem cell23_6207521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_6207521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207521 prefixEnd_6207521 := by exact prefixLift 6207521
  have htrace : WordTrace (prefixWord ++ tailWord_6207521) baseStart_6207521 baseEnd_6207521 := by
    simpa [prefixWord, tailWord_6207521, baseEnd_6207521] using wordTrace_append hprefix tailTrace_6207521
  have hstable : (prefixWord ++ tailWord_6207521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207521).length < 2 ^ (prefixWord ++ tailWord_6207521).sum := by decide
  have hdescent : baseEnd_6207521 < baseStart_6207521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207537 : List Nat := [1, 2, 2, 3, 1, 3, 2, 3, 2, 4]
def baseStart_6207537 : Nat := 118140960795 + 6207537 * 2 ^ 59
def prefixEnd_6207537 : Nat := 4983230072969 + 3 ^ 40 * 6207537 * 2
def baseEnd_6207537 : Nat := 1062483387189594905546521

theorem tailTrace_6207537 : CollatzResearch.WordTrace tailWord_6207537 prefixEnd_6207537 1062483387189594905546521 := by
  unfold tailWord_6207537
  simp only [CollatzResearch.WordTrace]
  refine ⟨226407474512161086760828865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150938316341440724507219243 226407474512161086760828865)
  ·
    refine ⟨169805605884120815070621649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226407474512161086760828865 169805605884120815070621649)
    ·
      refine ⟨127354204413090611302966237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169805605884120815070621649 127354204413090611302966237)
      ·
        refine ⟨47757826654908979238612339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127354204413090611302966237 47757826654908979238612339)
        ·
          refine ⟨71636739982363468857918509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47757826654908979238612339 71636739982363468857918509)
          ·
            refine ⟨26863777493386300821719441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71636739982363468857918509 26863777493386300821719441)
            ·
              refine ⟨20147833120039725616289581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26863777493386300821719441 20147833120039725616289581)
              ·
                refine ⟨7555437420014897106108593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20147833120039725616289581 7555437420014897106108593)
                ·
                  refine ⟨5666578065011172829581445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7555437420014897106108593 5666578065011172829581445)
                  ·
                    refine ⟨1062483387189594905546521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5666578065011172829581445 1062483387189594905546521)
                    ·
                      rfl

theorem cell23_6207537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 4].length) (baseStart_6207537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207537 prefixEnd_6207537 := by exact prefixLift 6207537
  have htrace : WordTrace (prefixWord ++ tailWord_6207537) baseStart_6207537 baseEnd_6207537 := by
    simpa [prefixWord, tailWord_6207537, baseEnd_6207537] using wordTrace_append hprefix tailTrace_6207537
  have hstable : (prefixWord ++ tailWord_6207537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207537).length < 2 ^ (prefixWord ++ tailWord_6207537).sum := by decide
  have hdescent : baseEnd_6207537 < baseStart_6207537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207560 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 3, 3, 3]
def baseStart_6207560 : Nat := 118140960795 + 6207560 * 2 ^ 59
def prefixEnd_6207560 : Nat := 4983230072969 + 3 ^ 40 * 6207560 * 2
def baseEnd_6207560 : Nat := 3187461971623838126651957

theorem tailTrace_6207560 : CollatzResearch.WordTrace tailWord_6207560 prefixEnd_6207560 3187461971623838126651957 := by
  unfold tailWord_6207560
  simp only [CollatzResearch.WordTrace]
  refine ⟨113204156695538880844458067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150938875594051841125944089 113204156695538880844458067)
  ·
    refine ⟨169806235043308321266687101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113204156695538880844458067 169806235043308321266687101)
    ·
      refine ⟨63677338141240620475007663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169806235043308321266687101 63677338141240620475007663)
      ·
        refine ⟨95516007211860930712511495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63677338141240620475007663 95516007211860930712511495)
        ·
          refine ⟨143274010817791396068767243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95516007211860930712511495 143274010817791396068767243)
          ·
            refine ⟨214911016226687094103150865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143274010817791396068767243 214911016226687094103150865)
            ·
              refine ⟨161183262170015320577363149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214911016226687094103150865 161183262170015320577363149)
              ·
                refine ⟨60443723313755745216511181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161183262170015320577363149 60443723313755745216511181)
                ·
                  refine ⟨22666396242658404456191693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60443723313755745216511181 22666396242658404456191693)
                  ·
                    refine ⟨8499898590996901671071885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22666396242658404456191693 8499898590996901671071885)
                    ·
                      refine ⟨3187461971623838126651957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8499898590996901671071885 3187461971623838126651957)
                      ·
                        rfl

theorem cell23_6207560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_6207560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207560 prefixEnd_6207560 := by exact prefixLift 6207560
  have htrace : WordTrace (prefixWord ++ tailWord_6207560) baseStart_6207560 baseEnd_6207560 := by
    simpa [prefixWord, tailWord_6207560, baseEnd_6207560] using wordTrace_append hprefix tailTrace_6207560
  have hstable : (prefixWord ++ tailWord_6207560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207560).length < 2 ^ (prefixWord ++ tailWord_6207560).sum := by decide
  have hdescent : baseEnd_6207560 < baseStart_6207560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207561 : List Nat := [1, 2, 1, 1, 2, 2, 6, 3, 1, 2, 2]
def baseStart_6207561 : Nat := 118140960795 + 6207561 * 2 ^ 59
def prefixEnd_6207561 : Nat := 4983230072969 + 3 ^ 40 * 6207561 * 2
def baseEnd_6207561 : Nat := 3187462485104492622739453

theorem tailTrace_6207561 : CollatzResearch.WordTrace tailWord_6207561 prefixEnd_6207561 3187462485104492622739453 := by
  unfold tailWord_6207561
  simp only [CollatzResearch.WordTrace]
  refine ⟨226408349864074138859702537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150938899909382759239801691 226408349864074138859702537)
  ·
    refine ⟨169806262398055604144776903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226408349864074138859702537 169806262398055604144776903)
    ·
      refine ⟨254709393597083406217165355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169806262398055604144776903 254709393597083406217165355)
      ·
        refine ⟨382064090395625109325748033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254709393597083406217165355 382064090395625109325748033)
        ·
          refine ⟨286548067796718831994311025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382064090395625109325748033 286548067796718831994311025)
          ·
            refine ⟨214911050847539123995733269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286548067796718831994311025 214911050847539123995733269)
            ·
              refine ⟨10073955508478396437299997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 214911050847539123995733269 10073955508478396437299997)
              ·
                refine ⟨3777733315679398663987499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10073955508478396437299997 3777733315679398663987499)
                ·
                  refine ⟨5666599973519097995981249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3777733315679398663987499 5666599973519097995981249)
                  ·
                    refine ⟨4249949980139323496985937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5666599973519097995981249 4249949980139323496985937)
                    ·
                      refine ⟨3187462485104492622739453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4249949980139323496985937 3187462485104492622739453)
                      ·
                        rfl

theorem cell23_6207561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 1, 2, 2].length) (baseStart_6207561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207561 prefixEnd_6207561 := by exact prefixLift 6207561
  have htrace : WordTrace (prefixWord ++ tailWord_6207561) baseStart_6207561 baseEnd_6207561 := by
    simpa [prefixWord, tailWord_6207561, baseEnd_6207561] using wordTrace_append hprefix tailTrace_6207561
  have hstable : (prefixWord ++ tailWord_6207561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207561).length < 2 ^ (prefixWord ++ tailWord_6207561).sum := by decide
  have hdescent : baseEnd_6207561 < baseStart_6207561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207563 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 4, 7]
def baseStart_6207563 : Nat := 118140960795 + 6207563 * 2 ^ 59
def prefixEnd_6207563 : Nat := 4983230072969 + 3 ^ 40 * 6207563 * 2
def baseEnd_6207563 : Nat := 1062487837355267204971481

theorem tailTrace_6207563 : CollatzResearch.WordTrace tailWord_6207563 prefixEnd_6207563 1062487837355267204971481 := by
  unfold tailWord_6207563
  simp only [CollatzResearch.WordTrace]
  refine ⟨226408422810066893201275343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150938948540044595467516895 226408422810066893201275343)
  ·
    refine ⟨339612634215100339801913015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226408422810066893201275343 339612634215100339801913015)
    ·
      refine ⟨509418951322650509702869523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339612634215100339801913015 509418951322650509702869523)
      ·
        refine ⟨764128426983975764554304285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509418951322650509702869523 764128426983975764554304285)
        ·
          refine ⟨286548160118990911707864107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 764128426983975764554304285 286548160118990911707864107)
          ·
            refine ⟨429822240178486367561796161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286548160118990911707864107 429822240178486367561796161)
            ·
              refine ⟨322366680133864775671347121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429822240178486367561796161 322366680133864775671347121)
              ·
                refine ⟨241775010100398581753510341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322366680133864775671347121 241775010100398581753510341)
                ·
                  refine ⟨45332814393824734078783189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 241775010100398581753510341 45332814393824734078783189)
                  ·
                    refine ⟨1062487837355267204971481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45332814393824734078783189 1062487837355267204971481)
                    ·
                      rfl

theorem cell23_6207563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 7].length) (baseStart_6207563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207563 prefixEnd_6207563 := by exact prefixLift 6207563
  have htrace : WordTrace (prefixWord ++ tailWord_6207563) baseStart_6207563 baseEnd_6207563 := by
    simpa [prefixWord, tailWord_6207563, baseEnd_6207563] using wordTrace_append hprefix tailTrace_6207563
  have hstable : (prefixWord ++ tailWord_6207563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207563).length < 2 ^ (prefixWord ++ tailWord_6207563).sum := by decide
  have hdescent : baseEnd_6207563 < baseStart_6207563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207564 : List Nat := [2, 2, 1, 3, 1, 1, 6, 1, 1, 2, 3]
def baseStart_6207564 : Nat := 118140960795 + 6207564 * 2 ^ 59
def prefixEnd_6207564 : Nat := 4983230072969 + 3 ^ 40 * 6207564 * 2
def baseEnd_6207564 : Nat := 3187464025546456111001939

theorem tailTrace_6207564 : CollatzResearch.WordTrace tailWord_6207564 prefixEnd_6207564 3187464025546456111001939 := by
  unfold tailWord_6207564
  simp only [CollatzResearch.WordTrace]
  refine ⟨113204229641531635186030873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150938972855375513581374497 113204229641531635186030873)
  ·
    refine ⟨84903172231148726389523155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113204229641531635186030873 84903172231148726389523155)
    ·
      refine ⟨127354758346723089584284733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84903172231148726389523155 127354758346723089584284733)
      ·
        refine ⟨47758034380021158594106775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127354758346723089584284733 47758034380021158594106775)
        ·
          refine ⟨71637051570031737891160163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47758034380021158594106775 71637051570031737891160163)
          ·
            refine ⟨107455577355047606836740245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71637051570031737891160163 107455577355047606836740245)
            ·
              refine ⟨5036980188517856570472199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 107455577355047606836740245 5036980188517856570472199)
              ·
                refine ⟨7555470282776784855708299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5036980188517856570472199 7555470282776784855708299)
                ·
                  refine ⟨11333205424165177283562449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7555470282776784855708299 11333205424165177283562449)
                  ·
                    refine ⟨8499904068123882962671837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11333205424165177283562449 8499904068123882962671837)
                    ·
                      refine ⟨3187464025546456111001939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8499904068123882962671837 3187464025546456111001939)
                      ·
                        rfl

theorem cell23_6207564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_6207564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207564 prefixEnd_6207564 := by exact prefixLift 6207564
  have htrace : WordTrace (prefixWord ++ tailWord_6207564) baseStart_6207564 baseEnd_6207564 := by
    simpa [prefixWord, tailWord_6207564, baseEnd_6207564] using wordTrace_append hprefix tailTrace_6207564
  have hstable : (prefixWord ++ tailWord_6207564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207564).length < 2 ^ (prefixWord ++ tailWord_6207564).sum := by decide
  have hdescent : baseEnd_6207564 < baseStart_6207564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207577 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 4, 1, 3]
def baseStart_6207577 : Nat := 118140960795 + 6207577 * 2 ^ 59
def prefixEnd_6207577 : Nat := 4983230072969 + 3 ^ 40 * 6207577 * 2
def baseEnd_6207577 : Nat := 3187470700794964560139379

theorem tailTrace_6207577 : CollatzResearch.WordTrace tailWord_6207577 prefixEnd_6207577 3187470700794964560139379 := by
  unfold tailWord_6207577
  simp only [CollatzResearch.WordTrace]
  refine ⟨226408933432016173592284985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150939288954677449061523323 226408933432016173592284985)
  ·
    refine ⟨169806700074012130194213739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226408933432016173592284985 169806700074012130194213739)
    ·
      refine ⟨254710050111018195291320609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169806700074012130194213739 254710050111018195291320609)
      ·
        refine ⟨191032537583263646468490457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254710050111018195291320609 191032537583263646468490457)
        ·
          refine ⟨143274403187447734851367843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191032537583263646468490457 143274403187447734851367843)
          ·
            refine ⟨214911604781171602277051765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143274403187447734851367843 214911604781171602277051765)
            ·
              refine ⟨20147962948234837713473603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 214911604781171602277051765 20147962948234837713473603)
              ·
                refine ⟨30221944422352256570210405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20147962948234837713473603 30221944422352256570210405)
                ·
                  refine ⟨5666614579191048106914451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30221944422352256570210405 5666614579191048106914451)
                  ·
                    refine ⟨8499921868786572160371677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5666614579191048106914451 8499921868786572160371677)
                    ·
                      refine ⟨3187470700794964560139379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8499921868786572160371677 3187470700794964560139379)
                      ·
                        rfl

theorem cell23_6207577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 1, 3].length) (baseStart_6207577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207577 prefixEnd_6207577 := by exact prefixLift 6207577
  have htrace : WordTrace (prefixWord ++ tailWord_6207577) baseStart_6207577 baseEnd_6207577 := by
    simpa [prefixWord, tailWord_6207577, baseEnd_6207577] using wordTrace_append hprefix tailTrace_6207577
  have hstable : (prefixWord ++ tailWord_6207577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207577).length < 2 ^ (prefixWord ++ tailWord_6207577).sum := by decide
  have hdescent : baseEnd_6207577 < baseStart_6207577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207587 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 5, 3, 2]
def baseStart_6207587 : Nat := 118140960795 + 6207587 * 2 ^ 59
def prefixEnd_6207587 : Nat := 4983230072969 + 3 ^ 40 * 6207587 * 2
def baseEnd_6207587 : Nat := 3187475835601509521014333

theorem tailTrace_6207587 : CollatzResearch.WordTrace tailWord_6207587 prefixEnd_6207587 3187475835601509521014333 := by
  unfold tailWord_6207587
  simp only [CollatzResearch.WordTrace]
  refine ⟨226409298161979945300149015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150939532107986630200099343 226409298161979945300149015)
  ·
    refine ⟨339613947242969917950223523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226409298161979945300149015 339613947242969917950223523)
    ·
      refine ⟨509420920864454876925335285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339613947242969917950223523 509420920864454876925335285)
      ·
        refine ⟨47758211331042644711750183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 509420920864454876925335285 47758211331042644711750183)
        ·
          refine ⟨71637316996563967067625275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47758211331042644711750183 71637316996563967067625275)
          ·
            refine ⟨107455975494845950601437913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71637316996563967067625275 107455975494845950601437913)
            ·
              refine ⟨80591981621134462951078435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107455975494845950601437913 80591981621134462951078435)
              ·
                refine ⟨120887972431701694426617653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80591981621134462951078435 120887972431701694426617653)
                ·
                  refine ⟨11333247415472033852495405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120887972431701694426617653 11333247415472033852495405)
                  ·
                    refine ⟨4249967780802012694685777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11333247415472033852495405 4249967780802012694685777)
                    ·
                      refine ⟨3187475835601509521014333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4249967780802012694685777 3187475835601509521014333)
                      ·
                        rfl

theorem cell23_6207587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_6207587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207587 prefixEnd_6207587 := by exact prefixLift 6207587
  have htrace : WordTrace (prefixWord ++ tailWord_6207587) baseStart_6207587 baseEnd_6207587 := by
    simpa [prefixWord, tailWord_6207587, baseEnd_6207587] using wordTrace_append hprefix tailTrace_6207587
  have hstable : (prefixWord ++ tailWord_6207587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207587).length < 2 ^ (prefixWord ++ tailWord_6207587).sum := by decide
  have hdescent : baseEnd_6207587 < baseStart_6207587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207655 : List Nat := [1, 1, 6, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_6207655 : Nat := 118140960795 + 6207655 * 2 ^ 59
def prefixEnd_6207655 : Nat := 4983230072969 + 3 ^ 40 * 6207655 * 2
def baseEnd_6207655 : Nat := 3187510752286015254964021

theorem tailTrace_6207655 : CollatzResearch.WordTrace tailWord_6207655 prefixEnd_6207655 3187510752286015254964021 := by
  unfold tailWord_6207655
  simp only [CollatzResearch.WordTrace]
  refine ⟨226411778325733592913624419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150941185550489061942416279 226411778325733592913624419)
  ·
    refine ⟨339617667488600389370436629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226411778325733592913624419 339617667488600389370436629)
    ·
      refine ⟨15919578163528143251739217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 339617667488600389370436629 15919578163528143251739217)
      ·
        refine ⟨11939683622646107438804413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15919578163528143251739217 11939683622646107438804413)
        ·
          refine ⟨4477381358492290289551655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11939683622646107438804413 4477381358492290289551655)
          ·
            refine ⟨6716072037738435434327483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4477381358492290289551655 6716072037738435434327483)
            ·
              refine ⟨10074108056607653151491225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6716072037738435434327483 10074108056607653151491225)
              ·
                refine ⟨7555581042455739863618419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10074108056607653151491225 7555581042455739863618419)
                ·
                  refine ⟨11333371563683609795427629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7555581042455739863618419 11333371563683609795427629)
                  ·
                    refine ⟨4250014336381353673285361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11333371563683609795427629 4250014336381353673285361)
                    ·
                      refine ⟨3187510752286015254964021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4250014336381353673285361 3187510752286015254964021)
                      ·
                        rfl

theorem cell23_6207655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_6207655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207655 prefixEnd_6207655 := by exact prefixLift 6207655
  have htrace : WordTrace (prefixWord ++ tailWord_6207655) baseStart_6207655 baseEnd_6207655 := by
    simpa [prefixWord, tailWord_6207655, baseEnd_6207655] using wordTrace_append hprefix tailTrace_6207655
  have hstable : (prefixWord ++ tailWord_6207655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207655).length < 2 ^ (prefixWord ++ tailWord_6207655).sum := by decide
  have hdescent : baseEnd_6207655 < baseStart_6207655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207694 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2]
def baseStart_6207694 : Nat := 118140960795 + 6207694 * 2 ^ 59
def prefixEnd_6207694 : Nat := 4983230072969 + 3 ^ 40 * 6207694 * 2
def baseEnd_6207694 : Nat := 3187530778031540602376341

theorem tailTrace_6207694 : CollatzResearch.WordTrace tailWord_6207694 prefixEnd_6207694 3187530778031540602376341 := by
  unfold tailWord_6207694
  simp only [CollatzResearch.WordTrace]
  refine ⟨28301650096574037821786767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150942133848394868382862757 28301650096574037821786767)
  ·
    refine ⟨42452475144861056732680151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28301650096574037821786767 42452475144861056732680151)
    ·
      refine ⟨63678712717291585099020227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42452475144861056732680151 63678712717291585099020227)
      ·
        refine ⟨95518069075937377648530341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63678712717291585099020227 95518069075937377648530341)
        ·
          refine ⟨17909637951738258309099439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95518069075937377648530341 17909637951738258309099439)
          ·
            refine ⟨26864456927607387463649159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17909637951738258309099439 26864456927607387463649159)
            ·
              refine ⟨40296685391411081195473739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26864456927607387463649159 40296685391411081195473739)
              ·
                refine ⟨60445028087116621793210609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40296685391411081195473739 60445028087116621793210609)
                ·
                  refine ⟨45333771065337466344907957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60445028087116621793210609 45333771065337466344907957)
                  ·
                    refine ⟨4250041037375387469835121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45333771065337466344907957 4250041037375387469835121)
                    ·
                      refine ⟨3187530778031540602376341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4250041037375387469835121 3187530778031540602376341)
                      ·
                        rfl

theorem cell23_6207694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_6207694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207694 prefixEnd_6207694 := by exact prefixLift 6207694
  have htrace : WordTrace (prefixWord ++ tailWord_6207694) baseStart_6207694 baseEnd_6207694 := by
    simpa [prefixWord, tailWord_6207694, baseEnd_6207694] using wordTrace_append hprefix tailTrace_6207694
  have hstable : (prefixWord ++ tailWord_6207694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207694).length < 2 ^ (prefixWord ++ tailWord_6207694).sum := by decide
  have hdescent : baseEnd_6207694 < baseStart_6207694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207707 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 1, 6, 2]
def baseStart_6207707 : Nat := 118140960795 + 6207707 * 2 ^ 59
def prefixEnd_6207707 : Nat := 4983230072969 + 3 ^ 40 * 6207707 * 2
def baseEnd_6207707 : Nat := 3187537453280049051513781

theorem tailTrace_6207707 : CollatzResearch.WordTrace tailWord_6207707 prefixEnd_6207707 3187537453280049051513781 := by
  unfold tailWord_6207707
  simp only [CollatzResearch.WordTrace]
  refine ⟨226413674921545205794517375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150942449947696803863011583 226413674921545205794517375)
  ·
    refine ⟨339620512382317808691776063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226413674921545205794517375 339620512382317808691776063)
    ·
      refine ⟨509430768573476713037664095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339620512382317808691776063 509430768573476713037664095)
      ·
        refine ⟨764146152860215069556496143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509430768573476713037664095 764146152860215069556496143)
        ·
          refine ⟨1146219229290322604334744215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764146152860215069556496143 1146219229290322604334744215)
          ·
            refine ⟨1719328843935483906502116323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1146219229290322604334744215 1719328843935483906502116323)
            ·
              refine ⟨2578993265903225859753174485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1719328843935483906502116323 2578993265903225859753174485)
              ·
                refine ⟨60445154669606856087965027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2578993265903225859753174485 60445154669606856087965027)
                ·
                  refine ⟨90667732004410284131947541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60445154669606856087965027 90667732004410284131947541)
                  ·
                    refine ⟨4250049937706732068685041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 90667732004410284131947541 4250049937706732068685041)
                    ·
                      refine ⟨3187537453280049051513781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4250049937706732068685041 3187537453280049051513781)
                      ·
                        rfl

theorem cell23_6207707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 6, 2].length) (baseStart_6207707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207707 prefixEnd_6207707 := by exact prefixLift 6207707
  have htrace : WordTrace (prefixWord ++ tailWord_6207707) baseStart_6207707 baseEnd_6207707 := by
    simpa [prefixWord, tailWord_6207707, baseEnd_6207707] using wordTrace_append hprefix tailTrace_6207707
  have hstable : (prefixWord ++ tailWord_6207707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207707).length < 2 ^ (prefixWord ++ tailWord_6207707).sum := by decide
  have hdescent : baseEnd_6207707 < baseStart_6207707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207777 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 3, 5]
def baseStart_6207777 : Nat := 118140960795 + 6207777 * 2 ^ 59
def prefixEnd_6207777 : Nat := 4983230072969 + 3 ^ 40 * 6207777 * 2
def baseEnd_6207777 : Nat := 1062524465641954592546153

theorem tailTrace_6207777 : CollatzResearch.WordTrace tailWord_6207777 prefixEnd_6207777 1062524465641954592546153 := by
  unfold tailWord_6207777
  simp only [CollatzResearch.WordTrace]
  refine ⟨226416228031291607749565585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150944152020861071833043723 226416228031291607749565585)
  ·
    refine ⟨169812171023468705812174189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226416228031291607749565585 169812171023468705812174189)
    ·
      refine ⟨63679564133800764679565321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169812171023468705812174189 63679564133800764679565321)
      ·
        refine ⟨47759673100350573509673991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63679564133800764679565321 47759673100350573509673991)
        ·
          refine ⟨71639509650525860264510987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47759673100350573509673991 71639509650525860264510987)
          ·
            refine ⟨107459264475788790396766481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71639509650525860264510987 107459264475788790396766481)
            ·
              refine ⟨80594448356841592797574861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107459264475788790396766481 80594448356841592797574861)
              ·
                refine ⟨30222918133815597299090573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80594448356841592797574861 30222918133815597299090573)
                ·
                  refine ⟨11333594300180848987158965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30222918133815597299090573 11333594300180848987158965)
                  ·
                    refine ⟨1062524465641954592546153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11333594300180848987158965 1062524465641954592546153)
                    ·
                      rfl

theorem cell23_6207777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_6207777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207777 prefixEnd_6207777 := by exact prefixLift 6207777
  have htrace : WordTrace (prefixWord ++ tailWord_6207777) baseStart_6207777 baseEnd_6207777 := by
    simpa [prefixWord, tailWord_6207777, baseEnd_6207777] using wordTrace_append hprefix tailTrace_6207777
  have hstable : (prefixWord ++ tailWord_6207777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207777).length < 2 ^ (prefixWord ++ tailWord_6207777).sum := by decide
  have hdescent : baseEnd_6207777 < baseStart_6207777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207801 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 4, 3, 2]
def baseStart_6207801 : Nat := 118140960795 + 6207801 * 2 ^ 59
def prefixEnd_6207801 : Nat := 4983230072969 + 3 ^ 40 * 6207801 * 2
def baseEnd_6207801 : Nat := 3187585720461571683738349

theorem tailTrace_6207801 : CollatzResearch.WordTrace tailWord_6207801 prefixEnd_6207801 3187585720461571683738349 := by
  unfold tailWord_6207801
  simp only [CollatzResearch.WordTrace]
  refine ⟨226417103383204659848439257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150944735588803106565626171 226417103383204659848439257)
  ·
    refine ⟨169812827537403494886329443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226417103383204659848439257 169812827537403494886329443)
    ·
      refine ⟨254719241306105242329494165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169812827537403494886329443 254719241306105242329494165)
      ·
        refine ⟨11939964436223683234195039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 254719241306105242329494165 11939964436223683234195039)
        ·
          refine ⟨17909946654335524851292559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11939964436223683234195039 17909946654335524851292559)
          ·
            refine ⟨26864919981503287276938839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17909946654335524851292559 26864919981503287276938839)
            ·
              refine ⟨40297379972254930915408259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26864919981503287276938839 40297379972254930915408259)
              ·
                refine ⟨60446069958382396373112389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40297379972254930915408259 60446069958382396373112389)
                ·
                  refine ⟨11333638117196699319958573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60446069958382396373112389 11333638117196699319958573)
                  ·
                    refine ⟨4250114293948762244984465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11333638117196699319958573 4250114293948762244984465)
                    ·
                      refine ⟨3187585720461571683738349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4250114293948762244984465 3187585720461571683738349)
                      ·
                        rfl

theorem cell23_6207801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_6207801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207801 prefixEnd_6207801 := by exact prefixLift 6207801
  have htrace : WordTrace (prefixWord ++ tailWord_6207801) baseStart_6207801 baseEnd_6207801 := by
    simpa [prefixWord, tailWord_6207801, baseEnd_6207801] using wordTrace_append hprefix tailTrace_6207801
  have hstable : (prefixWord ++ tailWord_6207801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207801).length < 2 ^ (prefixWord ++ tailWord_6207801).sum := by decide
  have hdescent : baseEnd_6207801 < baseStart_6207801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207817 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 2, 6, 3]
def baseStart_6207817 : Nat := 118140960795 + 6207817 * 2 ^ 59
def prefixEnd_6207817 : Nat := 4983230072969 + 3 ^ 40 * 6207817 * 2
def baseEnd_6207817 : Nat := 3187593936152043621138275

theorem tailTrace_6207817 : CollatzResearch.WordTrace tailWord_6207817 prefixEnd_6207817 3187593936152043621138275 := by
  unfold tailWord_6207817
  simp only [CollatzResearch.WordTrace]
  refine ⟨226417686951146694581021705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150945124634097796387347803 226417686951146694581021705)
  ·
    refine ⟨169813265213360020935766279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226417686951146694581021705 169813265213360020935766279)
    ·
      refine ⟨254719897820040031403649419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169813265213360020935766279 254719897820040031403649419)
      ·
        refine ⟨382079846730060047105474129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254719897820040031403649419 382079846730060047105474129)
        ·
          refine ⟨286559885047545035329105597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382079846730060047105474129 286559885047545035329105597)
          ·
            refine ⟨107459956892829388248414599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 286559885047545035329105597 107459956892829388248414599)
            ·
              refine ⟨161189935339244082372621899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107459956892829388248414599 161189935339244082372621899)
              ·
                refine ⟨241784903008866123558932849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161189935339244082372621899 241784903008866123558932849)
                ·
                  refine ⟨181338677256649592669199637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241784903008866123558932849 181338677256649592669199637)
                  ·
                    refine ⟨8500250496405449656368733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 181338677256649592669199637 8500250496405449656368733)
                    ·
                      refine ⟨3187593936152043621138275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8500250496405449656368733 3187593936152043621138275)
                      ·
                        rfl

theorem cell23_6207817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 6, 3].length) (baseStart_6207817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207817 prefixEnd_6207817 := by exact prefixLift 6207817
  have htrace : WordTrace (prefixWord ++ tailWord_6207817) baseStart_6207817 baseEnd_6207817 := by
    simpa [prefixWord, tailWord_6207817, baseEnd_6207817] using wordTrace_append hprefix tailTrace_6207817
  have hstable : (prefixWord ++ tailWord_6207817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207817).length < 2 ^ (prefixWord ++ tailWord_6207817).sum := by decide
  have hdescent : baseEnd_6207817 < baseStart_6207817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207831 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 5, 2, 2]
def baseStart_6207831 : Nat := 118140960795 + 6207831 * 2 ^ 59
def prefixEnd_6207831 : Nat := 4983230072969 + 3 ^ 40 * 6207831 * 2
def baseEnd_6207831 : Nat := 3187601124881206566363211

theorem tailTrace_6207831 : CollatzResearch.WordTrace tailWord_6207831 prefixEnd_6207831 3187601124881206566363211 := by
  unfold tailWord_6207831
  simp only [CollatzResearch.WordTrace]
  refine ⟨226418197573095974972031347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150945465048730649981354231 226418197573095974972031347)
  ·
    refine ⟨339627296359643962458047021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226418197573095974972031347 339627296359643962458047021)
    ·
      refine ⟨127360236134866485921767633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339627296359643962458047021 127360236134866485921767633)
      ·
        refine ⟨95520177101149864441325725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127360236134866485921767633 95520177101149864441325725)
        ·
          refine ⟨35820066412931199165497147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95520177101149864441325725 35820066412931199165497147)
          ·
            refine ⟨53730099619396798748245721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35820066412931199165497147 53730099619396798748245721)
            ·
              refine ⟨40297574714547599061184291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53730099619396798748245721 40297574714547599061184291)
              ·
                refine ⟨60446362071821398591776437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40297574714547599061184291 60446362071821398591776437)
                ·
                  refine ⟨5666846444233256117979041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60446362071821398591776437 5666846444233256117979041)
                  ·
                    refine ⟨4250134833174942088484281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5666846444233256117979041 4250134833174942088484281)
                    ·
                      refine ⟨3187601124881206566363211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4250134833174942088484281 3187601124881206566363211)
                      ·
                        rfl

theorem cell23_6207831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_6207831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207831 prefixEnd_6207831 := by exact prefixLift 6207831
  have htrace : WordTrace (prefixWord ++ tailWord_6207831) baseStart_6207831 baseEnd_6207831 := by
    simpa [prefixWord, tailWord_6207831, baseEnd_6207831] using wordTrace_append hprefix tailTrace_6207831
  have hstable : (prefixWord ++ tailWord_6207831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207831).length < 2 ^ (prefixWord ++ tailWord_6207831).sum := by decide
  have hdescent : baseEnd_6207831 < baseStart_6207831 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207844 : List Nat := [2, 3, 1, 1, 3, 1, 3, 2, 1, 2, 4]
def baseStart_6207844 : Nat := 118140960795 + 6207844 * 2 ^ 59
def prefixEnd_6207844 : Nat := 4983230072969 + 3 ^ 40 * 6207844 * 2
def baseEnd_6207844 : Nat := 3187607800129715015500651

theorem tailTrace_6207844 : CollatzResearch.WordTrace tailWord_6207844 prefixEnd_6207844 3187607800129715015500651 := by
  unfold tailWord_6207844
  simp only [CollatzResearch.WordTrace]
  refine ⟨113209335861024439096127293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150945781148032585461503057 113209335861024439096127293)
  ·
    refine ⟨42453500947884164661047735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113209335861024439096127293 42453500947884164661047735)
    ·
      refine ⟨63680251421826246991571603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42453500947884164661047735 63680251421826246991571603)
      ·
        refine ⟨95520377132739370487357405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63680251421826246991571603 95520377132739370487357405)
        ·
          refine ⟨35820141424777263932759027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95520377132739370487357405 35820141424777263932759027)
          ·
            refine ⟨53730212137165895899138541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35820141424777263932759027 53730212137165895899138541)
            ·
              refine ⟨20148829551437210962176953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53730212137165895899138541 20148829551437210962176953)
              ·
                refine ⟨15111622163577908221632715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20148829551437210962176953 15111622163577908221632715)
                ·
                  refine ⟨22667433245366862332449073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15111622163577908221632715 22667433245366862332449073)
                  ·
                    refine ⟨17000574934025146749336805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22667433245366862332449073 17000574934025146749336805)
                    ·
                      refine ⟨3187607800129715015500651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17000574934025146749336805 3187607800129715015500651)
                      ·
                        rfl

theorem cell23_6207844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_6207844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207844 prefixEnd_6207844 := by exact prefixLift 6207844
  have htrace : WordTrace (prefixWord ++ tailWord_6207844) baseStart_6207844 baseEnd_6207844 := by
    simpa [prefixWord, tailWord_6207844, baseEnd_6207844] using wordTrace_append hprefix tailTrace_6207844
  have hstable : (prefixWord ++ tailWord_6207844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207844).length < 2 ^ (prefixWord ++ tailWord_6207844).sum := by decide
  have hdescent : baseEnd_6207844 < baseStart_6207844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207848 : List Nat := [2, 1, 4, 2, 2, 2, 3, 1, 1, 1, 4]
def baseStart_6207848 : Nat := 118140960795 + 6207848 * 2 ^ 59
def prefixEnd_6207848 : Nat := 4983230072969 + 3 ^ 40 * 6207848 * 2
def baseEnd_6207848 : Nat := 3187609854052332999850633

theorem tailTrace_6207848 : CollatzResearch.WordTrace tailWord_6207848 prefixEnd_6207848 3187609854052332999850633 := by
  unfold tailWord_6207848
  simp only [CollatzResearch.WordTrace]
  refine ⟨113209408807017193437700099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150945878409356257916933465 113209408807017193437700099)
  ·
    refine ⟨169814113210525790156550149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113209408807017193437700099 169814113210525790156550149)
    ·
      refine ⟨31840146226973585654353153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169814113210525790156550149 31840146226973585654353153)
      ·
        refine ⟨23880109670230189240764865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31840146226973585654353153 23880109670230189240764865)
        ·
          refine ⟨17910082252672641930573649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23880109670230189240764865 17910082252672641930573649)
          ·
            refine ⟨13432561689504481447930237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17910082252672641930573649 13432561689504481447930237)
            ·
              refine ⟨5037210633564180542973839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13432561689504481447930237 5037210633564180542973839)
              ·
                refine ⟨7555815950346270814460759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5037210633564180542973839 7555815950346270814460759)
                ·
                  refine ⟨11333723925519406221691139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7555815950346270814460759 11333723925519406221691139)
                  ·
                    refine ⟨17000585888279109332536709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11333723925519406221691139 17000585888279109332536709)
                    ·
                      refine ⟨3187609854052332999850633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17000585888279109332536709 3187609854052332999850633)
                      ·
                        rfl

theorem cell23_6207848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_6207848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207848 prefixEnd_6207848 := by exact prefixLift 6207848
  have htrace : WordTrace (prefixWord ++ tailWord_6207848) baseStart_6207848 baseEnd_6207848 := by
    simpa [prefixWord, tailWord_6207848, baseEnd_6207848] using wordTrace_append hprefix tailTrace_6207848
  have hstable : (prefixWord ++ tailWord_6207848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207848).length < 2 ^ (prefixWord ++ tailWord_6207848).sum := by decide
  have hdescent : baseEnd_6207848 < baseStart_6207848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207867 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 2, 7]
def baseStart_6207867 : Nat := 118140960795 + 6207867 * 2 ^ 59
def prefixEnd_6207867 : Nat := 4983230072969 + 3 ^ 40 * 6207867 * 2
def baseEnd_6207867 : Nat := 1062539870061589475171015

theorem tailTrace_6207867 : CollatzResearch.WordTrace tailWord_6207867 prefixEnd_6207867 1062539870061589475171015 := by
  unfold tailWord_6207867
  simp only [CollatzResearch.WordTrace]
  refine ⟨226419510600965553120341855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150946340400643702080227903 226419510600965553120341855)
  ·
    refine ⟨339629265901448329680512783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226419510600965553120341855 339629265901448329680512783)
    ·
      refine ⟨509443898852172494520769175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339629265901448329680512783 509443898852172494520769175)
      ·
        refine ⟨764165848278258741781153763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509443898852172494520769175 764165848278258741781153763)
        ·
          refine ⟨1146248772417388112671730645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764165848278258741781153763 1146248772417388112671730645)
          ·
            refine ⟨26865205603532533890743687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1146248772417388112671730645 26865205603532533890743687)
            ·
              refine ⟨40297808405298800836115531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26865205603532533890743687 40297808405298800836115531)
              ·
                refine ⟨60446712607948201254173297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40297808405298800836115531 60446712607948201254173297)
                ·
                  refine ⟨45335034455961150940629973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60446712607948201254173297 45335034455961150940629973)
                  ·
                    refine ⟨1062539870061589475171015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45335034455961150940629973 1062539870061589475171015)
                    ·
                      rfl

theorem cell23_6207867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 7].length) (baseStart_6207867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207867 prefixEnd_6207867 := by exact prefixLift 6207867
  have htrace : WordTrace (prefixWord ++ tailWord_6207867) baseStart_6207867 baseEnd_6207867 := by
    simpa [prefixWord, tailWord_6207867, baseEnd_6207867] using wordTrace_append hprefix tailTrace_6207867
  have hstable : (prefixWord ++ tailWord_6207867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207867).length < 2 ^ (prefixWord ++ tailWord_6207867).sum := by decide
  have hdescent : baseEnd_6207867 < baseStart_6207867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207877 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 1, 4, 5]
def baseStart_6207877 : Nat := 118140960795 + 6207877 * 2 ^ 59
def prefixEnd_6207877 : Nat := 4983230072969 + 3 ^ 40 * 6207877 * 2
def baseEnd_6207877 : Nat := 3187624744991313386387999

theorem tailTrace_6207877 : CollatzResearch.WordTrace tailWord_6207877 prefixEnd_6207877 3187624744991313386387999 := by
  unfold tailWord_6207877
  simp only [CollatzResearch.WordTrace]
  refine ⟨226419875330929324828205885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150946583553952883218803923 226419875330929324828205885)
  ·
    refine ⟨84907453249098496810577207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226419875330929324828205885 84907453249098496810577207)
    ·
      refine ⟨127361179873647745215865811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84907453249098496810577207 127361179873647745215865811)
      ·
        refine ⟨191041769810471617823798717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127361179873647745215865811 191041769810471617823798717)
        ·
          refine ⟨71640663678926856683924519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191041769810471617823798717 71640663678926856683924519)
          ·
            refine ⟨107460995518390285025886779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71640663678926856683924519 107460995518390285025886779)
            ·
              refine ⟨161191493277585427538830169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107460995518390285025886779 161191493277585427538830169)
              ·
                refine ⟨120893619958189070654122627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161191493277585427538830169 120893619958189070654122627)
                ·
                  refine ⟨181340429937283605981183941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120893619958189070654122627 181340429937283605981183941)
                  ·
                    refine ⟨34001330613240676121471989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 181340429937283605981183941 34001330613240676121471989)
                    ·
                      refine ⟨3187624744991313386387999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34001330613240676121471989 3187624744991313386387999)
                      ·
                        rfl

theorem cell23_6207877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_6207877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207877 prefixEnd_6207877 := by exact prefixLift 6207877
  have htrace : WordTrace (prefixWord ++ tailWord_6207877) baseStart_6207877 baseEnd_6207877 := by
    simpa [prefixWord, tailWord_6207877, baseEnd_6207877] using wordTrace_append hprefix tailTrace_6207877
  have hstable : (prefixWord ++ tailWord_6207877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207877).length < 2 ^ (prefixWord ++ tailWord_6207877).sum := by decide
  have hdescent : baseEnd_6207877 < baseStart_6207877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207881 : List Nat := [1, 2, 1, 1, 6, 2, 2, 1, 1, 3, 3]
def baseStart_6207881 : Nat := 118140960795 + 6207881 * 2 ^ 59
def prefixEnd_6207881 : Nat := 4983230072969 + 3 ^ 40 * 6207881 * 2
def baseEnd_6207881 : Nat := 3187626798913931370737981

theorem tailTrace_6207881 : CollatzResearch.WordTrace tailWord_6207881 prefixEnd_6207881 3187626798913931370737981 := by
  unfold tailWord_6207881
  simp only [CollatzResearch.WordTrace]
  refine ⟨226420021222914833511351497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150946680815276555674234331 226420021222914833511351497)
  ·
    refine ⟨169815015917186125133513623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226420021222914833511351497 169815015917186125133513623)
    ·
      refine ⟨254722523875779187700270435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169815015917186125133513623 254722523875779187700270435)
      ·
        refine ⟨382083785813668781550405653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254722523875779187700270435 382083785813668781550405653)
        ·
          refine ⟨17910177460015724135175265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 382083785813668781550405653 17910177460015724135175265)
          ·
            refine ⟨13432633095011793101381449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17910177460015724135175265 13432633095011793101381449)
            ·
              refine ⟨10074474821258844826036087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13432633095011793101381449 10074474821258844826036087)
              ·
                refine ⟨15111712231888267239054131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10074474821258844826036087 15111712231888267239054131)
                ·
                  refine ⟨22667568347832400858581197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15111712231888267239054131 22667568347832400858581197)
                  ·
                    refine ⟨8500338130437150321967949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22667568347832400858581197 8500338130437150321967949)
                    ·
                      refine ⟨3187626798913931370737981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8500338130437150321967949 3187626798913931370737981)
                      ·
                        rfl

theorem cell23_6207881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 3, 3].length) (baseStart_6207881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207881 prefixEnd_6207881 := by exact prefixLift 6207881
  have htrace : WordTrace (prefixWord ++ tailWord_6207881) baseStart_6207881 baseEnd_6207881 := by
    simpa [prefixWord, tailWord_6207881, baseEnd_6207881] using wordTrace_append hprefix tailTrace_6207881
  have hstable : (prefixWord ++ tailWord_6207881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207881).length < 2 ^ (prefixWord ++ tailWord_6207881).sum := by decide
  have hdescent : baseEnd_6207881 < baseStart_6207881 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207897 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 1, 8]
def baseStart_6207897 : Nat := 118140960795 + 6207897 * 2 ^ 59
def prefixEnd_6207897 : Nat := 4983230072969 + 3 ^ 40 * 6207897 * 2
def baseEnd_6207897 : Nat := 1062545004868134436045969

theorem tailTrace_6207897 : CollatzResearch.WordTrace tailWord_6207897 prefixEnd_6207897 1062545004868134436045969 := by
  unfold tailWord_6207897
  simp only [CollatzResearch.WordTrace]
  refine ⟨226420604790856868243933945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150947069860571245495955963 226420604790856868243933945)
  ·
    refine ⟨169815453593142651182950459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226420604790856868243933945 169815453593142651182950459)
    ·
      refine ⟨254723180389713976774425689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169815453593142651182950459 254723180389713976774425689)
      ·
        refine ⟨191042385292285482580819267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254723180389713976774425689 191042385292285482580819267)
        ·
          refine ⟨286563577938428223871228901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191042385292285482580819267 286563577938428223871228901)
          ·
            refine ⟨53730670863455291975855419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 286563577938428223871228901 53730670863455291975855419)
            ·
              refine ⟨80596006295182937963783129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53730670863455291975855419 80596006295182937963783129)
              ·
                refine ⟨60447004721387203472837347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80596006295182937963783129 60447004721387203472837347)
                ·
                  refine ⟨90670507082080805209256021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60447004721387203472837347 90670507082080805209256021)
                  ·
                    refine ⟨1062545004868134436045969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 90670507082080805209256021 1062545004868134436045969)
                    ·
                      rfl

theorem cell23_6207897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 8].length) (baseStart_6207897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207897 prefixEnd_6207897 := by exact prefixLift 6207897
  have htrace : WordTrace (prefixWord ++ tailWord_6207897) baseStart_6207897 baseEnd_6207897 := by
    simpa [prefixWord, tailWord_6207897, baseEnd_6207897] using wordTrace_append hprefix tailTrace_6207897
  have hstable : (prefixWord ++ tailWord_6207897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207897).length < 2 ^ (prefixWord ++ tailWord_6207897).sum := by decide
  have hdescent : baseEnd_6207897 < baseStart_6207897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207902 : List Nat := [4, 3, 1, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_6207902 : Nat := 118140960795 + 6207902 * 2 ^ 59
def prefixEnd_6207902 : Nat := 4983230072969 + 3 ^ 40 * 6207902 * 2
def baseEnd_6207902 : Nat := 3187637582007675788575385

theorem tailTrace_6207902 : CollatzResearch.WordTrace tailWord_6207902 prefixEnd_6207902 3187637582007675788575385 := by
  unfold tailWord_6207902
  simp only [CollatzResearch.WordTrace]
  refine ⟨28302598394479844262233245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150947191437225836065243973 28302598394479844262233245)
  ·
    refine ⟨10613474397929941598337467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28302598394479844262233245 10613474397929941598337467)
    ·
      refine ⟨15920211596894912397506201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10613474397929941598337467 15920211596894912397506201)
      ·
        refine ⟨11940158697671184298129651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15920211596894912397506201 11940158697671184298129651)
        ·
          refine ⟨17910238046506776447194477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11940158697671184298129651 17910238046506776447194477)
          ·
            refine ⟨6716339267440041167697929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17910238046506776447194477 6716339267440041167697929)
            ·
              refine ⟨5037254450580030875773447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6716339267440041167697929 5037254450580030875773447)
              ·
                refine ⟨7555881675870046313660171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5037254450580030875773447 7555881675870046313660171)
                ·
                  refine ⟨11333822513805069470490257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7555881675870046313660171 11333822513805069470490257)
                  ·
                    refine ⟨8500366885353802102867693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11333822513805069470490257 8500366885353802102867693)
                    ·
                      refine ⟨3187637582007675788575385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8500366885353802102867693 3187637582007675788575385)
                      ·
                        rfl

theorem cell23_6207902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_6207902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207902 prefixEnd_6207902 := by exact prefixLift 6207902
  have htrace : WordTrace (prefixWord ++ tailWord_6207902) baseStart_6207902 baseEnd_6207902 := by
    simpa [prefixWord, tailWord_6207902, baseEnd_6207902] using wordTrace_append hprefix tailTrace_6207902
  have hstable : (prefixWord ++ tailWord_6207902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207902).length < 2 ^ (prefixWord ++ tailWord_6207902).sum := by decide
  have hdescent : baseEnd_6207902 < baseStart_6207902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207944 : List Nat := [2, 1, 3, 1, 3, 2, 2, 2, 7]
def baseStart_6207944 : Nat := 118140960795 + 6207944 * 2 ^ 59
def prefixEnd_6207944 : Nat := 4983230072969 + 3 ^ 40 * 6207944 * 2
def baseEnd_6207944 : Nat := 354184349799462736027799

theorem tailTrace_6207944 : CollatzResearch.WordTrace tailWord_6207944 prefixEnd_6207944 354184349799462736027799 := by
  unfold tailWord_6207944
  simp only [CollatzResearch.WordTrace]
  refine ⟨113211159510843297635447443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150948212681124396847263257 113211159510843297635447443)
  ·
    refine ⟨169816739266264946453171165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113211159510843297635447443 169816739266264946453171165)
    ·
      refine ⟨63681277224849354919939187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169816739266264946453171165 63681277224849354919939187)
      ·
        refine ⟨95521915837274032379908781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63681277224849354919939187 95521915837274032379908781)
        ·
          refine ⟨35820718438977762142465793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95521915837274032379908781 35820718438977762142465793)
          ·
            refine ⟨26865538829233321606849345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35820718438977762142465793 26865538829233321606849345)
            ·
              refine ⟨20149154121924991205137009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26865538829233321606849345 20149154121924991205137009)
              ·
                refine ⟨15111865591443743403852757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20149154121924991205137009 15111865591443743403852757)
                ·
                  refine ⟨354184349799462736027799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15111865591443743403852757 354184349799462736027799)
                  ·
                    rfl

theorem cell23_6207944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 7].length) (baseStart_6207944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207944 prefixEnd_6207944 := by exact prefixLift 6207944
  have htrace : WordTrace (prefixWord ++ tailWord_6207944) baseStart_6207944 baseEnd_6207944 := by
    simpa [prefixWord, tailWord_6207944, baseEnd_6207944] using wordTrace_append hprefix tailTrace_6207944
  have hstable : (prefixWord ++ tailWord_6207944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207944).length < 2 ^ (prefixWord ++ tailWord_6207944).sum := by decide
  have hdescent : baseEnd_6207944 < baseStart_6207944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207984 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 5]
def baseStart_6207984 : Nat := 118140960795 + 6207984 * 2 ^ 59
def prefixEnd_6207984 : Nat := 4983230072969 + 3 ^ 40 * 6207984 * 2
def baseEnd_6207984 : Nat := 3187679687421344467750007

theorem tailTrace_6207984 : CollatzResearch.WordTrace tailWord_6207984 prefixEnd_6207984 3187679687421344467750007 := by
  unfold tailWord_6207984
  simp only [CollatzResearch.WordTrace]
  refine ⟨113211888970770841051175503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150949185294361121401567337 113211888970770841051175503)
  ·
    refine ⟨169817833456156261576763255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113211888970770841051175503 169817833456156261576763255)
    ·
      refine ⟨254726750184234392365144883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169817833456156261576763255 254726750184234392365144883)
      ·
        refine ⟨382090125276351588547717325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254726750184234392365144883 382090125276351588547717325)
        ·
          refine ⟨143283796978631845705393997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382090125276351588547717325 143283796978631845705393997)
          ·
            refine ⟨53731423866986942139522749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143283796978631845705393997 53731423866986942139522749)
            ·
              refine ⟨20149283950120103302321031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53731423866986942139522749 20149283950120103302321031)
              ·
                refine ⟨30223925925180154953481547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20149283950120103302321031 30223925925180154953481547)
                ·
                  refine ⟨45335888887770232430222321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30223925925180154953481547 45335888887770232430222321)
                  ·
                    refine ⟨34001916665827674322666741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45335888887770232430222321 34001916665827674322666741)
                    ·
                      refine ⟨3187679687421344467750007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34001916665827674322666741 3187679687421344467750007)
                      ·
                        rfl

theorem cell23_6207984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 5].length) (baseStart_6207984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207984 prefixEnd_6207984 := by exact prefixLift 6207984
  have htrace : WordTrace (prefixWord ++ tailWord_6207984) baseStart_6207984 baseEnd_6207984 := by
    simpa [prefixWord, tailWord_6207984, baseEnd_6207984] using wordTrace_append hprefix tailTrace_6207984
  have hstable : (prefixWord ++ tailWord_6207984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207984).length < 2 ^ (prefixWord ++ tailWord_6207984).sum := by decide
  have hdescent : baseEnd_6207984 < baseStart_6207984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6207994 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4]
def baseStart_6207994 : Nat := 118140960795 + 6207994 * 2 ^ 59
def prefixEnd_6207994 : Nat := 4983230072969 + 3 ^ 40 * 6207994 * 2
def baseEnd_6207994 : Nat := 3187684822227889428624961

theorem tailTrace_6207994 : CollatzResearch.WordTrace tailWord_6207994 prefixEnd_6207994 3187684822227889428624961 := by
  unfold tailWord_6207994
  simp only [CollatzResearch.WordTrace]
  refine ⟨56606035667876363452553759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150949428447670302540143357 56606035667876363452553759)
  ·
    refine ⟨84909053501814545178830639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56606035667876363452553759 84909053501814545178830639)
    ·
      refine ⟨127363580252721817768245959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84909053501814545178830639 127363580252721817768245959)
      ·
        refine ⟨191045370379082726652368939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127363580252721817768245959 191045370379082726652368939)
        ·
          refine ⟨286568055568624089978553409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191045370379082726652368939 286568055568624089978553409)
          ·
            refine ⟨214926041676468067483915057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286568055568624089978553409 214926041676468067483915057)
            ·
              refine ⟨161194531257351050612936293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 214926041676468067483915057 161194531257351050612936293)
              ·
                refine ⟨30223974610753321989925555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161194531257351050612936293 30223974610753321989925555)
                ·
                  refine ⟨45335961916129982984888333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30223974610753321989925555 45335961916129982984888333)
                  ·
                    refine ⟨17000985718548743619333125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45335961916129982984888333 17000985718548743619333125)
                    ·
                      refine ⟨3187684822227889428624961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17000985718548743619333125 3187684822227889428624961)
                      ·
                        rfl

theorem cell23_6207994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_6207994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6207994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6207994 prefixEnd_6207994 := by exact prefixLift 6207994
  have htrace : WordTrace (prefixWord ++ tailWord_6207994) baseStart_6207994 baseEnd_6207994 := by
    simpa [prefixWord, tailWord_6207994, baseEnd_6207994] using wordTrace_append hprefix tailTrace_6207994
  have hstable : (prefixWord ++ tailWord_6207994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6207994).length < 2 ^ (prefixWord ++ tailWord_6207994).sum := by decide
  have hdescent : baseEnd_6207994 < baseStart_6207994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6207994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208011 : List Nat := [1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 4]
def baseStart_6208011 : Nat := 118140960795 + 6208011 * 2 ^ 59
def prefixEnd_6208011 : Nat := 4983230072969 + 3 ^ 40 * 6208011 * 2
def baseEnd_6208011 : Nat := 3187693551399015862112383

theorem tailTrace_6208011 : CollatzResearch.WordTrace tailWord_6208011 prefixEnd_6208011 3187693551399015862112383 := by
  unfold tailWord_6208011
  simp only [CollatzResearch.WordTrace]
  refine ⟨226424762712443865713583887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150949841808295910475722591 226424762712443865713583887)
  ·
    refine ⟨339637144068665798570375831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226424762712443865713583887 339637144068665798570375831)
    ·
      refine ⟨509455716102998697855563747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339637144068665798570375831 509455716102998697855563747)
      ·
        refine ⟨764183574154498046783345621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509455716102998697855563747 764183574154498046783345621)
        ·
          refine ⟨17910552519246047971484663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 764183574154498046783345621 17910552519246047971484663)
          ·
            refine ⟨26865828778869071957226995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17910552519246047971484663 26865828778869071957226995)
            ·
              refine ⟨40298743168303607935840493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26865828778869071957226995 40298743168303607935840493)
              ·
                refine ⟨15112028688113852975940185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40298743168303607935840493 15112028688113852975940185)
                ·
                  refine ⟨11334021516085389731955139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15112028688113852975940185 11334021516085389731955139)
                  ·
                    refine ⟨17001032274128084597932709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11334021516085389731955139 17001032274128084597932709)
                    ·
                      refine ⟨3187693551399015862112383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17001032274128084597932709 3187693551399015862112383)
                      ·
                        rfl

theorem cell23_6208011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 4].length) (baseStart_6208011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208011 prefixEnd_6208011 := by exact prefixLift 6208011
  have htrace : WordTrace (prefixWord ++ tailWord_6208011) baseStart_6208011 baseEnd_6208011 := by
    simpa [prefixWord, tailWord_6208011, baseEnd_6208011] using wordTrace_append hprefix tailTrace_6208011
  have hstable : (prefixWord ++ tailWord_6208011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208011).length < 2 ^ (prefixWord ++ tailWord_6208011).sum := by decide
  have hdescent : baseEnd_6208011 < baseStart_6208011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208062 : List Nat := [4, 2, 1, 4, 1, 2, 1, 1, 2, 1, 4]
def baseStart_6208062 : Nat := 118140960795 + 6208062 * 2 ^ 59
def prefixEnd_6208062 : Nat := 4983230072969 + 3 ^ 40 * 6208062 * 2
def baseEnd_6208062 : Nat := 3187719738912395162574649

theorem tailTrace_6208062 : CollatzResearch.WordTrace tailWord_6208062 prefixEnd_6208062 3187719738912395162574649 := by
  unfold tailWord_6208062
  simp only [CollatzResearch.WordTrace]
  refine ⟨28303327854407387677961305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150951081890172734282460293 28303327854407387677961305)
  ·
    refine ⟨21227495890805540758470979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28303327854407387677961305 21227495890805540758470979)
    ·
      refine ⟨31841243836208311137706469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21227495890805540758470979 31841243836208311137706469)
      ·
        refine ⟨5970233219289058338319963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31841243836208311137706469 5970233219289058338319963)
        ·
          refine ⟨8955349828933587507479945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5970233219289058338319963 8955349828933587507479945)
          ·
            refine ⟨6716512371700190630609959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8955349828933587507479945 6716512371700190630609959)
            ·
              refine ⟨10074768557550285945914939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6716512371700190630609959 10074768557550285945914939)
              ·
                refine ⟨15112152836325428918872409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10074768557550285945914939 15112152836325428918872409)
                ·
                  refine ⟨11334114627244071689154307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15112152836325428918872409 11334114627244071689154307)
                  ·
                    refine ⟨17001171940866107533731461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11334114627244071689154307 17001171940866107533731461)
                    ·
                      refine ⟨3187719738912395162574649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17001171940866107533731461 3187719738912395162574649)
                      ·
                        rfl

theorem cell23_6208062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_6208062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208062 prefixEnd_6208062 := by exact prefixLift 6208062
  have htrace : WordTrace (prefixWord ++ tailWord_6208062) baseStart_6208062 baseEnd_6208062 := by
    simpa [prefixWord, tailWord_6208062, baseEnd_6208062] using wordTrace_append hprefix tailTrace_6208062
  have hstable : (prefixWord ++ tailWord_6208062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208062).length < 2 ^ (prefixWord ++ tailWord_6208062).sum := by decide
  have hdescent : baseEnd_6208062 < baseStart_6208062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208065 : List Nat := [1, 2, 5, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_6208065 : Nat := 118140960795 + 6208065 * 2 ^ 59
def prefixEnd_6208065 : Nat := 4983230072969 + 3 ^ 40 * 6208065 * 2
def baseEnd_6208065 : Nat := 3187721279354358650837135

theorem tailTrace_6208065 : CollatzResearch.WordTrace tailWord_6208065 prefixEnd_6208065 3187721279354358650837135 := by
  unfold tailWord_6208065
  simp only [CollatzResearch.WordTrace]
  refine ⟨226426732254248232936049649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150951154836165488624033099 226426732254248232936049649)
  ·
    refine ⟨169820049190686174702037237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226426732254248232936049649 169820049190686174702037237)
    ·
      refine ⟨15920629611626828878315991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 169820049190686174702037237 15920629611626828878315991)
      ·
        refine ⟨23880944417440243317473987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15920629611626828878315991 23880944417440243317473987)
        ·
          refine ⟨35821416626160364976210981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23880944417440243317473987 35821416626160364976210981)
          ·
            refine ⟨6716515617405068433039559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35821416626160364976210981 6716515617405068433039559)
            ·
              refine ⟨10074773426107602649559339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6716515617405068433039559 10074773426107602649559339)
              ·
                refine ⟨15112160139161403974339009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10074773426107602649559339 15112160139161403974339009)
                ·
                  refine ⟨11334120104371052980754257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15112160139161403974339009 11334120104371052980754257)
                  ·
                    refine ⟨8500590078278289735565693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11334120104371052980754257 8500590078278289735565693)
                    ·
                      refine ⟨3187721279354358650837135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8500590078278289735565693 3187721279354358650837135)
                      ·
                        rfl

theorem cell23_6208065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_6208065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208065 prefixEnd_6208065 := by exact prefixLift 6208065
  have htrace : WordTrace (prefixWord ++ tailWord_6208065) baseStart_6208065 baseEnd_6208065 := by
    simpa [prefixWord, tailWord_6208065, baseEnd_6208065] using wordTrace_append hprefix tailTrace_6208065
  have hstable : (prefixWord ++ tailWord_6208065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208065).length < 2 ^ (prefixWord ++ tailWord_6208065).sum := by decide
  have hdescent : baseEnd_6208065 < baseStart_6208065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208088 : List Nat := [2, 1, 2, 2, 1, 2, 2, 4, 2, 3, 2]
def baseStart_6208088 : Nat := 118140960795 + 6208088 * 2 ^ 59
def prefixEnd_6208088 : Nat := 4983230072969 + 3 ^ 40 * 6208088 * 2
def baseEnd_6208088 : Nat := 3187733089409412060849529

theorem tailTrace_6208088 : CollatzResearch.WordTrace tailWord_6208088 prefixEnd_6208088 3187733089409412060849529 := by
  unfold tailWord_6208088
  simp only [CollatzResearch.WordTrace]
  refine ⟨113213785566582453932068459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150951714088776605242757945 113213785566582453932068459)
  ·
    refine ⟨169820678349873680898102689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113213785566582453932068459 169820678349873680898102689)
    ·
      refine ⟨127365508762405260673577017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169820678349873680898102689 127365508762405260673577017)
      ·
        refine ⟨95524131571803945505182763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127365508762405260673577017 95524131571803945505182763)
        ·
          refine ⟨143286197357705918257774145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95524131571803945505182763 143286197357705918257774145)
          ·
            refine ⟨107464648018279438693330609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143286197357705918257774145 107464648018279438693330609)
            ·
              refine ⟨80598486013709579019997957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107464648018279438693330609 80598486013709579019997957)
              ·
                refine ⟨15112216127570546066249617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80598486013709579019997957 15112216127570546066249617)
                ·
                  refine ⟨11334162095677909549687213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15112216127570546066249617 11334162095677909549687213)
                  ·
                    refine ⟨4250310785879216081132705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11334162095677909549687213 4250310785879216081132705)
                    ·
                      refine ⟨3187733089409412060849529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4250310785879216081132705 3187733089409412060849529)
                      ·
                        rfl

theorem cell23_6208088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_6208088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208088 prefixEnd_6208088 := by exact prefixLift 6208088
  have htrace : WordTrace (prefixWord ++ tailWord_6208088) baseStart_6208088 baseEnd_6208088 := by
    simpa [prefixWord, tailWord_6208088, baseEnd_6208088] using wordTrace_append hprefix tailTrace_6208088
  have hstable : (prefixWord ++ tailWord_6208088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208088).length < 2 ^ (prefixWord ++ tailWord_6208088).sum := by decide
  have hdescent : baseEnd_6208088 < baseStart_6208088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208111 : List Nat := [1, 1, 2, 1, 3, 2, 5, 1, 1, 6]
def baseStart_6208111 : Nat := 118140960795 + 6208111 * 2 ^ 59
def prefixEnd_6208111 : Nat := 4983230072969 + 3 ^ 40 * 6208111 * 2
def baseEnd_6208111 : Nat := 1062581633154821823620641

theorem tailTrace_6208111 : CollatzResearch.WordTrace tailWord_6208111 prefixEnd_6208111 1062581633154821823620641 := by
  unfold tailWord_6208111
  simp only [CollatzResearch.WordTrace]
  refine ⟨226428410012081582792224187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150952273341387721861482791 226428410012081582792224187)
  ·
    refine ⟨339642615018122374188336281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226428410012081582792224187 339642615018122374188336281)
    ·
      refine ⟨254731961263591780641252211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339642615018122374188336281 254731961263591780641252211)
      ·
        refine ⟨382097941895387670961878317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254731961263591780641252211 382097941895387670961878317)
        ·
          refine ⟨143286728210770376610704369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382097941895387670961878317 143286728210770376610704369)
          ·
            refine ⟨107465046158077782458028277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143286728210770376610704369 107465046158077782458028277)
            ·
              refine ⟨10074848077319792105440151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 107465046158077782458028277 10074848077319792105440151)
              ·
                refine ⟨15112272115979688158160227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10074848077319792105440151 15112272115979688158160227)
                ·
                  refine ⟨22668408173969532237240341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15112272115979688158160227 22668408173969532237240341)
                  ·
                    refine ⟨1062581633154821823620641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22668408173969532237240341 1062581633154821823620641)
                    ·
                      rfl

theorem cell23_6208111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 6].length) (baseStart_6208111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208111 prefixEnd_6208111 := by exact prefixLift 6208111
  have htrace : WordTrace (prefixWord ++ tailWord_6208111) baseStart_6208111 baseEnd_6208111 := by
    simpa [prefixWord, tailWord_6208111, baseEnd_6208111] using wordTrace_append hprefix tailTrace_6208111
  have hstable : (prefixWord ++ tailWord_6208111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208111).length < 2 ^ (prefixWord ++ tailWord_6208111).sum := by decide
  have hdescent : baseEnd_6208111 < baseStart_6208111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208131 : List Nat := [1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 4]
def baseStart_6208131 : Nat := 118140960795 + 6208131 * 2 ^ 59
def prefixEnd_6208131 : Nat := 4983230072969 + 3 ^ 40 * 6208131 * 2
def baseEnd_6208131 : Nat := 3187755169077555392611831

theorem tailTrace_6208131 : CollatzResearch.WordTrace tailWord_6208131 prefixEnd_6208131 3187755169077555392611831 := by
  unfold tailWord_6208131
  simp only [CollatzResearch.WordTrace]
  refine ⟨226429139472009126207952247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150952759648006084138634831 226429139472009126207952247)
  ·
    refine ⟨339643709208013689311928371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226429139472009126207952247 339643709208013689311928371)
    ·
      refine ⟨509465563812020533967892557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339643709208013689311928371 509465563812020533967892557)
      ·
        refine ⟨191049586429507700237959709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 509465563812020533967892557 191049586429507700237959709)
        ·
          refine ⟨71643594911065387589234891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191049586429507700237959709 71643594911065387589234891)
          ·
            refine ⟨107465392366598081383852337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71643594911065387589234891 107465392366598081383852337)
            ·
              refine ⟨80599044274948561037889253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107465392366598081383852337 80599044274948561037889253)
              ·
                refine ⟨15112320801552855194604235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80599044274948561037889253 15112320801552855194604235)
                ·
                  refine ⟨22668481202329282791906353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15112320801552855194604235 22668481202329282791906353)
                  ·
                    refine ⟨17001360901746962093929765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22668481202329282791906353 17001360901746962093929765)
                    ·
                      refine ⟨3187755169077555392611831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17001360901746962093929765 3187755169077555392611831)
                      ·
                        rfl

theorem cell23_6208131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_6208131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208131 prefixEnd_6208131 := by exact prefixLift 6208131
  have htrace : WordTrace (prefixWord ++ tailWord_6208131) baseStart_6208131 baseEnd_6208131 := by
    simpa [prefixWord, tailWord_6208131, baseEnd_6208131] using wordTrace_append hprefix tailTrace_6208131
  have hstable : (prefixWord ++ tailWord_6208131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208131).length < 2 ^ (prefixWord ++ tailWord_6208131).sum := by decide
  have hdescent : baseEnd_6208131 < baseStart_6208131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208148 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_6208148 : Nat := 118140960795 + 6208148 * 2 ^ 59
def prefixEnd_6208148 : Nat := 4983230072969 + 3 ^ 40 * 6208148 * 2
def baseEnd_6208148 : Nat := 3187763898248681826099253

theorem tailTrace_6208148 : CollatzResearch.WordTrace tailWord_6208148 prefixEnd_6208148 3187763898248681826099253 := by
  unfold tailWord_6208148
  simp only [CollatzResearch.WordTrace]
  refine ⟨113214879756473769055660549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150953173008631692074214065 113214879756473769055660549)
  ·
    refine ⟨21227789954338831697936353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113214879756473769055660549 21227789954338831697936353)
    ·
      refine ⟨15920842465754123773452265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21227789954338831697936353 15920842465754123773452265)
      ·
        refine ⟨11940631849315592830089199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15920842465754123773452265 11940631849315592830089199)
        ·
          refine ⟨17910947773973389245133799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11940631849315592830089199 17910947773973389245133799)
          ·
            refine ⟨26866421660960083867700699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17910947773973389245133799 26866421660960083867700699)
            ·
              refine ⟨40299632491440125801551049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26866421660960083867700699 40299632491440125801551049)
              ·
                refine ⟨30224724368580094351163287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40299632491440125801551049 30224724368580094351163287)
                ·
                  refine ⟨45337086552870141526744931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30224724368580094351163287 45337086552870141526744931)
                  ·
                    refine ⟨68005629829305212290117397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 45337086552870141526744931 68005629829305212290117397)
                    ·
                      refine ⟨3187763898248681826099253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68005629829305212290117397 3187763898248681826099253)
                      ·
                        rfl

theorem cell23_6208148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_6208148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208148 prefixEnd_6208148 := by exact prefixLift 6208148
  have htrace : WordTrace (prefixWord ++ tailWord_6208148) baseStart_6208148 baseEnd_6208148 := by
    simpa [prefixWord, tailWord_6208148, baseEnd_6208148] using wordTrace_append hprefix tailTrace_6208148
  have hstable : (prefixWord ++ tailWord_6208148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208148).length < 2 ^ (prefixWord ++ tailWord_6208148).sum := by decide
  have hdescent : baseEnd_6208148 < baseStart_6208148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208158 : List Nat := [4, 3, 1, 1, 1, 1, 4, 8]
def baseStart_6208158 : Nat := 118140960795 + 6208158 * 2 ^ 59
def prefixEnd_6208158 : Nat := 4983230072969 + 3 ^ 40 * 6208158 * 2
def baseEnd_6208158 : Nat := 118065519742786177295341

theorem tailTrace_6208158 : CollatzResearch.WordTrace tailWord_6208158 prefixEnd_6208158 118065519742786177295341 := by
  unfold tailWord_6208158
  simp only [CollatzResearch.WordTrace]
  refine ⟨28303765530363913727398141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150953416161940873212790085 28303765530363913727398141)
  ·
    refine ⟨10613912073886467647774303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28303765530363913727398141 10613912073886467647774303)
    ·
      refine ⟨15920868110829701471661455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10613912073886467647774303 15920868110829701471661455)
      ·
        refine ⟨23881302166244552207492183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15920868110829701471661455 23881302166244552207492183)
        ·
          refine ⟨35821953249366828311238275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23881302166244552207492183 35821953249366828311238275)
          ·
            refine ⟨53732929874050242466857413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35821953249366828311238275 53732929874050242466857413)
            ·
              refine ⟨10074924351384420462535765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53732929874050242466857413 10074924351384420462535765)
              ·
                refine ⟨118065519742786177295341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10074924351384420462535765 118065519742786177295341)
                ·
                  rfl

theorem cell23_6208158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 8].length) (baseStart_6208158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208158 prefixEnd_6208158 := by exact prefixLift 6208158
  have htrace : WordTrace (prefixWord ++ tailWord_6208158) baseStart_6208158 baseEnd_6208158 := by
    simpa [prefixWord, tailWord_6208158, baseEnd_6208158] using wordTrace_append hprefix tailTrace_6208158
  have hstable : (prefixWord ++ tailWord_6208158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208158).length < 2 ^ (prefixWord ++ tailWord_6208158).sum := by decide
  have hdescent : baseEnd_6208158 < baseStart_6208158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208182 : List Nat := [5, 1, 3, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_6208182 : Nat := 118140960795 + 6208182 * 2 ^ 59
def prefixEnd_6208182 : Nat := 4983230072969 + 3 ^ 40 * 6208182 * 2
def baseEnd_6208182 : Nat := 3187781356590934693074097

theorem tailTrace_6208182 : CollatzResearch.WordTrace tailWord_6208182 prefixEnd_6208182 3187781356590934693074097 := by
  unfold tailWord_6208182
  simp only [CollatzResearch.WordTrace]
  refine ⟨14151937474676522619878675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150953999729882907945372533 14151937474676522619878675)
  ·
    refine ⟨21227906212014783929818013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14151937474676522619878675 21227906212014783929818013)
    ·
      refine ⟨7960464829505543973681755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21227906212014783929818013 7960464829505543973681755)
      ·
        refine ⟨11940697244258315960522633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7960464829505543973681755 11940697244258315960522633)
        ·
          refine ⟨8955522933193736970391975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11940697244258315960522633 8955522933193736970391975)
          ·
            refine ⟨13433284399790605455587963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8955522933193736970391975 13433284399790605455587963)
            ·
              refine ⟨20149926599685908183381945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13433284399790605455587963 20149926599685908183381945)
              ·
                refine ⟨15112444949764431137536459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20149926599685908183381945 15112444949764431137536459)
                ·
                  refine ⟨22668667424646646706304689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15112444949764431137536459 22668667424646646706304689)
                  ·
                    refine ⟨17001500568484985029728517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22668667424646646706304689 17001500568484985029728517)
                    ·
                      refine ⟨3187781356590934693074097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17001500568484985029728517 3187781356590934693074097)
                      ·
                        rfl

theorem cell23_6208182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_6208182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208182 prefixEnd_6208182 := by exact prefixLift 6208182
  have htrace : WordTrace (prefixWord ++ tailWord_6208182) baseStart_6208182 baseEnd_6208182 := by
    simpa [prefixWord, tailWord_6208182, baseEnd_6208182] using wordTrace_append hprefix tailTrace_6208182
  have hstable : (prefixWord ++ tailWord_6208182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208182).length < 2 ^ (prefixWord ++ tailWord_6208182).sum := by decide
  have hdescent : baseEnd_6208182 < baseStart_6208182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208202 : List Nat := [3, 1, 2, 1, 4, 2, 2, 2, 2, 1, 3]
def baseStart_6208202 : Nat := 118140960795 + 6208202 * 2 ^ 59
def prefixEnd_6208202 : Nat := 4983230072969 + 3 ^ 40 * 6208202 * 2
def baseEnd_6208202 : Nat := 3187791626204024614824005

theorem tailTrace_6208202 : CollatzResearch.WordTrace tailWord_6208202 prefixEnd_6208202 3187791626204024614824005 := by
  unfold tailWord_6208202
  simp only [CollatzResearch.WordTrace]
  refine ⟨56607932263687976333446715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150954486036501270222524573 56607932263687976333446715)
  ·
    refine ⟨84911898395531964500170073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56607932263687976333446715 84911898395531964500170073)
    ·
      refine ⟨63683923796648973375127555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84911898395531964500170073 63683923796648973375127555)
      ·
        refine ⟨95525885694973460062691333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63683923796648973375127555 95525885694973460062691333)
        ·
          refine ⟨17911103567807523761754625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95525885694973460062691333 17911103567807523761754625)
          ·
            refine ⟨13433327675855642821315969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17911103567807523761754625 13433327675855642821315969)
            ·
              refine ⟨10074995756891732115986977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13433327675855642821315969 10074995756891732115986977)
              ·
                refine ⟨7556246817668799086990233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10074995756891732115986977 7556246817668799086990233)
                ·
                  refine ⟨5667185113251599315242675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7556246817668799086990233 5667185113251599315242675)
                  ·
                    refine ⟨8500777669877398972864013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5667185113251599315242675 8500777669877398972864013)
                    ·
                      refine ⟨3187791626204024614824005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8500777669877398972864013 3187791626204024614824005)
                      ·
                        rfl

theorem cell23_6208202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_6208202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208202 prefixEnd_6208202 := by exact prefixLift 6208202
  have htrace : WordTrace (prefixWord ++ tailWord_6208202) baseStart_6208202 baseEnd_6208202 := by
    simpa [prefixWord, tailWord_6208202, baseEnd_6208202] using wordTrace_append hprefix tailTrace_6208202
  have hstable : (prefixWord ++ tailWord_6208202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208202).length < 2 ^ (prefixWord ++ tailWord_6208202).sum := by decide
  have hdescent : baseEnd_6208202 < baseStart_6208202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208225 : List Nat := [1, 2, 3, 1, 4, 1, 1, 3, 1, 4, 2]
def baseStart_6208225 : Nat := 118140960795 + 6208225 * 2 ^ 59
def prefixEnd_6208225 : Nat := 4983230072969 + 3 ^ 40 * 6208225 * 2
def baseEnd_6208225 : Nat := 3187803436259078024836399

theorem tailTrace_6208225 : CollatzResearch.WordTrace tailWord_6208225 prefixEnd_6208225 3187803436259078024836399 := by
  unfold tailWord_6208225
  simp only [CollatzResearch.WordTrace]
  refine ⟨226432567933668580261874129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150955045289112386841249419 226432567933668580261874129)
  ·
    refine ⟨169824425950251435196405597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226432567933668580261874129 169824425950251435196405597)
    ·
      refine ⟨63684159731344288198652099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169824425950251435196405597 63684159731344288198652099)
      ·
        refine ⟨95526239597016432297978149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63684159731344288198652099 95526239597016432297978149)
        ·
          refine ⟨17911169924440581055870903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95526239597016432297978149 17911169924440581055870903)
          ·
            refine ⟨26866754886660871583806355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17911169924440581055870903 26866754886660871583806355)
            ·
              refine ⟨40300132329991307375709533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26866754886660871583806355 40300132329991307375709533)
              ·
                refine ⟨15112549623746740265891075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40300132329991307375709533 15112549623746740265891075)
                ·
                  refine ⟨22668824435620110398836613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15112549623746740265891075 22668824435620110398836613)
                  ·
                    refine ⟨4250404581678770699781865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22668824435620110398836613 4250404581678770699781865)
                    ·
                      refine ⟨3187803436259078024836399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4250404581678770699781865 3187803436259078024836399)
                      ·
                        rfl

theorem cell23_6208225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 4, 2].length) (baseStart_6208225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208225 prefixEnd_6208225 := by exact prefixLift 6208225
  have htrace : WordTrace (prefixWord ++ tailWord_6208225) baseStart_6208225 baseEnd_6208225 := by
    simpa [prefixWord, tailWord_6208225, baseEnd_6208225] using wordTrace_append hprefix tailTrace_6208225
  have hstable : (prefixWord ++ tailWord_6208225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208225).length < 2 ^ (prefixWord ++ tailWord_6208225).sum := by decide
  have hdescent : baseEnd_6208225 < baseStart_6208225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208271 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 7]
def baseStart_6208271 : Nat := 118140960795 + 6208271 * 2 ^ 59
def prefixEnd_6208271 : Nat := 4983230072969 + 3 ^ 40 * 6208271 * 2
def baseEnd_6208271 : Nat := 3187827056369184844861187

theorem tailTrace_6208271 : CollatzResearch.WordTrace tailWord_6208271 prefixEnd_6208271 3187827056369184844861187 := by
  unfold tailWord_6208271
  simp only [CollatzResearch.WordTrace]
  refine ⟨226434245691501930118048667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150956163794334620078699111 226434245691501930118048667)
  ·
    refine ⟨339651368537252895177073001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226434245691501930118048667 339651368537252895177073001)
    ·
      refine ⟨254738526402939671382804751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339651368537252895177073001 254738526402939671382804751)
      ·
        refine ⟨382107789604409507074207127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254738526402939671382804751 382107789604409507074207127)
        ·
          refine ⟨573161684406614260611310691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382107789604409507074207127 573161684406614260611310691)
          ·
            refine ⟨859742526609921390916966037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573161684406614260611310691 859742526609921390916966037)
            ·
              refine ⟨40300430934840065199232783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 859742526609921390916966037 40300430934840065199232783)
              ·
                refine ⟨60450646402260097798849175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40300430934840065199232783 60450646402260097798849175)
                ·
                  refine ⟨90675969603390146698273763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60450646402260097798849175 90675969603390146698273763)
                  ·
                    refine ⟨136013954405085220047410645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90675969603390146698273763 136013954405085220047410645)
                    ·
                      refine ⟨3187827056369184844861187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136013954405085220047410645 3187827056369184844861187)
                      ·
                        rfl

theorem cell23_6208271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_6208271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208271 prefixEnd_6208271 := by exact prefixLift 6208271
  have htrace : WordTrace (prefixWord ++ tailWord_6208271) baseStart_6208271 baseEnd_6208271 := by
    simpa [prefixWord, tailWord_6208271, baseEnd_6208271] using wordTrace_append hprefix tailTrace_6208271
  have hstable : (prefixWord ++ tailWord_6208271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208271).length < 2 ^ (prefixWord ++ tailWord_6208271).sum := by decide
  have hdescent : baseEnd_6208271 < baseStart_6208271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208291 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 1, 10]
def baseStart_6208291 : Nat := 118140960795 + 6208291 * 2 ^ 59
def prefixEnd_6208291 : Nat := 4983230072969 + 3 ^ 40 * 6208291 * 2
def baseEnd_6208291 : Nat := 1062612441994091588870365

theorem tailTrace_6208291 : CollatzResearch.WordTrace tailWord_6208291 prefixEnd_6208291 1062612441994091588870365 := by
  unfold tailWord_6208291
  simp only [CollatzResearch.WordTrace]
  refine ⟨226434975151429473533776727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150956650100952982355851151 226434975151429473533776727)
  ·
    refine ⟨339652462727144210300665091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226434975151429473533776727 339652462727144210300665091)
    ·
      refine ⟨509478694090716315450997637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339652462727144210300665091 509478694090716315450997637)
      ·
        refine ⟨95527255142009309147062057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 509478694090716315450997637 95527255142009309147062057)
        ·
          refine ⟨71645441356506981860296543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95527255142009309147062057 71645441356506981860296543)
          ·
            refine ⟨107468162034760472790444815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71645441356506981860296543 107468162034760472790444815)
            ·
              refine ⟨161202243052140709185667223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107468162034760472790444815 161202243052140709185667223)
              ·
                refine ⟨241803364578211063778500835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161202243052140709185667223 241803364578211063778500835)
                ·
                  refine ⟨362705046867316595667751253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 241803364578211063778500835 362705046867316595667751253)
                  ·
                    refine ⟨1062612441994091588870365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 362705046867316595667751253 1062612441994091588870365)
                    ·
                      rfl

theorem cell23_6208291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 10].length) (baseStart_6208291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208291 prefixEnd_6208291 := by exact prefixLift 6208291
  have htrace : WordTrace (prefixWord ++ tailWord_6208291) baseStart_6208291 baseEnd_6208291 := by
    simpa [prefixWord, tailWord_6208291, baseEnd_6208291] using wordTrace_append hprefix tailTrace_6208291
  have hstable : (prefixWord ++ tailWord_6208291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208291).length < 2 ^ (prefixWord ++ tailWord_6208291).sum := by decide
  have hdescent : baseEnd_6208291 < baseStart_6208291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208405 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 3, 1, 4]
def baseStart_6208405 : Nat := 118140960795 + 6208405 * 2 ^ 59
def prefixEnd_6208405 : Nat := 4983230072969 + 3 ^ 40 * 6208405 * 2
def baseEnd_6208405 : Nat := 3187895862776887320585571

theorem tailTrace_6208405 : CollatzResearch.WordTrace tailWord_6208405 prefixEnd_6208405 3187895862776887320585571 := by
  unfold tailWord_6208405
  simp only [CollatzResearch.WordTrace]
  refine ⟨226439133073016471003426669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150959422048677647335617779 226439133073016471003426669)
  ·
    refine ⟨84914674902381176626285001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226439133073016471003426669 84914674902381176626285001)
    ·
      refine ⟨63686006176785882469713751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84914674902381176626285001 63686006176785882469713751)
      ·
        refine ⟨95529009265178823704570627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63686006176785882469713751 95529009265178823704570627)
        ·
          refine ⟨143293513897768235556855941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95529009265178823704570627 143293513897768235556855941)
          ·
            refine ⟨26867533855831544166910489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143293513897768235556855941 26867533855831544166910489)
            ·
              refine ⟨20150650391873658125182867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26867533855831544166910489 20150650391873658125182867)
              ·
                refine ⟨30225975587810487187774301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20150650391873658125182867 30225975587810487187774301)
                ·
                  refine ⟨11334740845428932695415363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30225975587810487187774301 11334740845428932695415363)
                  ·
                    refine ⟨17002111268143399043123045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11334740845428932695415363 17002111268143399043123045)
                    ·
                      refine ⟨3187895862776887320585571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17002111268143399043123045 3187895862776887320585571)
                      ·
                        rfl

theorem cell23_6208405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_6208405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208405 prefixEnd_6208405 := by exact prefixLift 6208405
  have htrace : WordTrace (prefixWord ++ tailWord_6208405) baseStart_6208405 baseEnd_6208405 := by
    simpa [prefixWord, tailWord_6208405, baseEnd_6208405] using wordTrace_append hprefix tailTrace_6208405
  have hstable : (prefixWord ++ tailWord_6208405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208405).length < 2 ^ (prefixWord ++ tailWord_6208405).sum := by decide
  have hdescent : baseEnd_6208405 < baseStart_6208405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208415 : List Nat := [1, 1, 2, 5, 2, 1, 2, 2, 1, 6]
def baseStart_6208415 : Nat := 118140960795 + 6208415 * 2 ^ 59
def prefixEnd_6208415 : Nat := 4983230072969 + 3 ^ 40 * 6208415 * 2
def baseEnd_6208415 : Nat := 1062633665861144093820175

theorem tailTrace_6208415 : CollatzResearch.WordTrace tailWord_6208415 prefixEnd_6208415 1062633665861144093820175 := by
  unfold tailWord_6208415
  simp only [CollatzResearch.WordTrace]
  refine ⟨226439497802980242711290699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150959665201986828474193799 226439497802980242711290699)
  ·
    refine ⟨339659246704470364066936049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226439497802980242711290699 339659246704470364066936049)
    ·
      refine ⟨254744435028352773050202037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339659246704470364066936049 254744435028352773050202037)
      ·
        refine ⟨23882290783908072473456441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 254744435028352773050202037 23882290783908072473456441)
        ·
          refine ⟨17911718087931054355092331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23882290783908072473456441 17911718087931054355092331)
          ·
            refine ⟨26867577131896581532638497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17911718087931054355092331 26867577131896581532638497)
            ·
              refine ⟨20150682848922436149478873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26867577131896581532638497 20150682848922436149478873)
              ·
                refine ⟨15113012136691827112109155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20150682848922436149478873 15113012136691827112109155)
                ·
                  refine ⟨22669518205037740668163733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15113012136691827112109155 22669518205037740668163733)
                  ·
                    refine ⟨1062633665861144093820175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22669518205037740668163733 1062633665861144093820175)
                    ·
                      rfl

theorem cell23_6208415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 6].length) (baseStart_6208415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208415 prefixEnd_6208415 := by exact prefixLift 6208415
  have htrace : WordTrace (prefixWord ++ tailWord_6208415) baseStart_6208415 baseEnd_6208415 := by
    simpa [prefixWord, tailWord_6208415, baseEnd_6208415] using wordTrace_append hprefix tailTrace_6208415
  have hstable : (prefixWord ++ tailWord_6208415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208415).length < 2 ^ (prefixWord ++ tailWord_6208415).sum := by decide
  have hdescent : baseEnd_6208415 < baseStart_6208415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208462 : List Nat := [4, 1, 1, 1, 2, 5, 2, 7]
def baseStart_6208462 : Nat := 118140960795 + 6208462 * 2 ^ 59
def prefixEnd_6208462 : Nat := 4983230072969 + 3 ^ 40 * 6208462 * 2
def baseEnd_6208462 : Nat := 118071301154599762873067

theorem tailTrace_6208462 : CollatzResearch.WordTrace tailWord_6208462 prefixEnd_6208462 118071301154599762873067 := by
  unfold tailWord_6208462
  simp only [CollatzResearch.WordTrace]
  refine ⟨28305151504226246217281455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150960808022539979825501093 28305151504226246217281455)
  ·
    refine ⟨42457727256339369325922183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28305151504226246217281455 42457727256339369325922183)
    ·
      refine ⟨63686590884509053988883275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42457727256339369325922183 63686590884509053988883275)
      ·
        refine ⟨95529886326763580983324913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63686590884509053988883275 95529886326763580983324913)
        ·
          refine ⟨71647414745072685737493685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95529886326763580983324913 71647414745072685737493685)
          ·
            refine ⟨6716945132350564287890033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71647414745072685737493685 6716945132350564287890033)
            ·
              refine ⟨5037708849262923215917525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6716945132350564287890033 5037708849262923215917525)
              ·
                refine ⟨118071301154599762873067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5037708849262923215917525 118071301154599762873067)
                ·
                  rfl

theorem cell23_6208462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 2, 7].length) (baseStart_6208462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208462 prefixEnd_6208462 := by exact prefixLift 6208462
  have htrace : WordTrace (prefixWord ++ tailWord_6208462) baseStart_6208462 baseEnd_6208462 := by
    simpa [prefixWord, tailWord_6208462, baseEnd_6208462] using wordTrace_append hprefix tailTrace_6208462
  have hstable : (prefixWord ++ tailWord_6208462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208462).length < 2 ^ (prefixWord ++ tailWord_6208462).sum := by decide
  have hdescent : baseEnd_6208462 < baseStart_6208462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208472 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 4, 1, 3]
def baseStart_6208472 : Nat := 118140960795 + 6208472 * 2 ^ 59
def prefixEnd_6208472 : Nat := 4983230072969 + 3 ^ 40 * 6208472 * 2
def baseEnd_6208472 : Nat := 3187930265980738558447763

theorem tailTrace_6208472 : CollatzResearch.WordTrace tailWord_6208472 prefixEnd_6208472 3187930265980738558447763 := by
  unfold tailWord_6208472
  simp only [CollatzResearch.WordTrace]
  refine ⟨113220788381886870723057835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150961051175849160964077113 113220788381886870723057835)
  ·
    refine ⟨169831182572830306084586753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113220788381886870723057835 169831182572830306084586753)
    ·
      refine ⟨127373386929622729563440065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169831182572830306084586753 127373386929622729563440065)
      ·
        refine ⟨95530040197217047172580049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127373386929622729563440065 95530040197217047172580049)
        ·
          refine ⟨71647530147912785379435037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95530040197217047172580049 71647530147912785379435037)
          ·
            refine ⟨26867823805467294517288139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71647530147912785379435037 26867823805467294517288139)
            ·
              refine ⟨40301735708200941775932209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26867823805467294517288139 40301735708200941775932209)
              ·
                refine ⟨30226301781150706331949157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40301735708200941775932209 30226301781150706331949157)
                ·
                  refine ⟨5667431583965757437240467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30226301781150706331949157 5667431583965757437240467)
                  ·
                    refine ⟨8501147375948636155860701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5667431583965757437240467 8501147375948636155860701)
                    ·
                      refine ⟨3187930265980738558447763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8501147375948636155860701 3187930265980738558447763)
                      ·
                        rfl

theorem cell23_6208472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_6208472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208472 prefixEnd_6208472 := by exact prefixLift 6208472
  have htrace : WordTrace (prefixWord ++ tailWord_6208472) baseStart_6208472 baseEnd_6208472 := by
    simpa [prefixWord, tailWord_6208472, baseEnd_6208472] using wordTrace_append hprefix tailTrace_6208472
  have hstable : (prefixWord ++ tailWord_6208472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208472).length < 2 ^ (prefixWord ++ tailWord_6208472).sum := by decide
  have hdescent : baseEnd_6208472 < baseStart_6208472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208473 : List Nat := [1, 2, 1, 2, 5, 3, 1, 3, 1, 2, 2]
def baseStart_6208473 : Nat := 118140960795 + 6208473 * 2 ^ 59
def prefixEnd_6208473 : Nat := 4983230072969 + 3 ^ 40 * 6208473 * 2
def baseEnd_6208473 : Nat := 3187930779461393054535259

theorem tailTrace_6208473 : CollatzResearch.WordTrace tailWord_6208473 prefixEnd_6208473 3187930779461393054535259 := by
  unfold tailWord_6208473
  simp only [CollatzResearch.WordTrace]
  refine ⟨226441613236770118616902073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150961075491180079077934715 226441613236770118616902073)
  ·
    refine ⟨169831209927577588962676555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226441613236770118616902073 169831209927577588962676555)
    ·
      refine ⟨254746814891366383444014833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169831209927577588962676555 254746814891366383444014833)
      ·
        refine ⟨191060111168524787583011125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254746814891366383444014833 191060111168524787583011125)
        ·
          refine ⟨17911885422049198835907293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 191060111168524787583011125 17911885422049198835907293)
          ·
            refine ⟨6716957033268449563465235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17911885422049198835907293 6716957033268449563465235)
            ·
              refine ⟨10075435549902674345197853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6716957033268449563465235 10075435549902674345197853)
              ·
                refine ⟨3778288331213502879449195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10075435549902674345197853 3778288331213502879449195)
                ·
                  refine ⟨5667432496820254319173793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3778288331213502879449195 5667432496820254319173793)
                  ·
                    refine ⟨4250574372615190739380345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5667432496820254319173793 4250574372615190739380345)
                    ·
                      refine ⟨3187930779461393054535259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4250574372615190739380345 3187930779461393054535259)
                      ·
                        rfl

theorem cell23_6208473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 1, 2, 2].length) (baseStart_6208473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208473 prefixEnd_6208473 := by exact prefixLift 6208473
  have htrace : WordTrace (prefixWord ++ tailWord_6208473) baseStart_6208473 baseEnd_6208473 := by
    simpa [prefixWord, tailWord_6208473, baseEnd_6208473] using wordTrace_append hprefix tailTrace_6208473
  have hstable : (prefixWord ++ tailWord_6208473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208473).length < 2 ^ (prefixWord ++ tailWord_6208473).sum := by decide
  have hdescent : baseEnd_6208473 < baseStart_6208473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208500 : List Nat := [2, 6, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_6208500 : Nat := 118140960795 + 6208500 * 2 ^ 59
def prefixEnd_6208500 : Nat := 4983230072969 + 3 ^ 40 * 6208500 * 2
def baseEnd_6208500 : Nat := 1062648214479688149632545

theorem tailTrace_6208500 : CollatzResearch.WordTrace tailWord_6208500 prefixEnd_6208500 1062648214479688149632545 := by
  unfold tailWord_6208500
  simp only [CollatzResearch.WordTrace]
  refine ⟨113221299003836151114067477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150961732005114868152089969 113221299003836151114067477)
  ·
    refine ⟨5307248390804819583471913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 113221299003836151114067477 5307248390804819583471913)
    ·
      refine ⟨3980436293103614687603935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5307248390804819583471913 3980436293103614687603935)
      ·
        refine ⟨5970654439655422031405903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3980436293103614687603935 5970654439655422031405903)
        ·
          refine ⟨8955981659483133047108855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5970654439655422031405903 8955981659483133047108855)
          ·
            refine ⟨13433972489224699570663283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8955981659483133047108855 13433972489224699570663283)
            ·
              refine ⟨20150958733837049355994925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13433972489224699570663283 20150958733837049355994925)
              ·
                refine ⟨7556609525188893508498097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20150958733837049355994925 7556609525188893508498097)
                ·
                  refine ⟨5667457143891670131373573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7556609525188893508498097 5667457143891670131373573)
                  ·
                    refine ⟨1062648214479688149632545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5667457143891670131373573 1062648214479688149632545)
                    ·
                      rfl

theorem cell23_6208500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_6208500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208500 prefixEnd_6208500 := by exact prefixLift 6208500
  have htrace : WordTrace (prefixWord ++ tailWord_6208500) baseStart_6208500 baseEnd_6208500 := by
    simpa [prefixWord, tailWord_6208500, baseEnd_6208500] using wordTrace_append hprefix tailTrace_6208500
  have hstable : (prefixWord ++ tailWord_6208500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208500).length < 2 ^ (prefixWord ++ tailWord_6208500).sum := by decide
  have hdescent : baseEnd_6208500 < baseStart_6208500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208546 : List Nat := [3, 3, 1, 1, 1, 3, 1, 4, 2, 2, 2]
def baseStart_6208546 : Nat := 118140960795 + 6208546 * 2 ^ 59
def prefixEnd_6208546 : Nat := 4983230072969 + 3 ^ 40 * 6208546 * 2
def baseEnd_6208546 : Nat := 3187968263549171268922423

theorem tailTrace_6208546 : CollatzResearch.WordTrace tailWord_6208546 prefixEnd_6208546 3187968263549171268922423 := by
  unfold tailWord_6208546
  simp only [CollatzResearch.WordTrace]
  refine ⟨56611068941376413021077373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150962850510337101389539661 56611068941376413021077373)
  ·
    refine ⟨21229150853016154882904015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56611068941376413021077373 21229150853016154882904015)
    ·
      refine ⟨31843726279524232324356023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21229150853016154882904015 31843726279524232324356023)
      ·
        refine ⟨47765589419286348486534035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31843726279524232324356023 47765589419286348486534035)
        ·
          refine ⟨71648384128929522729801053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47765589419286348486534035 71648384128929522729801053)
          ·
            refine ⟨26868144048348571023675395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71648384128929522729801053 26868144048348571023675395)
            ·
              refine ⟨40302216072522856535513093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26868144048348571023675395 40302216072522856535513093)
              ·
                refine ⟨7556665513598035600408705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40302216072522856535513093 7556665513598035600408705)
                ·
                  refine ⟨5667499135198526700306529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7556665513598035600408705 5667499135198526700306529)
                  ·
                    refine ⟨4250624351398895025229897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5667499135198526700306529 4250624351398895025229897)
                    ·
                      refine ⟨3187968263549171268922423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4250624351398895025229897 3187968263549171268922423)
                      ·
                        rfl

theorem cell23_6208546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_6208546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208546 prefixEnd_6208546 := by exact prefixLift 6208546
  have htrace : WordTrace (prefixWord ++ tailWord_6208546) baseStart_6208546 baseEnd_6208546 := by
    simpa [prefixWord, tailWord_6208546, baseEnd_6208546] using wordTrace_append hprefix tailTrace_6208546
  have hstable : (prefixWord ++ tailWord_6208546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208546).length < 2 ^ (prefixWord ++ tailWord_6208546).sum := by decide
  have hdescent : baseEnd_6208546 < baseStart_6208546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208562 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3]
def baseStart_6208562 : Nat := 118140960795 + 6208562 * 2 ^ 59
def prefixEnd_6208562 : Nat := 4983230072969 + 3 ^ 40 * 6208562 * 2
def baseEnd_6208562 : Nat := 3187976479239643206322349

theorem tailTrace_6208562 : CollatzResearch.WordTrace tailWord_6208562 prefixEnd_6208562 3187976479239643206322349 := by
  unfold tailWord_6208562
  simp only [CollatzResearch.WordTrace]
  refine ⟨56611214833361921704222985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150963239555631791211261293 56611214833361921704222985)
  ·
    refine ⟨42458411125021441278167239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56611214833361921704222985 42458411125021441278167239)
    ·
      refine ⟨63687616687532161917250859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42458411125021441278167239 63687616687532161917250859)
      ·
        refine ⟨95531425031298242875876289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63687616687532161917250859 95531425031298242875876289)
        ·
          refine ⟨71648568773473682156907217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95531425031298242875876289 71648568773473682156907217)
          ·
            refine ⟨53736426580105261617680413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71648568773473682156907217 53736426580105261617680413)
            ·
              refine ⟨20151159967539473106630155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53736426580105261617680413 20151159967539473106630155)
              ·
                refine ⟨30226739951309209659945233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20151159967539473106630155 30226739951309209659945233)
                ·
                  refine ⟨22670054963481907244958925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30226739951309209659945233 22670054963481907244958925)
                  ·
                    refine ⟨8501270611305715216859597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22670054963481907244958925 8501270611305715216859597)
                    ·
                      refine ⟨3187976479239643206322349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8501270611305715216859597 3187976479239643206322349)
                      ·
                        rfl

theorem cell23_6208562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_6208562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208562 prefixEnd_6208562 := by exact prefixLift 6208562
  have htrace : WordTrace (prefixWord ++ tailWord_6208562) baseStart_6208562 baseEnd_6208562 := by
    simpa [prefixWord, tailWord_6208562, baseEnd_6208562] using wordTrace_append hprefix tailTrace_6208562
  have hstable : (prefixWord ++ tailWord_6208562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208562).length < 2 ^ (prefixWord ++ tailWord_6208562).sum := by decide
  have hdescent : baseEnd_6208562 < baseStart_6208562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208565 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 1, 7]
def baseStart_6208565 : Nat := 118140960795 + 6208565 * 2 ^ 59
def prefixEnd_6208565 : Nat := 4983230072969 + 3 ^ 40 * 6208565 * 2
def baseEnd_6208565 : Nat := 1062659339893868898194945

theorem tailTrace_6208565 : CollatzResearch.WordTrace tailWord_6208565 prefixEnd_6208565 1062659339893868898194945 := by
  unfold tailWord_6208565
  simp only [CollatzResearch.WordTrace]
  refine ⟨226444968752436818329251149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150963312501624545552834099 226444968752436818329251149)
  ·
    refine ⟨84916863282163806873469181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226444968752436818329251149 84916863282163806873469181)
    ·
      refine ⟨31843823730811427577550943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84916863282163806873469181 31843823730811427577550943)
      ·
        refine ⟨47765735596217141366326415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31843823730811427577550943 47765735596217141366326415)
        ·
          refine ⟨71648603394325712049489623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47765735596217141366326415 71648603394325712049489623)
          ·
            refine ⟨107472905091488568074234435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71648603394325712049489623 107472905091488568074234435)
            ·
              refine ⟨161209357637232852111351653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107472905091488568074234435 161209357637232852111351653)
              ·
                refine ⟨30226754556981159770878435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 161209357637232852111351653 30226754556981159770878435)
                ·
                  refine ⟨45340131835471739656317653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30226754556981159770878435 45340131835471739656317653)
                  ·
                    refine ⟨1062659339893868898194945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45340131835471739656317653 1062659339893868898194945)
                    ·
                      rfl

theorem cell23_6208565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_6208565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208565 prefixEnd_6208565 := by exact prefixLift 6208565
  have htrace : WordTrace (prefixWord ++ tailWord_6208565) baseStart_6208565 baseEnd_6208565 := by
    simpa [prefixWord, tailWord_6208565, baseEnd_6208565] using wordTrace_append hprefix tailTrace_6208565
  have hstable : (prefixWord ++ tailWord_6208565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208565).length < 2 ^ (prefixWord ++ tailWord_6208565).sum := by decide
  have hdescent : baseEnd_6208565 < baseStart_6208565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208663 : List Nat := [1, 1, 3, 3, 3, 2, 3, 2, 1, 4]
def baseStart_6208663 : Nat := 118140960795 + 6208663 * 2 ^ 59
def prefixEnd_6208663 : Nat := 4983230072969 + 3 ^ 40 * 6208663 * 2
def baseEnd_6208663 : Nat := 1062676113595249103719795

theorem tailTrace_6208663 : CollatzResearch.WordTrace tailWord_6208663 prefixEnd_6208663 1062676113595249103719795 := by
  unfold tailWord_6208663
  simp only [CollatzResearch.WordTrace]
  refine ⟨226448543106081781066318643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150965695404054520710879095 226448543106081781066318643)
  ·
    refine ⟨339672814659122671599477965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226448543106081781066318643 339672814659122671599477965)
    ·
      refine ⟨127377305497171001849804237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339672814659122671599477965 127377305497171001849804237)
      ·
        refine ⟨47766489561439125693676589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127377305497171001849804237 47766489561439125693676589)
        ·
          refine ⟨17912433585539672135128721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47766489561439125693676589 17912433585539672135128721)
          ·
            refine ⟨13434325189154754101346541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17912433585539672135128721 13434325189154754101346541)
            ·
              refine ⟨5037871945933032788004953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13434325189154754101346541 5037871945933032788004953)
              ·
                refine ⟨3778403959449774591003715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5037871945933032788004953 3778403959449774591003715)
                ·
                  refine ⟨5667605939174661886505573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3778403959449774591003715 5667605939174661886505573)
                  ·
                    refine ⟨1062676113595249103719795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5667605939174661886505573 1062676113595249103719795)
                    ·
                      rfl

theorem cell23_6208663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 1, 4].length) (baseStart_6208663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208663 prefixEnd_6208663 := by exact prefixLift 6208663
  have htrace : WordTrace (prefixWord ++ tailWord_6208663) baseStart_6208663 baseEnd_6208663 := by
    simpa [prefixWord, tailWord_6208663, baseEnd_6208663] using wordTrace_append hprefix tailTrace_6208663
  have hstable : (prefixWord ++ tailWord_6208663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208663).length < 2 ^ (prefixWord ++ tailWord_6208663).sum := by decide
  have hdescent : baseEnd_6208663 < baseStart_6208663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208665 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 4, 1, 7]
def baseStart_6208665 : Nat := 118140960795 + 6208665 * 2 ^ 59
def prefixEnd_6208665 : Nat := 4983230072969 + 3 ^ 40 * 6208665 * 2
def baseEnd_6208665 : Nat := 3188029367747056303334375

theorem tailTrace_6208665 : CollatzResearch.WordTrace tailWord_6208665 prefixEnd_6208665 3188029367747056303334375 := by
  unfold tailWord_6208665
  simp only [CollatzResearch.WordTrace]
  refine ⟨226448616052074535407891449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150965744034716356938594299 226448616052074535407891449)
  ·
    refine ⟨169836462039055901555918587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226448616052074535407891449 169836462039055901555918587)
    ·
      refine ⟨254754693058583852333877881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169836462039055901555918587 254754693058583852333877881)
      ·
        refine ⟨191066019793937889250408411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254754693058583852333877881 191066019793937889250408411)
        ·
          refine ⟨286599029690906833875612617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191066019793937889250408411 286599029690906833875612617)
          ·
            refine ⟨214949272268180125406709463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286599029690906833875612617 214949272268180125406709463)
            ·
              refine ⟨322423908402270188110064195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214949272268180125406709463 322423908402270188110064195)
              ·
                refine ⟨483635862603405282165096293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322423908402270188110064195 483635862603405282165096293)
                ·
                  refine ⟨90681724238138490405955555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 483635862603405282165096293 90681724238138490405955555)
                  ·
                    refine ⟨136022586357207735608933333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90681724238138490405955555 136022586357207735608933333)
                    ·
                      refine ⟨3188029367747056303334375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136022586357207735608933333 3188029367747056303334375)
                      ·
                        rfl

theorem cell23_6208665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_6208665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208665 prefixEnd_6208665 := by exact prefixLift 6208665
  have htrace : WordTrace (prefixWord ++ tailWord_6208665) baseStart_6208665 baseEnd_6208665 := by
    simpa [prefixWord, tailWord_6208665, baseEnd_6208665] using wordTrace_append hprefix tailTrace_6208665
  have hstable : (prefixWord ++ tailWord_6208665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208665).length < 2 ^ (prefixWord ++ tailWord_6208665).sum := by decide
  have hdescent : baseEnd_6208665 < baseStart_6208665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208672 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 3, 5]
def baseStart_6208672 : Nat := 118140960795 + 6208672 * 2 ^ 59
def prefixEnd_6208672 : Nat := 4983230072969 + 3 ^ 40 * 6208672 * 2
def baseEnd_6208672 : Nat := 1062677654037212591982281

theorem tailTrace_6208672 : CollatzResearch.WordTrace tailWord_6208672 prefixEnd_6208672 1062677654037212591982281 := by
  unfold tailWord_6208672
  simp only [CollatzResearch.WordTrace]
  refine ⟨113224435681524587801698135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150965914242032783735597513 113224435681524587801698135)
  ·
    refine ⟨169836653522286881702547203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113224435681524587801698135 169836653522286881702547203)
    ·
      refine ⟨254754980283430322553820805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169836653522286881702547203 254754980283430322553820805)
      ·
        refine ⟨47766558803143185478841401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254754980283430322553820805 47766558803143185478841401)
        ·
          refine ⟨35824919102357389109131051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47766558803143185478841401 35824919102357389109131051)
          ·
            refine ⟨53737378653536083663696577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35824919102357389109131051 53737378653536083663696577)
            ·
              refine ⟨40303033990152062747772433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53737378653536083663696577 40303033990152062747772433)
              ·
                refine ⟨30227275492614047060829325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40303033990152062747772433 30227275492614047060829325)
                ·
                  refine ⟨11335228309730267647810997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30227275492614047060829325 11335228309730267647810997)
                  ·
                    refine ⟨1062677654037212591982281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11335228309730267647810997 1062677654037212591982281)
                    ·
                      rfl

theorem cell23_6208672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 3, 5].length) (baseStart_6208672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208672 prefixEnd_6208672 := by exact prefixLift 6208672
  have htrace : WordTrace (prefixWord ++ tailWord_6208672) baseStart_6208672 baseEnd_6208672 := by
    simpa [prefixWord, tailWord_6208672, baseEnd_6208672] using wordTrace_append hprefix tailTrace_6208672
  have hstable : (prefixWord ++ tailWord_6208672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208672).length < 2 ^ (prefixWord ++ tailWord_6208672).sum := by decide
  have hdescent : baseEnd_6208672 < baseStart_6208672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208676 : List Nat := [2, 3, 1, 2, 3, 3, 2, 1, 6]
def baseStart_6208676 : Nat := 118140960795 + 6208676 * 2 ^ 59
def prefixEnd_6208676 : Nat := 4983230072969 + 3 ^ 40 * 6208676 * 2
def baseEnd_6208676 : Nat := 354226112892695084477425

theorem tailTrace_6208676 : CollatzResearch.WordTrace tailWord_6208676 prefixEnd_6208676 354226112892695084477425 := by
  unfold tailWord_6208676
  simp only [CollatzResearch.WordTrace]
  refine ⟨113224508627517342143270941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150966011503356456191027921 113224508627517342143270941)
  ·
    refine ⟨42459190735319003303726603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113224508627517342143270941 42459190735319003303726603)
    ·
      refine ⟨63688786102978504955589905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42459190735319003303726603 63688786102978504955589905)
      ·
        refine ⟨47766589577233878716692429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63688786102978504955589905 47766589577233878716692429)
        ·
          refine ⟨17912471091462704518759661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47766589577233878716692429 17912471091462704518759661)
          ·
            refine ⟨6717176659298514194534873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17912471091462704518759661 6717176659298514194534873)
            ·
              refine ⟨5037882494473885645901155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6717176659298514194534873 5037882494473885645901155)
              ·
                refine ⟨7556823741710828468851733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5037882494473885645901155 7556823741710828468851733)
                ·
                  refine ⟨354226112892695084477425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7556823741710828468851733 354226112892695084477425)
                  ·
                    rfl

theorem cell23_6208676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_6208676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208676 prefixEnd_6208676 := by exact prefixLift 6208676
  have htrace : WordTrace (prefixWord ++ tailWord_6208676) baseStart_6208676 baseEnd_6208676 := by
    simpa [prefixWord, tailWord_6208676, baseEnd_6208676] using wordTrace_append hprefix tailTrace_6208676
  have hstable : (prefixWord ++ tailWord_6208676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208676).length < 2 ^ (prefixWord ++ tailWord_6208676).sum := by decide
  have hdescent : baseEnd_6208676 < baseStart_6208676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208689 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 3, 5]
def baseStart_6208689 : Nat := 118140960795 + 6208689 * 2 ^ 59
def prefixEnd_6208689 : Nat := 4983230072969 + 3 ^ 40 * 6208689 * 2
def baseEnd_6208689 : Nat := 1062680563760921403144755

theorem tailTrace_6208689 : CollatzResearch.WordTrace tailWord_6208689 prefixEnd_6208689 1062680563760921403144755 := by
  unfold tailWord_6208689
  simp only [CollatzResearch.WordTrace]
  refine ⟨226449491403987587506765121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150966327602658391671176747 226449491403987587506765121)
  ·
    refine ⟨169837118552990690630073841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226449491403987587506765121 169837118552990690630073841)
    ·
      refine ⟨127377838914743017972555381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169837118552990690630073841 127377838914743017972555381)
      ·
        refine ⟨11941672398257157934927067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127377838914743017972555381 11941672398257157934927067)
        ·
          refine ⟨17912508597385736902390601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11941672398257157934927067 17912508597385736902390601)
          ·
            refine ⟨13434381448039302676792951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17912508597385736902390601 13434381448039302676792951)
            ·
              refine ⟨20151572172058954015189427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13434381448039302676792951 20151572172058954015189427)
              ·
                refine ⟨30227358258088431022784141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20151572172058954015189427 30227358258088431022784141)
                ·
                  refine ⟨11335259346783161633544053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30227358258088431022784141 11335259346783161633544053)
                  ·
                    refine ⟨1062680563760921403144755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11335259346783161633544053 1062680563760921403144755)
                    ·
                      rfl

theorem cell23_6208689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_6208689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208689 prefixEnd_6208689 := by exact prefixLift 6208689
  have htrace : WordTrace (prefixWord ++ tailWord_6208689) baseStart_6208689 baseEnd_6208689 := by
    simpa [prefixWord, tailWord_6208689, baseEnd_6208689] using wordTrace_append hprefix tailTrace_6208689
  have hstable : (prefixWord ++ tailWord_6208689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208689).length < 2 ^ (prefixWord ++ tailWord_6208689).sum := by decide
  have hdescent : baseEnd_6208689 < baseStart_6208689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208710 : List Nat := [6, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_6208710 : Nat := 118140960795 + 6208710 * 2 ^ 59
def prefixEnd_6208710 : Nat := 4983230072969 + 3 ^ 40 * 6208710 * 2
def baseEnd_6208710 : Nat := 354228052708500958585741

theorem tailTrace_6208710 : CollatzResearch.WordTrace tailWord_6208710 prefixEnd_6208710 354228052708500958585741 := by
  unfold tailWord_6208710
  simp only [CollatzResearch.WordTrace]
  refine ⟨7076570541778484627914987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 150966838224607672062186389 7076570541778484627914987)
  ·
    refine ⟨10614855812667726941872481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7076570541778484627914987 10614855812667726941872481)
    ·
      refine ⟨7961141859500795206404361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10614855812667726941872481 7961141859500795206404361)
      ·
        refine ⟨5970856394625596404803271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7961141859500795206404361 5970856394625596404803271)
        ·
          refine ⟨8956284591938394607204907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5970856394625596404803271 8956284591938394607204907)
          ·
            refine ⟨13434426887907591910807361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8956284591938394607204907 13434426887907591910807361)
            ·
              refine ⟨10075820165930693933105521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13434426887907591910807361 10075820165930693933105521)
              ·
                refine ⟨7556865124448020449829141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10075820165930693933105521 7556865124448020449829141)
                ·
                  refine ⟨354228052708500958585741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7556865124448020449829141 354228052708500958585741)
                  ·
                    rfl

theorem cell23_6208710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_6208710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208710 prefixEnd_6208710 := by exact prefixLift 6208710
  have htrace : WordTrace (prefixWord ++ tailWord_6208710) baseStart_6208710 baseEnd_6208710 := by
    simpa [prefixWord, tailWord_6208710, baseEnd_6208710] using wordTrace_append hprefix tailTrace_6208710
  have hstable : (prefixWord ++ tailWord_6208710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208710).length < 2 ^ (prefixWord ++ tailWord_6208710).sum := by decide
  have hdescent : baseEnd_6208710 < baseStart_6208710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208759 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 6, 1, 3]
def baseStart_6208759 : Nat := 118140960795 + 6208759 * 2 ^ 59
def prefixEnd_6208759 : Nat := 4983230072969 + 3 ^ 40 * 6208759 * 2
def baseEnd_6208759 : Nat := 3188077634928578935558943

theorem tailTrace_6208759 : CollatzResearch.WordTrace tailWord_6208759 prefixEnd_6208759 3188077634928578935558943 := by
  unfold tailWord_6208759
  simp only [CollatzResearch.WordTrace]
  refine ⟨226452044513733989461813331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150968029675822659641208887 226452044513733989461813331)
  ·
    refine ⟨339678066770600984192719997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226452044513733989461813331 339678066770600984192719997)
    ·
      refine ⟨127379275038975369072269999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339678066770600984192719997 127379275038975369072269999)
      ·
        refine ⟨191068912558463053608404999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127379275038975369072269999 191068912558463053608404999)
        ·
          refine ⟨286603368837694580412607499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191068912558463053608404999 286603368837694580412607499)
          ·
            refine ⟨429905053256541870618911249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286603368837694580412607499 429905053256541870618911249)
            ·
              refine ⟨322428789942406402964183437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429905053256541870618911249 322428789942406402964183437)
              ·
                refine ⟨120910796228402401111568789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 322428789942406402964183437 120910796228402401111568789)
                ·
                  refine ⟨5667693573206362552104787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120910796228402401111568789 5667693573206362552104787)
                  ·
                    refine ⟨8501540359809543828157181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5667693573206362552104787 8501540359809543828157181)
                    ·
                      refine ⟨3188077634928578935558943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8501540359809543828157181 3188077634928578935558943)
                      ·
                        rfl

theorem cell23_6208759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 1, 3].length) (baseStart_6208759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208759 prefixEnd_6208759 := by exact prefixLift 6208759
  have htrace : WordTrace (prefixWord ++ tailWord_6208759) baseStart_6208759 baseEnd_6208759 := by
    simpa [prefixWord, tailWord_6208759, baseEnd_6208759] using wordTrace_append hprefix tailTrace_6208759
  have hstable : (prefixWord ++ tailWord_6208759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208759).length < 2 ^ (prefixWord ++ tailWord_6208759).sum := by decide
  have hdescent : baseEnd_6208759 < baseStart_6208759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208770 : List Nat := [3, 4, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_6208770 : Nat := 118140960795 + 6208770 * 2 ^ 59
def prefixEnd_6208770 : Nat := 4983230072969 + 3 ^ 40 * 6208770 * 2
def baseEnd_6208770 : Nat := 1062694427738592797507131

theorem tailTrace_6208770 : CollatzResearch.WordTrace tailWord_6208770 prefixEnd_6208770 1062694427738592797507131 := by
  unfold tailWord_6208770
  simp only [CollatzResearch.WordTrace]
  refine ⟨56613111429173534585115941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150968297144462758893642509 56613111429173534585115941)
  ·
    refine ⟨10614958392970037734709239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56613111429173534585115941 10614958392970037734709239)
    ·
      refine ⟨15922437589455056602063859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10614958392970037734709239 15922437589455056602063859)
      ·
        refine ⟨23883656384182584903095789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15922437589455056602063859 23883656384182584903095789)
        ·
          refine ⟨8956371144068469338660921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23883656384182584903095789 8956371144068469338660921)
          ·
            refine ⟨6717278358051352003995691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8956371144068469338660921 6717278358051352003995691)
            ·
              refine ⟨10075917537077028005993537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6717278358051352003995691 10075917537077028005993537)
              ·
                refine ⟨7556938152807771004495153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10075917537077028005993537 7556938152807771004495153)
                ·
                  refine ⟨5667703614605828253371365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7556938152807771004495153 5667703614605828253371365)
                  ·
                    refine ⟨1062694427738592797507131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5667703614605828253371365 1062694427738592797507131)
                    ·
                      rfl

theorem cell23_6208770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_6208770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208770 prefixEnd_6208770 := by exact prefixLift 6208770
  have htrace : WordTrace (prefixWord ++ tailWord_6208770) baseStart_6208770 baseEnd_6208770 := by
    simpa [prefixWord, tailWord_6208770, baseEnd_6208770] using wordTrace_append hprefix tailTrace_6208770
  have hstable : (prefixWord ++ tailWord_6208770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208770).length < 2 ^ (prefixWord ++ tailWord_6208770).sum := by decide
  have hdescent : baseEnd_6208770 < baseStart_6208770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208803 : List Nat := [1, 1, 1, 4, 2, 4, 2, 2, 1, 3, 2]
def baseStart_6208803 : Nat := 118140960795 + 6208803 * 2 ^ 59
def prefixEnd_6208803 : Nat := 4983230072969 + 3 ^ 40 * 6208803 * 2
def baseEnd_6208803 : Nat := 3188100228077376763408741

theorem tailTrace_6208803 : CollatzResearch.WordTrace tailWord_6208803 prefixEnd_6208803 3188100228077376763408741 := by
  unfold tailWord_6208803
  simp only [CollatzResearch.WordTrace]
  refine ⟨226453649325574584976415063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150969099550383056650943375 226453649325574584976415063)
  ·
    refine ⟨339680473988361877464622595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226453649325574584976415063 339680473988361877464622595)
    ·
      refine ⟨509520710982542816196933893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339680473988361877464622595 509520710982542816196933893)
      ·
        refine ⟨95535133309226778036925105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 509520710982542816196933893 95535133309226778036925105)
        ·
          refine ⟨71651349981920083527693829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95535133309226778036925105 71651349981920083527693829)
          ·
            refine ⟨13434628121610015661442593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 71651349981920083527693829 13434628121610015661442593)
            ·
              refine ⟨10075971091207511746081945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13434628121610015661442593 10075971091207511746081945)
              ·
                refine ⟨7556978318405633809561459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10075971091207511746081945 7556978318405633809561459)
                ·
                  refine ⟨11335467477608450714342189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7556978318405633809561459 11335467477608450714342189)
                  ·
                    refine ⟨4250800304103169017878321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11335467477608450714342189 4250800304103169017878321)
                    ·
                      refine ⟨3188100228077376763408741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4250800304103169017878321 3188100228077376763408741)
                      ·
                        rfl

theorem cell23_6208803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_6208803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208803 prefixEnd_6208803 := by exact prefixLift 6208803
  have htrace : WordTrace (prefixWord ++ tailWord_6208803) baseStart_6208803 baseEnd_6208803 := by
    simpa [prefixWord, tailWord_6208803, baseEnd_6208803] using wordTrace_append hprefix tailTrace_6208803
  have hstable : (prefixWord ++ tailWord_6208803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208803).length < 2 ^ (prefixWord ++ tailWord_6208803).sum := by decide
  have hdescent : baseEnd_6208803 < baseStart_6208803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208816 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 6, 2, 2]
def baseStart_6208816 : Nat := 118140960795 + 6208816 * 2 ^ 59
def prefixEnd_6208816 : Nat := 4983230072969 + 3 ^ 40 * 6208816 * 2
def baseEnd_6208816 : Nat := 3188106903325885212546181

theorem tailTrace_6208816 : CollatzResearch.WordTrace tailWord_6208816 prefixEnd_6208816 3188106903325885212546181 := by
  unfold tailWord_6208816
  simp only [CollatzResearch.WordTrace]
  refine ⟨113227061737263744098319151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150969415649684992131092201 113227061737263744098319151)
  ·
    refine ⟨169840592605895616147478727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113227061737263744098319151 169840592605895616147478727)
    ·
      refine ⟨254760888908843424221218091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169840592605895616147478727 254760888908843424221218091)
      ·
        refine ⟨382141333363265136331827137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254760888908843424221218091 382141333363265136331827137)
        ·
          refine ⟨286606000022448852248870353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382141333363265136331827137 286606000022448852248870353)
          ·
            refine ⟨214954500016836639186652765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 286606000022448852248870353 214954500016836639186652765)
            ·
              refine ⟨80607937506313739694994787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214954500016836639186652765 80607937506313739694994787)
              ·
                refine ⟨120911906259470609542492181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80607937506313739694994787 120911906259470609542492181)
                ·
                  refine ⟨5667745605912684822304321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 120911906259470609542492181 5667745605912684822304321)
                  ·
                    refine ⟨4250809204434513616728241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5667745605912684822304321 4250809204434513616728241)
                    ·
                      refine ⟨3188106903325885212546181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4250809204434513616728241 3188106903325885212546181)
                      ·
                        rfl

theorem cell23_6208816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 6, 2, 2].length) (baseStart_6208816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208816 prefixEnd_6208816 := by exact prefixLift 6208816
  have htrace : WordTrace (prefixWord ++ tailWord_6208816) baseStart_6208816 baseEnd_6208816 := by
    simpa [prefixWord, tailWord_6208816, baseEnd_6208816] using wordTrace_append hprefix tailTrace_6208816
  have hstable : (prefixWord ++ tailWord_6208816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208816).length < 2 ^ (prefixWord ++ tailWord_6208816).sum := by decide
  have hdescent : baseEnd_6208816 < baseStart_6208816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208819 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 5]
def baseStart_6208819 : Nat := 118140960795 + 6208819 * 2 ^ 59
def prefixEnd_6208819 : Nat := 4983230072969 + 3 ^ 40 * 6208819 * 2
def baseEnd_6208819 : Nat := 3188108443767848700808667

theorem tailTrace_6208819 : CollatzResearch.WordTrace tailWord_6208819 prefixEnd_6208819 3188108443767848700808667 := by
  unfold tailWord_6208819
  simp only [CollatzResearch.WordTrace]
  refine ⟨226454232893516619708997511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150969488595677746472665007 226454232893516619708997511)
  ·
    refine ⟨339681349340274929563496267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226454232893516619708997511 339681349340274929563496267)
    ·
      refine ⟨509522024010412394345244401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339681349340274929563496267 509522024010412394345244401)
      ·
        refine ⟨382141518007809295758933301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 509522024010412394345244401 382141518007809295758933301)
        ·
          refine ⟨35825767313232121477399997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 382141518007809295758933301 35825767313232121477399997)
          ·
            refine ⟨13434662742462045554024999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35825767313232121477399997 13434662742462045554024999)
            ·
              refine ⟨20151994113693068331037499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13434662742462045554024999 20151994113693068331037499)
              ·
                refine ⟨30227991170539602496556249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20151994113693068331037499 30227991170539602496556249)
                ·
                  refine ⟨22670993377904701872417187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30227991170539602496556249 22670993377904701872417187)
                  ·
                    refine ⟨34006490066857052808625781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22670993377904701872417187 34006490066857052808625781)
                    ·
                      refine ⟨3188108443767848700808667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34006490066857052808625781 3188108443767848700808667)
                      ·
                        rfl

theorem cell23_6208819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 5].length) (baseStart_6208819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208819 prefixEnd_6208819 := by exact prefixLift 6208819
  have htrace : WordTrace (prefixWord ++ tailWord_6208819) baseStart_6208819 baseEnd_6208819 := by
    simpa [prefixWord, tailWord_6208819, baseEnd_6208819] using wordTrace_append hprefix tailTrace_6208819
  have hstable : (prefixWord ++ tailWord_6208819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208819).length < 2 ^ (prefixWord ++ tailWord_6208819).sum := by decide
  have hdescent : baseEnd_6208819 < baseStart_6208819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208832 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 7]
def baseStart_6208832 : Nat := 118140960795 + 6208832 * 2 ^ 59
def prefixEnd_6208832 : Nat := 4983230072969 + 3 ^ 40 * 6208832 * 2
def baseEnd_6208832 : Nat := 3188115119016357149946107

theorem tailTrace_6208832 : CollatzResearch.WordTrace tailWord_6208832 prefixEnd_6208832 3188115119016357149946107 := by
  unfold tailWord_6208832
  simp only [CollatzResearch.WordTrace]
  refine ⟨113227353521234761464610375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150969804694979681952813833 113227353521234761464610375)
  ·
    refine ⟨169841030281852142196915563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113227353521234761464610375 169841030281852142196915563)
    ·
      refine ⟨254761545422778213295373345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169841030281852142196915563 254761545422778213295373345)
      ·
        refine ⟨191071159067083659971530009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254761545422778213295373345 191071159067083659971530009)
        ·
          refine ⟨143303369300312744978647507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191071159067083659971530009 143303369300312744978647507)
          ·
            refine ⟨214955053950469117467971261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143303369300312744978647507 214955053950469117467971261)
            ·
              refine ⟨80608145231425919050489223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214955053950469117467971261 80608145231425919050489223)
              ·
                refine ⟨120912217847138878575733835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80608145231425919050489223 120912217847138878575733835)
                ·
                  refine ⟨181368326770708317863600753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120912217847138878575733835 181368326770708317863600753)
                  ·
                    refine ⟨136026245078031238397700565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 181368326770708317863600753 136026245078031238397700565)
                    ·
                      refine ⟨3188115119016357149946107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136026245078031238397700565 3188115119016357149946107)
                      ·
                        rfl

theorem cell23_6208832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_6208832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208832 prefixEnd_6208832 := by exact prefixLift 6208832
  have htrace : WordTrace (prefixWord ++ tailWord_6208832) baseStart_6208832 baseEnd_6208832 := by
    simpa [prefixWord, tailWord_6208832, baseEnd_6208832] using wordTrace_append hprefix tailTrace_6208832
  have hstable : (prefixWord ++ tailWord_6208832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208832).length < 2 ^ (prefixWord ++ tailWord_6208832).sum := by decide
  have hdescent : baseEnd_6208832 < baseStart_6208832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208839 : List Nat := [1, 1, 4, 1, 2, 3, 3, 1, 7]
def baseStart_6208839 : Nat := 118140960795 + 6208839 * 2 ^ 59
def prefixEnd_6208839 : Nat := 4983230072969 + 3 ^ 40 * 6208839 * 2
def baseEnd_6208839 : Nat := 354235412597882069173175

theorem tailTrace_6208839 : CollatzResearch.WordTrace tailWord_6208839 prefixEnd_6208839 354235412597882069173175 := by
  unfold tailWord_6208839
  simp only [CollatzResearch.WordTrace]
  refine ⟨226454962353444163124725571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150969974902296108749817047 226454962353444163124725571)
  ·
    refine ⟨339682443530166244687088357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226454962353444163124725571 339682443530166244687088357)
    ·
      refine ⟨63690458161906170878829067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 339682443530166244687088357 63690458161906170878829067)
      ·
        refine ⟨95535687242859256318243601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63690458161906170878829067 95535687242859256318243601)
        ·
          refine ⟨71651765432144442238682701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95535687242859256318243601 71651765432144442238682701)
          ·
            refine ⟨26869412037054165839506013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71651765432144442238682701 26869412037054165839506013)
            ·
              refine ⟨10076029513895312189814755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26869412037054165839506013 10076029513895312189814755)
              ·
                refine ⟨15114044270842968284722133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10076029513895312189814755 15114044270842968284722133)
                ·
                  refine ⟨354235412597882069173175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15114044270842968284722133 354235412597882069173175)
                  ·
                    rfl

theorem cell23_6208839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 7].length) (baseStart_6208839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208839 prefixEnd_6208839 := by exact prefixLift 6208839
  have htrace : WordTrace (prefixWord ++ tailWord_6208839) baseStart_6208839 baseEnd_6208839 := by
    simpa [prefixWord, tailWord_6208839, baseEnd_6208839] using wordTrace_append hprefix tailTrace_6208839
  have hstable : (prefixWord ++ tailWord_6208839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208839).length < 2 ^ (prefixWord ++ tailWord_6208839).sum := by decide
  have hdescent : baseEnd_6208839 < baseStart_6208839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208849 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 1, 5, 3]
def baseStart_6208849 : Nat := 118140960795 + 6208849 * 2 ^ 59
def prefixEnd_6208849 : Nat := 4983230072969 + 3 ^ 40 * 6208849 * 2
def baseEnd_6208849 : Nat := 3188123848187483583433529

theorem tailTrace_6208849 : CollatzResearch.WordTrace tailWord_6208849 prefixEnd_6208849 3188123848187483583433529 := by
  unfold tailWord_6208849
  simp only [CollatzResearch.WordTrace]
  refine ⟨226455327083407934832589601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150970218055605289888393067 226455327083407934832589601)
  ·
    refine ⟨169841495312555951124442201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226455327083407934832589601 169841495312555951124442201)
    ·
      refine ⟨127381121484416963343331651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169841495312555951124442201 127381121484416963343331651)
      ·
        refine ⟨191071682226625445014997477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127381121484416963343331651 191071682226625445014997477)
        ·
          refine ⟨35825940417492270940312027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191071682226625445014997477 35825940417492270940312027)
          ·
            refine ⟨53738910626238406410468041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35825940417492270940312027 53738910626238406410468041)
            ·
              refine ⟨40304182969678804807851031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53738910626238406410468041 40304182969678804807851031)
              ·
                refine ⟨60456274454518207211776547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40304182969678804807851031 60456274454518207211776547)
                ·
                  refine ⟨90684411681777310817664821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60456274454518207211776547 90684411681777310817664821)
                  ·
                    refine ⟨8501663595166622889156077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90684411681777310817664821 8501663595166622889156077)
                    ·
                      refine ⟨3188123848187483583433529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8501663595166622889156077 3188123848187483583433529)
                      ·
                        rfl

theorem cell23_6208849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_6208849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208849 prefixEnd_6208849 := by exact prefixLift 6208849
  have htrace : WordTrace (prefixWord ++ tailWord_6208849) baseStart_6208849 baseEnd_6208849 := by
    simpa [prefixWord, tailWord_6208849, baseEnd_6208849] using wordTrace_append hprefix tailTrace_6208849
  have hstable : (prefixWord ++ tailWord_6208849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208849).length < 2 ^ (prefixWord ++ tailWord_6208849).sum := by decide
  have hdescent : baseEnd_6208849 < baseStart_6208849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208854 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_6208854 : Nat := 118140960795 + 6208854 * 2 ^ 59
def prefixEnd_6208854 : Nat := 4983230072969 + 3 ^ 40 * 6208854 * 2
def baseEnd_6208854 : Nat := 3188126415590756063871007

theorem tailTrace_6208854 : CollatzResearch.WordTrace tailWord_6208854 prefixEnd_6208854 3188126415590756063871007 := by
  unfold tailWord_6208854
  simp only [CollatzResearch.WordTrace]
  refine ⟨14153469340524363792907601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150970339632259880457681077 14153469340524363792907601)
  ·
    refine ⟨10615102005393272844680701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14153469340524363792907601 10615102005393272844680701)
    ·
      refine ⟨3980663252022477316755263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10615102005393272844680701 3980663252022477316755263)
      ·
        refine ⟨5970994878033715975132895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3980663252022477316755263 5970994878033715975132895)
        ·
          refine ⟨8956492317050573962699343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5970994878033715975132895 8956492317050573962699343)
          ·
            refine ⟨13434738475575860944049015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8956492317050573962699343 13434738475575860944049015)
            ·
              refine ⟨20152107713363791416073523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13434738475575860944049015 20152107713363791416073523)
              ·
                refine ⟨30228161570045687124110285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20152107713363791416073523 30228161570045687124110285)
                ·
                  refine ⟨11335560588767132671541357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30228161570045687124110285 11335560588767132671541357)
                  ·
                    refine ⟨4250835220787674751828009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11335560588767132671541357 4250835220787674751828009)
                    ·
                      refine ⟨3188126415590756063871007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4250835220787674751828009 3188126415590756063871007)
                      ·
                        rfl

theorem cell23_6208854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_6208854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208854 prefixEnd_6208854 := by exact prefixLift 6208854
  have htrace : WordTrace (prefixWord ++ tailWord_6208854) baseStart_6208854 baseEnd_6208854 := by
    simpa [prefixWord, tailWord_6208854, baseEnd_6208854] using wordTrace_append hprefix tailTrace_6208854
  have hstable : (prefixWord ++ tailWord_6208854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208854).length < 2 ^ (prefixWord ++ tailWord_6208854).sum := by decide
  have hdescent : baseEnd_6208854 < baseStart_6208854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208920 : List Nat := [2, 1, 2, 5, 3, 1, 1, 1, 2, 5]
def baseStart_6208920 : Nat := 118140960795 + 6208920 * 2 ^ 59
def prefixEnd_6208920 : Nat := 4983230072969 + 3 ^ 40 * 6208920 * 2
def baseEnd_6208920 : Nat := 1062720101771317601881901

theorem tailTrace_6208920 : CollatzResearch.WordTrace tailWord_6208920 prefixEnd_6208920 1062720101771317601881901 := by
  unfold tailWord_6208920
  simp only [CollatzResearch.WordTrace]
  refine ⟨113228958333075356979212107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150971944444100475972282809 113228958333075356979212107)
  ·
    refine ⟨169843437499613035468818161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113228958333075356979212107 169843437499613035468818161)
    ·
      refine ⟨127382578124709776601613621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169843437499613035468818161 127382578124709776601613621)
      ·
        refine ⟨11942116699191541556401277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 127382578124709776601613621 11942116699191541556401277)
        ·
          refine ⟨4478293762196828083650479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11942116699191541556401277 4478293762196828083650479)
          ·
            refine ⟨6717440643295242125475719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4478293762196828083650479 6717440643295242125475719)
            ·
              refine ⟨10076160964942863188213579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6717440643295242125475719 10076160964942863188213579)
              ·
                refine ⟨15114241447414294782320369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10076160964942863188213579 15114241447414294782320369)
                ·
                  refine ⟨11335681085560721086740277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15114241447414294782320369 11335681085560721086740277)
                  ·
                    refine ⟨1062720101771317601881901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11335681085560721086740277 1062720101771317601881901)
                    ·
                      rfl

theorem cell23_6208920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 2, 5].length) (baseStart_6208920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208920 prefixEnd_6208920 := by exact prefixLift 6208920
  have htrace : WordTrace (prefixWord ++ tailWord_6208920) baseStart_6208920 baseEnd_6208920 := by
    simpa [prefixWord, tailWord_6208920, baseEnd_6208920] using wordTrace_append hprefix tailTrace_6208920
  have hstable : (prefixWord ++ tailWord_6208920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208920).length < 2 ^ (prefixWord ++ tailWord_6208920).sum := by decide
  have hdescent : baseEnd_6208920 < baseStart_6208920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6208959 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 5, 5]
def baseStart_6208959 : Nat := 118140960795 + 6208959 * 2 ^ 59
def prefixEnd_6208959 : Nat := 4983230072969 + 3 ^ 40 * 6208959 * 2
def baseEnd_6208959 : Nat := 1062726777019826051019341

theorem tailTrace_6208959 : CollatzResearch.WordTrace tailWord_6208959 prefixEnd_6208959 1062726777019826051019341 := by
  unfold tailWord_6208959
  simp only [CollatzResearch.WordTrace]
  refine ⟨226459339113009423619093931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150972892742006282412729287 226459339113009423619093931)
  ·
    refine ⟨339689008669514135428640897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226459339113009423619093931 339689008669514135428640897)
    ·
      refine ⟨254766756502135601571480673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339689008669514135428640897 254766756502135601571480673)
      ·
        refine ⟨191075067376601701178610505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254766756502135601571480673 191075067376601701178610505)
        ·
          refine ⟨143306300532451275883957879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191075067376601701178610505 143306300532451275883957879)
          ·
            refine ⟨214959450798676913825936819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143306300532451275883957879 214959450798676913825936819)
            ·
              refine ⟨322439176198015370738905229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214959450798676913825936819 322439176198015370738905229)
              ·
                refine ⟨120914691074255764027089461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 322439176198015370738905229 120914691074255764027089461)
                ·
                  refine ⟨11335752288211477877539637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 120914691074255764027089461 11335752288211477877539637)
                  ·
                    refine ⟨1062726777019826051019341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11335752288211477877539637 1062726777019826051019341)
                    ·
                      rfl

theorem cell23_6208959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 5].length) (baseStart_6208959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6208959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6208959 prefixEnd_6208959 := by exact prefixLift 6208959
  have htrace : WordTrace (prefixWord ++ tailWord_6208959) baseStart_6208959 baseEnd_6208959 := by
    simpa [prefixWord, tailWord_6208959, baseEnd_6208959] using wordTrace_append hprefix tailTrace_6208959
  have hstable : (prefixWord ++ tailWord_6208959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6208959).length < 2 ^ (prefixWord ++ tailWord_6208959).sum := by decide
  have hdescent : baseEnd_6208959 < baseStart_6208959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6208959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209016 : List Nat := [2, 1, 2, 1, 1, 5, 2, 2, 1, 1, 5]
def baseStart_6209016 : Nat := 118140960795 + 6209016 * 2 ^ 59
def prefixEnd_6209016 : Nat := 4983230072969 + 3 ^ 40 * 6209016 * 2
def baseEnd_6209016 : Nat := 3188209599456784430045261

theorem tailTrace_6209016 : CollatzResearch.WordTrace tailWord_6209016 prefixEnd_6209016 3188209599456784430045261 := by
  unfold tailWord_6209016
  simp only [CollatzResearch.WordTrace]
  refine ⟨113230709036901461176959451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150974278715868614902612601 113230709036901461176959451)
  ·
    refine ⟨169846063555352191765439177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113230709036901461176959451 169846063555352191765439177)
    ·
      refine ⟨127384547666514143824079383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169846063555352191765439177 127384547666514143824079383)
      ·
        refine ⟨191076821499771215736119075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127384547666514143824079383 191076821499771215736119075)
        ·
          refine ⟨286615232249656823604178613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191076821499771215736119075 286615232249656823604178613)
          ·
            refine ⟨26870178023405327212891745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 286615232249656823604178613 26870178023405327212891745)
            ·
              refine ⟨20152633517553995409668809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26870178023405327212891745 20152633517553995409668809)
              ·
                refine ⟨15114475138165496557251607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20152633517553995409668809 15114475138165496557251607)
                ·
                  refine ⟨22671712707248244835877411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15114475138165496557251607 22671712707248244835877411)
                  ·
                    refine ⟨34007569060872367253816117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22671712707248244835877411 34007569060872367253816117)
                    ·
                      refine ⟨3188209599456784430045261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34007569060872367253816117 3188209599456784430045261)
                      ·
                        rfl

theorem cell23_6209016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_6209016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209016 prefixEnd_6209016 := by exact prefixLift 6209016
  have htrace : WordTrace (prefixWord ++ tailWord_6209016) baseStart_6209016 baseEnd_6209016 := by
    simpa [prefixWord, tailWord_6209016, baseEnd_6209016] using wordTrace_append hprefix tailTrace_6209016
  have hstable : (prefixWord ++ tailWord_6209016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209016).length < 2 ^ (prefixWord ++ tailWord_6209016).sum := by decide
  have hdescent : baseEnd_6209016 < baseStart_6209016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209039 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 6]
def baseStart_6209039 : Nat := 118140960795 + 6209039 * 2 ^ 59
def prefixEnd_6209039 : Nat := 4983230072969 + 3 ^ 40 * 6209039 * 2
def baseEnd_6209039 : Nat := 3188221409511837840057655

theorem tailTrace_6209039 : CollatzResearch.WordTrace tailWord_6209039 prefixEnd_6209039 3188221409511837840057655 := by
  unfold tailWord_6209039
  simp only [CollatzResearch.WordTrace]
  refine ⟨226462256952719597282006171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150974837968479731521337447 226462256952719597282006171)
  ·
    refine ⟨339693385429079395923009257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226462256952719597282006171 339693385429079395923009257)
    ·
      refine ⟨254770039071809546942256943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339693385429079395923009257 254770039071809546942256943)
      ·
        refine ⟨382155058607714320413385415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254770039071809546942256943 382155058607714320413385415)
        ·
          refine ⟨573232587911571480620078123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382155058607714320413385415 573232587911571480620078123)
          ·
            refine ⟨859848881867357220930117185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573232587911571480620078123 859848881867357220930117185)
            ·
              refine ⟨644886661400517915697587889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 859848881867357220930117185 644886661400517915697587889)
              ·
                refine ⟨483664996050388436773190917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 644886661400517915697587889 483664996050388436773190917)
                ·
                  refine ⟨90687186759447831894973297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 483664996050388436773190917 90687186759447831894973297)
                  ·
                    refine ⟨68015390069585873921229973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90687186759447831894973297 68015390069585873921229973)
                    ·
                      refine ⟨3188221409511837840057655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68015390069585873921229973 3188221409511837840057655)
                      ·
                        rfl

theorem cell23_6209039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_6209039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209039 prefixEnd_6209039 := by exact prefixLift 6209039
  have htrace : WordTrace (prefixWord ++ tailWord_6209039) baseStart_6209039 baseEnd_6209039 := by
    simpa [prefixWord, tailWord_6209039, baseEnd_6209039] using wordTrace_append hprefix tailTrace_6209039
  have hstable : (prefixWord ++ tailWord_6209039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209039).length < 2 ^ (prefixWord ++ tailWord_6209039).sum := by decide
  have hdescent : baseEnd_6209039 < baseStart_6209039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209049 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 3, 9]
def baseStart_6209049 : Nat := 118140960795 + 6209049 * 2 ^ 59
def prefixEnd_6209049 : Nat := 4983230072969 + 3 ^ 40 * 6209049 * 2
def baseEnd_6209049 : Nat := 1062742181439460933644203

theorem tailTrace_6209049 : CollatzResearch.WordTrace tailWord_6209049 prefixEnd_6209049 1062742181439460933644203 := by
  unfold tailWord_6209049
  simp only [CollatzResearch.WordTrace]
  refine ⟨226462621682683368989870201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150975081121788912659913467 226462621682683368989870201)
  ·
    refine ⟨169846966262012526742402651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226462621682683368989870201 169846966262012526742402651)
    ·
      refine ⟨254770449393018790113603977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169846966262012526742402651 254770449393018790113603977)
      ·
        refine ⟨191077837044764092585202983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254770449393018790113603977 191077837044764092585202983)
        ·
          refine ⟨286616755567146138877804475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191077837044764092585202983 286616755567146138877804475)
          ·
            refine ⟨429925133350719208316706713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286616755567146138877804475 429925133350719208316706713)
            ·
              refine ⟨322443850013039406237530035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 429925133350719208316706713 322443850013039406237530035)
              ·
                refine ⟨483665775019559109356295053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322443850013039406237530035 483665775019559109356295053)
                ·
                  refine ⟨181374665632334666008610645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 483665775019559109356295053 181374665632334666008610645)
                  ·
                    refine ⟨1062742181439460933644203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 181374665632334666008610645 1062742181439460933644203)
                    ·
                      rfl

theorem cell23_6209049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 9].length) (baseStart_6209049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209049 prefixEnd_6209049 := by exact prefixLift 6209049
  have htrace : WordTrace (prefixWord ++ tailWord_6209049) baseStart_6209049 baseEnd_6209049 := by
    simpa [prefixWord, tailWord_6209049, baseEnd_6209049] using wordTrace_append hprefix tailTrace_6209049
  have hstable : (prefixWord ++ tailWord_6209049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209049).length < 2 ^ (prefixWord ++ tailWord_6209049).sum := by decide
  have hdescent : baseEnd_6209049 < baseStart_6209049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209066 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 1, 9]
def baseStart_6209066 : Nat := 118140960795 + 6209066 * 2 ^ 59
def prefixEnd_6209066 : Nat := 4983230072969 + 3 ^ 40 * 6209066 * 2
def baseEnd_6209066 : Nat := 1062745091163169744806677

theorem tailTrace_6209066 : CollatzResearch.WordTrace tailWord_6209066 prefixEnd_6209066 1062745091163169744806677 := by
  unfold tailWord_6209066
  simp only [CollatzResearch.WordTrace]
  refine ⟨56615810430905445223309763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150975494482414520595492701 56615810430905445223309763)
  ·
    refine ⟨84923715646358167834964645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56615810430905445223309763 84923715646358167834964645)
    ·
      refine ⟨15923196683692156469055871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84923715646358167834964645 15923196683692156469055871)
      ·
        refine ⟨23884795025538234703583807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15923196683692156469055871 23884795025538234703583807)
        ·
          refine ⟨35827192538307352055375711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23884795025538234703583807 35827192538307352055375711)
          ·
            refine ⟨53740788807461028083063567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35827192538307352055375711 53740788807461028083063567)
            ·
              refine ⟨80611183211191542124595351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53740788807461028083063567 80611183211191542124595351)
              ·
                refine ⟨120916774816787313186893027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80611183211191542124595351 120916774816787313186893027)
                ·
                  refine ⟨181375162225180969780339541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120916774816787313186893027 181375162225180969780339541)
                  ·
                    refine ⟨1062745091163169744806677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 181375162225180969780339541 1062745091163169744806677)
                    ·
                      rfl

theorem cell23_6209066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_6209066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209066 prefixEnd_6209066 := by exact prefixLift 6209066
  have htrace : WordTrace (prefixWord ++ tailWord_6209066) baseStart_6209066 baseEnd_6209066 := by
    simpa [prefixWord, tailWord_6209066, baseEnd_6209066] using wordTrace_append hprefix tailTrace_6209066
  have hstable : (prefixWord ++ tailWord_6209066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209066).length < 2 ^ (prefixWord ++ tailWord_6209066).sum := by decide
  have hdescent : baseEnd_6209066 < baseStart_6209066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209080 : List Nat := [2, 1, 2, 1, 4, 2, 2, 3, 2, 1, 3]
def baseStart_6209080 : Nat := 118140960795 + 6209080 * 2 ^ 59
def prefixEnd_6209080 : Nat := 4983230072969 + 3 ^ 40 * 6209080 * 2
def baseEnd_6209080 : Nat := 3188242462218672179644967

theorem tailTrace_6209080 : CollatzResearch.WordTrace tailWord_6209080 prefixEnd_6209080 3188242462218672179644967 := by
  unfold tailWord_6209080
  simp only [CollatzResearch.WordTrace]
  refine ⟨113231876172785530642124347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150975834897047374189499129 113231876172785530642124347)
  ·
    refine ⟨169847814259178295963186521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113231876172785530642124347 169847814259178295963186521)
    ·
      refine ⟨127385860694383721972389891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169847814259178295963186521 127385860694383721972389891)
      ·
        refine ⟨191078791041575582958584837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127385860694383721972389891 191078791041575582958584837)
        ·
          refine ⟨35827273320295421804734657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191078791041575582958584837 35827273320295421804734657)
          ·
            refine ⟨26870454990221566353550993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35827273320295421804734657 26870454990221566353550993)
            ·
              refine ⟨20152841242666174765163245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26870454990221566353550993 20152841242666174765163245)
              ·
                refine ⟨7557315465999815536936217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20152841242666174765163245 7557315465999815536936217)
                ·
                  refine ⟨5667986599499861652702163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7557315465999815536936217 5667986599499861652702163)
                  ·
                    refine ⟨8501979899249792479053245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5667986599499861652702163 8501979899249792479053245)
                    ·
                      refine ⟨3188242462218672179644967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8501979899249792479053245 3188242462218672179644967)
                      ·
                        rfl

theorem cell23_6209080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 2, 1, 3].length) (baseStart_6209080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209080 prefixEnd_6209080 := by exact prefixLift 6209080
  have htrace : WordTrace (prefixWord ++ tailWord_6209080) baseStart_6209080 baseEnd_6209080 := by
    simpa [prefixWord, tailWord_6209080, baseEnd_6209080] using wordTrace_append hprefix tailTrace_6209080
  have hstable : (prefixWord ++ tailWord_6209080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209080).length < 2 ^ (prefixWord ++ tailWord_6209080).sum := by decide
  have hdescent : baseEnd_6209080 < baseStart_6209080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209101 : List Nat := [1, 6, 1, 1, 4, 1, 2, 1, 1, 2, 3]
def baseStart_6209101 : Nat := 118140960795 + 6209101 * 2 ^ 59
def prefixEnd_6209101 : Nat := 4983230072969 + 3 ^ 40 * 6209101 * 2
def baseEnd_6209101 : Nat := 3188253245312416597482371

theorem tailTrace_6209101 : CollatzResearch.WordTrace tailWord_6209101 prefixEnd_6209101 3188253245312416597482371 := by
  unfold tailWord_6209101
  simp only [CollatzResearch.WordTrace]
  refine ⟨226464518278494981870763157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150976345518996654580508771 226464518278494981870763157)
  ·
    refine ⟨10615524294304452275192023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 226464518278494981870763157 10615524294304452275192023)
    ·
      refine ⟨15923286441456678412788035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10615524294304452275192023 15923286441456678412788035)
      ·
        refine ⟨23884929662185017619182053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15923286441456678412788035 23884929662185017619182053)
        ·
          refine ⟨4478424311659690803596635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23884929662185017619182053 4478424311659690803596635)
          ·
            refine ⟨6717636467489536205394953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4478424311659690803596635 6717636467489536205394953)
            ·
              refine ⟨5038227350617152154046215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6717636467489536205394953 5038227350617152154046215)
              ·
                refine ⟨7557341025925728231069323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5038227350617152154046215 7557341025925728231069323)
                ·
                  refine ⟨11336011538888592346603985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7557341025925728231069323 11336011538888592346603985)
                  ·
                    refine ⟨8502008654166444259952989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11336011538888592346603985 8502008654166444259952989)
                    ·
                      refine ⟨3188253245312416597482371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8502008654166444259952989 3188253245312416597482371)
                      ·
                        rfl

theorem cell23_6209101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_6209101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209101 prefixEnd_6209101 := by exact prefixLift 6209101
  have htrace : WordTrace (prefixWord ++ tailWord_6209101) baseStart_6209101 baseEnd_6209101 := by
    simpa [prefixWord, tailWord_6209101, baseEnd_6209101] using wordTrace_append hprefix tailTrace_6209101
  have hstable : (prefixWord ++ tailWord_6209101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209101).length < 2 ^ (prefixWord ++ tailWord_6209101).sum := by decide
  have hdescent : baseEnd_6209101 < baseStart_6209101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209196 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 5]
def baseStart_6209196 : Nat := 118140960795 + 6209196 * 2 ^ 59
def prefixEnd_6209196 : Nat := 4983230072969 + 3 ^ 40 * 6209196 * 2
def baseEnd_6209196 : Nat := 3188302025974593725794433

theorem tailTrace_6209196 : CollatzResearch.WordTrace tailWord_6209196 prefixEnd_6209196 3188302025974593725794433 := by
  unfold tailWord_6209196
  simp only [CollatzResearch.WordTrace]
  refine ⟨113233991606575406547735721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150978655475433875396980961 113233991606575406547735721)
  ·
    refine ⟨84925493704931554910801791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113233991606575406547735721 84925493704931554910801791)
    ·
      refine ⟨127388240557397332366202687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84925493704931554910801791 127388240557397332366202687)
      ·
        refine ⟨191082360836095998549304031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127388240557397332366202687 191082360836095998549304031)
        ·
          refine ⟨286623541254143997823956047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191082360836095998549304031 286623541254143997823956047)
          ·
            refine ⟨429935311881215996735934071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286623541254143997823956047 429935311881215996735934071)
            ·
              refine ⟨644902967821823995103901107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429935311881215996735934071 644902967821823995103901107)
              ·
                refine ⟨967354451732735992655851661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 644902967821823995103901107 967354451732735992655851661)
                ·
                  refine ⟨362757919399775997245944373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 967354451732735992655851661 362757919399775997245944373)
                  ·
                    refine ⟨34008554943728999741807285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 362757919399775997245944373 34008554943728999741807285)
                    ·
                      refine ⟨3188302025974593725794433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34008554943728999741807285 3188302025974593725794433)
                      ·
                        rfl

theorem cell23_6209196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_6209196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209196 prefixEnd_6209196 := by exact prefixLift 6209196
  have htrace : WordTrace (prefixWord ++ tailWord_6209196) baseStart_6209196 baseEnd_6209196 := by
    simpa [prefixWord, tailWord_6209196, baseEnd_6209196] using wordTrace_append hprefix tailTrace_6209196
  have hstable : (prefixWord ++ tailWord_6209196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209196).length < 2 ^ (prefixWord ++ tailWord_6209196).sum := by decide
  have hdescent : baseEnd_6209196 < baseStart_6209196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209203 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 5, 4]
def baseStart_6209203 : Nat := 118140960795 + 6209203 * 2 ^ 59
def prefixEnd_6209203 : Nat := 4983230072969 + 3 ^ 40 * 6209203 * 2
def baseEnd_6209203 : Nat := 1062768540113058399468967

theorem tailTrace_6209203 : CollatzResearch.WordTrace tailWord_6209203 prefixEnd_6209203 1062768540113058399468967 := by
  unfold tailWord_6209203
  simp only [CollatzResearch.WordTrace]
  refine ⟨226468238524125453290976263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150978825682750302193984175 226468238524125453290976263)
  ·
    refine ⟨339702357786188179936464395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226468238524125453290976263 339702357786188179936464395)
    ·
      refine ⟨509553536679282269904696593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339702357786188179936464395 509553536679282269904696593)
      ·
        refine ⟨382165152509461702428522445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 509553536679282269904696593 382165152509461702428522445)
        ·
          refine ⟨143311932191048138410695917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382165152509461702428522445 143311932191048138410695917)
          ·
            refine ⟨53741974571643051904010969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143311932191048138410695917 53741974571643051904010969)
            ·
              refine ⟨40306480928732288928008227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53741974571643051904010969 40306480928732288928008227)
              ·
                refine ⟨60459721393098433392012341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40306480928732288928008227 60459721393098433392012341)
                ·
                  refine ⟨5668098880602978130501157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60459721393098433392012341 5668098880602978130501157)
                  ·
                    refine ⟨1062768540113058399468967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5668098880602978130501157 1062768540113058399468967)
                    ·
                      rfl

theorem cell23_6209203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 4].length) (baseStart_6209203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209203 prefixEnd_6209203 := by exact prefixLift 6209203
  have htrace : WordTrace (prefixWord ++ tailWord_6209203) baseStart_6209203 baseEnd_6209203 := by
    simpa [prefixWord, tailWord_6209203, baseEnd_6209203] using wordTrace_append hprefix tailTrace_6209203
  have hstable : (prefixWord ++ tailWord_6209203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209203).length < 2 ^ (prefixWord ++ tailWord_6209203).sum := by decide
  have hdescent : baseEnd_6209203 < baseStart_6209203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209210 : List Nat := [3, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4]
def baseStart_6209210 : Nat := 118140960795 + 6209210 * 2 ^ 59
def prefixEnd_6209210 : Nat := 4983230072969 + 3 ^ 40 * 6209210 * 2
def baseEnd_6209210 : Nat := 3188309214703756671019369

theorem tailTrace_6209210 : CollatzResearch.WordTrace tailWord_6209210 prefixEnd_6209210 3188309214703756671019369 := by
  unfold tailWord_6209210
  simp only [CollatzResearch.WordTrace]
  refine ⟨56617123458775023371620271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150978995890066728990987389 56617123458775023371620271)
  ·
    refine ⟨84925685188162535057430407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56617123458775023371620271 84925685188162535057430407)
    ·
      refine ⟨127388527782243802586145611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84925685188162535057430407 127388527782243802586145611)
      ·
        refine ⟨191082791673365703879218417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127388527782243802586145611 191082791673365703879218417)
        ·
          refine ⟨143312093755024277909413813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191082791673365703879218417 143312093755024277909413813)
          ·
            refine ⟨13435508789533526054007545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143312093755024277909413813 13435508789533526054007545)
            ·
              refine ⟨10076631592150144540505659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13435508789533526054007545 10076631592150144540505659)
              ·
                refine ⟨15114947388225216810758489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10076631592150144540505659 15114947388225216810758489)
                ·
                  refine ⟨11336210541168912608068867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15114947388225216810758489 11336210541168912608068867)
                  ·
                    refine ⟨17004315811753368912103301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11336210541168912608068867 17004315811753368912103301)
                    ·
                      refine ⟨3188309214703756671019369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17004315811753368912103301 3188309214703756671019369)
                      ·
                        rfl

theorem cell23_6209210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_6209210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209210 prefixEnd_6209210 := by exact prefixLift 6209210
  have htrace : WordTrace (prefixWord ++ tailWord_6209210) baseStart_6209210 baseEnd_6209210 := by
    simpa [prefixWord, tailWord_6209210, baseEnd_6209210] using wordTrace_append hprefix tailTrace_6209210
  have hstable : (prefixWord ++ tailWord_6209210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209210).length < 2 ^ (prefixWord ++ tailWord_6209210).sum := by decide
  have hdescent : baseEnd_6209210 < baseStart_6209210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209230 : List Nat := [4, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3]
def baseStart_6209230 : Nat := 118140960795 + 6209230 * 2 ^ 59
def prefixEnd_6209230 : Nat := 4983230072969 + 3 ^ 40 * 6209230 * 2
def baseEnd_6209230 : Nat := 3188319484316846592769277

theorem tailTrace_6209230 : CollatzResearch.WordTrace tailWord_6209230 prefixEnd_6209230 3188319484316846592769277 := by
  unfold tailWord_6209230
  simp only [CollatzResearch.WordTrace]
  refine ⟨28308652911878454612776143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150979482196685091268139429 28308652911878454612776143)
  ·
    refine ⟨42462979367817681919164215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28308652911878454612776143 42462979367817681919164215)
    ·
      refine ⟨63694469051726522878746323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42462979367817681919164215 63694469051726522878746323)
      ·
        refine ⟨95541703577589784318119485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63694469051726522878746323 95541703577589784318119485)
        ·
          refine ⟨35828138841596169119294807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95541703577589784318119485 35828138841596169119294807)
          ·
            refine ⟨53742208262394253678942211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35828138841596169119294807 53742208262394253678942211)
            ·
              refine ⟨80613312393591380518413317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53742208262394253678942211 80613312393591380518413317)
              ·
                refine ⟨15114996073798383847202497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 80613312393591380518413317 15114996073798383847202497)
                ·
                  refine ⟨11336247055348787885401873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15114996073798383847202497 11336247055348787885401873)
                  ·
                    refine ⟨8502185291511590914051405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11336247055348787885401873 8502185291511590914051405)
                    ·
                      refine ⟨3188319484316846592769277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8502185291511590914051405 3188319484316846592769277)
                      ·
                        rfl

theorem cell23_6209230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_6209230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209230 prefixEnd_6209230 := by exact prefixLift 6209230
  have htrace : WordTrace (prefixWord ++ tailWord_6209230) baseStart_6209230 baseEnd_6209230 := by
    simpa [prefixWord, tailWord_6209230, baseEnd_6209230] using wordTrace_append hprefix tailTrace_6209230
  have hstable : (prefixWord ++ tailWord_6209230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209230).length < 2 ^ (prefixWord ++ tailWord_6209230).sum := by decide
  have hdescent : baseEnd_6209230 < baseStart_6209230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209233 : List Nat := [1, 2, 2, 1, 2, 4, 1, 4, 6]
def baseStart_6209233 : Nat := 118140960795 + 6209233 * 2 ^ 59
def prefixEnd_6209233 : Nat := 4983230072969 + 3 ^ 40 * 6209233 * 2
def baseEnd_6209233 : Nat := 354257891639867786781307

theorem tailTrace_6209233 : CollatzResearch.WordTrace tailWord_6209233 prefixEnd_6209233 354257891639867786781307 := by
  unfold tailWord_6209233
  simp only [CollatzResearch.WordTrace]
  refine ⟨226469332714016768414568353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150979555142677845609712235 226469332714016768414568353)
  ·
    refine ⟨169851999535512576310926265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226469332714016768414568353 169851999535512576310926265)
    ·
      refine ⟨127388999651634432233194699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169851999535512576310926265 127388999651634432233194699)
      ·
        refine ⟨191083499477451648349792049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127388999651634432233194699 191083499477451648349792049)
        ·
          refine ⟨143312624608088736262344037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191083499477451648349792049 143312624608088736262344037)
          ·
            refine ⟨26871117114016638049189507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143312624608088736262344037 26871117114016638049189507)
            ·
              refine ⟨40306675671024957073784261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26871117114016638049189507 40306675671024957073784261)
              ·
                refine ⟨7557501688317179451334549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40306675671024957073784261 7557501688317179451334549)
                ·
                  refine ⟨354257891639867786781307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7557501688317179451334549 354257891639867786781307)
                  ·
                    rfl

theorem cell23_6209233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 6].length) (baseStart_6209233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209233 prefixEnd_6209233 := by exact prefixLift 6209233
  have htrace : WordTrace (prefixWord ++ tailWord_6209233) baseStart_6209233 baseEnd_6209233 := by
    simpa [prefixWord, tailWord_6209233, baseEnd_6209233] using wordTrace_append hprefix tailTrace_6209233
  have hstable : (prefixWord ++ tailWord_6209233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209233).length < 2 ^ (prefixWord ++ tailWord_6209233).sum := by decide
  have hdescent : baseEnd_6209233 < baseStart_6209233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209244 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_6209244 : Nat := 118140960795 + 6209244 * 2 ^ 59
def prefixEnd_6209244 : Nat := 4983230072969 + 3 ^ 40 * 6209244 * 2
def baseEnd_6209244 : Nat := 3188326673046009537994213

theorem tailTrace_6209244 : CollatzResearch.WordTrace tailWord_6209244 prefixEnd_6209244 3188326673046009537994213 := by
  unfold tailWord_6209244
  simp only [CollatzResearch.WordTrace]
  refine ⟨113234866958488458646609393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150979822611317944862145857 113234866958488458646609393)
  ·
    refine ⟨84926150218866343984957045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113234866958488458646609393 84926150218866343984957045)
    ·
      refine ⟨7961826583018719748589723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84926150218866343984957045 7961826583018719748589723)
      ·
        refine ⟨11942739874528079622884585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7961826583018719748589723 11942739874528079622884585)
        ·
          refine ⟨8957054905896059717163439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11942739874528079622884585 8957054905896059717163439)
          ·
            refine ⟨13435582358844089575745159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8957054905896059717163439 13435582358844089575745159)
            ·
              refine ⟨20153373538266134363617739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13435582358844089575745159 20153373538266134363617739)
              ·
                refine ⟨30230060307399201545426609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20153373538266134363617739 30230060307399201545426609)
                ·
                  refine ⟨22672545230549401159069957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30230060307399201545426609 22672545230549401159069957)
                  ·
                    refine ⟨4251102230728012717325617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22672545230549401159069957 4251102230728012717325617)
                    ·
                      refine ⟨3188326673046009537994213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4251102230728012717325617 3188326673046009537994213)
                      ·
                        rfl

theorem cell23_6209244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_6209244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209244 prefixEnd_6209244 := by exact prefixLift 6209244
  have htrace : WordTrace (prefixWord ++ tailWord_6209244) baseStart_6209244 baseEnd_6209244 := by
    simpa [prefixWord, tailWord_6209244, baseEnd_6209244] using wordTrace_append hprefix tailTrace_6209244
  have hstable : (prefixWord ++ tailWord_6209244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209244).length < 2 ^ (prefixWord ++ tailWord_6209244).sum := by decide
  have hdescent : baseEnd_6209244 < baseStart_6209244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209260 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 3]
def baseStart_6209260 : Nat := 118140960795 + 6209260 * 2 ^ 59
def prefixEnd_6209260 : Nat := 4983230072969 + 3 ^ 40 * 6209260 * 2
def baseEnd_6209260 : Nat := 3188334888736481475394139

theorem tailTrace_6209260 : CollatzResearch.WordTrace tailWord_6209260 prefixEnd_6209260 3188334888736481475394139 := by
  unfold tailWord_6209260
  simp only [CollatzResearch.WordTrace]
  refine ⟨113235158742459476012900617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150980211656612634683867489 113235158742459476012900617)
  ·
    refine ⟨84926369056844607009675463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113235158742459476012900617 84926369056844607009675463)
    ·
      refine ⟨127389553585266910514513195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84926369056844607009675463 127389553585266910514513195)
      ·
        refine ⟨191084330377900365771769793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127389553585266910514513195 191084330377900365771769793)
        ·
          refine ⟨143313247783425274328827345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191084330377900365771769793 143313247783425274328827345)
          ·
            refine ⟨107484935837568955746620509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143313247783425274328827345 107484935837568955746620509)
            ·
              refine ⟨40306850939088358404982691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107484935837568955746620509 40306850939088358404982691)
              ·
                refine ⟨60460276408632537607474037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40306850939088358404982691 60460276408632537607474037)
                ·
                  refine ⟨5668150913309300400700691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60460276408632537607474037 5668150913309300400700691)
                  ·
                    refine ⟨8502226369963950601051037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5668150913309300400700691 8502226369963950601051037)
                    ·
                      refine ⟨3188334888736481475394139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8502226369963950601051037 3188334888736481475394139)
                      ·
                        rfl

theorem cell23_6209260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 3].length) (baseStart_6209260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209260 prefixEnd_6209260 := by exact prefixLift 6209260
  have htrace : WordTrace (prefixWord ++ tailWord_6209260) baseStart_6209260 baseEnd_6209260 := by
    simpa [prefixWord, tailWord_6209260, baseEnd_6209260] using wordTrace_append hprefix tailTrace_6209260
  have hstable : (prefixWord ++ tailWord_6209260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209260).length < 2 ^ (prefixWord ++ tailWord_6209260).sum := by decide
  have hdescent : baseEnd_6209260 < baseStart_6209260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209263 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 3, 5]
def baseStart_6209263 : Nat := 118140960795 + 6209263 * 2 ^ 59
def prefixEnd_6209263 : Nat := 4983230072969 + 3 ^ 40 * 6209263 * 2
def baseEnd_6209263 : Nat := 1062778809726148321218875

theorem tailTrace_6209263 : CollatzResearch.WordTrace tailWord_6209263 prefixEnd_6209263 1062778809726148321218875 := by
  unfold tailWord_6209263
  simp only [CollatzResearch.WordTrace]
  refine ⟨226470426903908083538160443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150980284602605389025440295 226470426903908083538160443)
  ·
    refine ⟨339705640355862125307240665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226470426903908083538160443 339705640355862125307240665)
    ·
      refine ⟨254779230266896593980430499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339705640355862125307240665 254779230266896593980430499)
      ·
        refine ⟨382168845400344890970645749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254779230266896593980430499 382168845400344890970645749)
        ·
          refine ⟨35828329256282333528498039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 382168845400344890970645749 35828329256282333528498039)
          ·
            refine ⟨53742493884423500292747059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35828329256282333528498039 53742493884423500292747059)
            ·
              refine ⟨80613740826635250439120589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53742493884423500292747059 80613740826635250439120589)
              ·
                refine ⟨30230152809988218914670221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80613740826635250439120589 30230152809988218914670221)
                ·
                  refine ⟨11336307303745582093001333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30230152809988218914670221 11336307303745582093001333)
                  ·
                    refine ⟨1062778809726148321218875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11336307303745582093001333 1062778809726148321218875)
                    ·
                      rfl

theorem cell23_6209263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 5].length) (baseStart_6209263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209263 prefixEnd_6209263 := by exact prefixLift 6209263
  have htrace : WordTrace (prefixWord ++ tailWord_6209263) baseStart_6209263 baseEnd_6209263 := by
    simpa [prefixWord, tailWord_6209263, baseEnd_6209263] using wordTrace_append hprefix tailTrace_6209263
  have hstable : (prefixWord ++ tailWord_6209263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209263).length < 2 ^ (prefixWord ++ tailWord_6209263).sum := by decide
  have hdescent : baseEnd_6209263 < baseStart_6209263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209294 : List Nat := [4, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3]
def baseStart_6209294 : Nat := 118140960795 + 6209294 * 2 ^ 59
def prefixEnd_6209294 : Nat := 4983230072969 + 3 ^ 40 * 6209294 * 2
def baseEnd_6209294 : Nat := 3188352347078734342368983

theorem tailTrace_6209294 : CollatzResearch.WordTrace tailWord_6209294 prefixEnd_6209294 3188352347078734342368983 := by
  unfold tailWord_6209294
  simp only [CollatzResearch.WordTrace]
  refine ⟨28308944695849471979067367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150981038377863850555025957 28308944695849471979067367)
  ·
    refine ⟨42463417043774207968601051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28308944695849471979067367 42463417043774207968601051)
    ·
      refine ⟨63695125565661311952901577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42463417043774207968601051 63695125565661311952901577)
      ·
        refine ⟨47771344174245983964676183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63695125565661311952901577 47771344174245983964676183)
        ·
          refine ⟨71657016261368975947014275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47771344174245983964676183 71657016261368975947014275)
          ·
            refine ⟨107485524392053463920521413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71657016261368975947014275 107485524392053463920521413)
            ·
              refine ⟨20153535823510024485097765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107485524392053463920521413 20153535823510024485097765)
              ·
                refine ⟨3778787966908129590955831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20153535823510024485097765 3778787966908129590955831)
                ·
                  refine ⟨5668181950362194386433747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3778787966908129590955831 5668181950362194386433747)
                  ·
                    refine ⟨8502272925543291579650621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5668181950362194386433747 8502272925543291579650621)
                    ·
                      refine ⟨3188352347078734342368983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8502272925543291579650621 3188352347078734342368983)
                      ·
                        rfl

theorem cell23_6209294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_6209294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209294 prefixEnd_6209294 := by exact prefixLift 6209294
  have htrace : WordTrace (prefixWord ++ tailWord_6209294) baseStart_6209294 baseEnd_6209294 := by
    simpa [prefixWord, tailWord_6209294, baseEnd_6209294] using wordTrace_append hprefix tailTrace_6209294
  have hstable : (prefixWord ++ tailWord_6209294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209294).length < 2 ^ (prefixWord ++ tailWord_6209294).sum := by decide
  have hdescent : baseEnd_6209294 < baseStart_6209294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209317 : List Nat := [1, 3, 1, 2, 3, 3, 2, 2, 1, 1, 4]
def baseStart_6209317 : Nat := 118140960795 + 6209317 * 2 ^ 59
def prefixEnd_6209317 : Nat := 4983230072969 + 3 ^ 40 * 6209317 * 2
def baseEnd_6209317 : Nat := 3188364157133787752381377

theorem tailTrace_6209317 : CollatzResearch.WordTrace tailWord_6209317 prefixEnd_6209317 3188364157133787752381377 := by
  unfold tailWord_6209317
  simp only [CollatzResearch.WordTrace]
  refine ⟨226472396445712450760626205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150981597630474967173750803 226472396445712450760626205)
  ·
    refine ⟨84927148667142169035234827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226472396445712450760626205 84927148667142169035234827)
    ·
      refine ⟨127390723000713253552852241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84927148667142169035234827 127390723000713253552852241)
      ·
        refine ⟨95543042250534940164639181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127390723000713253552852241 95543042250534940164639181)
        ·
          refine ⟨35828640843950602561739693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95543042250534940164639181 35828640843950602561739693)
          ·
            refine ⟨13435740316481475960652385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35828640843950602561739693 13435740316481475960652385)
            ·
              refine ⟨10076805237361106970489289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13435740316481475960652385 10076805237361106970489289)
              ·
                refine ⟨7557603928020830227866967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10076805237361106970489289 7557603928020830227866967)
                ·
                  refine ⟨11336405892031245341800451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7557603928020830227866967 11336405892031245341800451)
                  ·
                    refine ⟨17004608838046868012700677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11336405892031245341800451 17004608838046868012700677)
                    ·
                      refine ⟨3188364157133787752381377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17004608838046868012700677 3188364157133787752381377)
                      ·
                        rfl

theorem cell23_6209317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_6209317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209317 prefixEnd_6209317 := by exact prefixLift 6209317
  have htrace : WordTrace (prefixWord ++ tailWord_6209317) baseStart_6209317 baseEnd_6209317 := by
    simpa [prefixWord, tailWord_6209317, baseEnd_6209317] using wordTrace_append hprefix tailTrace_6209317
  have hstable : (prefixWord ++ tailWord_6209317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209317).length < 2 ^ (prefixWord ++ tailWord_6209317).sum := by decide
  have hdescent : baseEnd_6209317 < baseStart_6209317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209334 : List Nat := [5, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_6209334 : Nat := 118140960795 + 6209334 * 2 ^ 59
def prefixEnd_6209334 : Nat := 4983230072969 + 3 ^ 40 * 6209334 * 2
def baseEnd_6209334 : Nat := 3188372886304914185868799

theorem tailTrace_6209334 : CollatzResearch.WordTrace tailWord_6209334 prefixEnd_6209334 3188372886304914185868799 := by
  unfold tailWord_6209334
  simp only [CollatzResearch.WordTrace]
  refine ⟨14154563530415678916499691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 150982010991100575109330037 14154563530415678916499691)
  ·
    refine ⟨21231845295623518374749537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14154563530415678916499691 21231845295623518374749537)
    ·
      refine ⟨15923883971717638781062153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21231845295623518374749537 15923883971717638781062153)
      ·
        refine ⟨11942912978788229085796615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15923883971717638781062153 11942912978788229085796615)
        ·
          refine ⟨17914369468182343628694923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11942912978788229085796615 17914369468182343628694923)
          ·
            refine ⟨26871554202273515443042385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17914369468182343628694923 26871554202273515443042385)
            ·
              refine ⟨20153665651705136582281789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26871554202273515443042385 20153665651705136582281789)
              ·
                refine ⟨7557624619389426218355671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20153665651705136582281789 7557624619389426218355671)
                ·
                  refine ⟨11336436929084139327533507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7557624619389426218355671 11336436929084139327533507)
                  ·
                    refine ⟨17004655393626208991300261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11336436929084139327533507 17004655393626208991300261)
                    ·
                      refine ⟨3188372886304914185868799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17004655393626208991300261 3188372886304914185868799)
                      ·
                        rfl

theorem cell23_6209334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_6209334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209334 prefixEnd_6209334 := by exact prefixLift 6209334
  have htrace : WordTrace (prefixWord ++ tailWord_6209334) baseStart_6209334 baseEnd_6209334 := by
    simpa [prefixWord, tailWord_6209334, baseEnd_6209334] using wordTrace_append hprefix tailTrace_6209334
  have hstable : (prefixWord ++ tailWord_6209334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209334).length < 2 ^ (prefixWord ++ tailWord_6209334).sum := by decide
  have hdescent : baseEnd_6209334 < baseStart_6209334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209353 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 2, 7]
def baseStart_6209353 : Nat := 118140960795 + 6209353 * 2 ^ 59
def prefixEnd_6209353 : Nat := 4983230072969 + 3 ^ 40 * 6209353 * 2
def baseEnd_6209353 : Nat := 1062794214145783203843737

theorem tailTrace_6209353 : CollatzResearch.WordTrace tailWord_6209353 prefixEnd_6209353 1062794214145783203843737 := by
  unfold tailWord_6209353
  simp only [CollatzResearch.WordTrace]
  refine ⟨226473709473582028908936713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150982472982388019272624475 226473709473582028908936713)
  ·
    refine ⟨169855282105186521681702535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226473709473582028908936713 169855282105186521681702535)
    ·
      refine ⟨254782923157779782522553803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169855282105186521681702535 254782923157779782522553803)
      ·
        refine ⟨382174384736669673783830705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254782923157779782522553803 382174384736669673783830705)
        ·
          refine ⟨286630788552502255337873029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382174384736669673783830705 286630788552502255337873029)
          ·
            refine ⟨53743272853594172875851193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 286630788552502255337873029 53743272853594172875851193)
            ·
              refine ⟨40307454640195629656888395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53743272853594172875851193 40307454640195629656888395)
              ·
                refine ⟨60461181960293444485332593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40307454640195629656888395 60461181960293444485332593)
                ·
                  refine ⟨45345886470220083363999445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60461181960293444485332593 45345886470220083363999445)
                  ·
                    refine ⟨1062794214145783203843737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45345886470220083363999445 1062794214145783203843737)
                    ·
                      rfl

theorem cell23_6209353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 7].length) (baseStart_6209353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209353 prefixEnd_6209353 := by exact prefixLift 6209353
  have htrace : WordTrace (prefixWord ++ tailWord_6209353) baseStart_6209353 baseEnd_6209353 := by
    simpa [prefixWord, tailWord_6209353, baseEnd_6209353] using wordTrace_append hprefix tailTrace_6209353
  have hstable : (prefixWord ++ tailWord_6209353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209353).length < 2 ^ (prefixWord ++ tailWord_6209353).sum := by decide
  have hdescent : baseEnd_6209353 < baseStart_6209353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209357 : List Nat := [1, 6, 1, 2, 1, 2, 2, 8]
def baseStart_6209357 : Nat := 118140960795 + 6209357 * 2 ^ 59
def prefixEnd_6209357 : Nat := 4983230072969 + 3 ^ 40 * 6209357 * 2
def baseEnd_6209357 : Nat := 118088322087406207254859

theorem tailTrace_6209357 : CollatzResearch.WordTrace tailWord_6209357 prefixEnd_6209357 118088322087406207254859 := by
  unfold tailWord_6209357
  simp only [CollatzResearch.WordTrace]
  refine ⟨226473855365567537592082325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150982570243711691728054883 226473855365567537592082325)
  ·
    refine ⟨10615961970260978324628859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 226473855365567537592082325 10615961970260978324628859)
    ·
      refine ⟨15923942955391467486943289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10615961970260978324628859 15923942955391467486943289)
      ·
        refine ⟨11942957216543600615207467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15923942955391467486943289 11942957216543600615207467)
        ·
          refine ⟨17914435824815400922811201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11942957216543600615207467 17914435824815400922811201)
          ·
            refine ⟨13435826868611550692108401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17914435824815400922811201 13435826868611550692108401)
            ·
              refine ⟨10076870151458663019081301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13435826868611550692108401 10076870151458663019081301)
              ·
                refine ⟨118088322087406207254859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10076870151458663019081301 118088322087406207254859)
                ·
                  rfl

theorem cell23_6209357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 8].length) (baseStart_6209357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209357 prefixEnd_6209357 := by exact prefixLift 6209357
  have htrace : WordTrace (prefixWord ++ tailWord_6209357) baseStart_6209357 baseEnd_6209357 := by
    simpa [prefixWord, tailWord_6209357, baseEnd_6209357] using wordTrace_append hprefix tailTrace_6209357
  have hstable : (prefixWord ++ tailWord_6209357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209357).length < 2 ^ (prefixWord ++ tailWord_6209357).sum := by decide
  have hdescent : baseEnd_6209357 < baseStart_6209357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209360 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 2, 7, 2]
def baseStart_6209360 : Nat := 118140960795 + 6209360 * 2 ^ 59
def prefixEnd_6209360 : Nat := 4983230072969 + 3 ^ 40 * 6209360 * 2
def baseEnd_6209360 : Nat := 3188386236801931084143679

theorem tailTrace_6209360 : CollatzResearch.WordTrace tailWord_6209360 prefixEnd_6209360 3188386236801931084143679 := by
  unfold tailWord_6209360
  simp only [CollatzResearch.WordTrace]
  refine ⟨113236982392278334552220767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150982643189704446069627689 113236982392278334552220767)
  ·
    refine ⟨169855473588417501828331151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113236982392278334552220767 169855473588417501828331151)
    ·
      refine ⟨254783210382626252742496727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169855473588417501828331151 254783210382626252742496727)
      ·
        refine ⟨382174815573939379113745091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254783210382626252742496727 382174815573939379113745091)
        ·
          refine ⟨573262223360909068670617637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382174815573939379113745091 573262223360909068670617637)
          ·
            refine ⟨107486666880170450375740807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 573262223360909068670617637 107486666880170450375740807)
            ·
              refine ⟨161230000320255675563611211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107486666880170450375740807 161230000320255675563611211)
              ·
                refine ⟨241845000480383513345416817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161230000320255675563611211 241845000480383513345416817)
                ·
                  refine ⟨181383750360287635009062613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241845000480383513345416817 181383750360287635009062613)
                  ·
                    refine ⟨4251181649069241445524905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 181383750360287635009062613 4251181649069241445524905)
                    ·
                      refine ⟨3188386236801931084143679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4251181649069241445524905 3188386236801931084143679)
                      ·
                        rfl

theorem cell23_6209360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 2, 7, 2].length) (baseStart_6209360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209360 prefixEnd_6209360 := by exact prefixLift 6209360
  have htrace : WordTrace (prefixWord ++ tailWord_6209360) baseStart_6209360 baseEnd_6209360 := by
    simpa [prefixWord, tailWord_6209360, baseEnd_6209360] using wordTrace_append hprefix tailTrace_6209360
  have hstable : (prefixWord ++ tailWord_6209360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209360).length < 2 ^ (prefixWord ++ tailWord_6209360).sum := by decide
  have hdescent : baseEnd_6209360 < baseStart_6209360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209377 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 3, 3, 2]
def baseStart_6209377 : Nat := 118140960795 + 6209377 * 2 ^ 59
def prefixEnd_6209377 : Nat := 4983230072969 + 3 ^ 40 * 6209377 * 2
def baseEnd_6209377 : Nat := 3188394965973057517631101

theorem tailTrace_6209377 : CollatzResearch.WordTrace tailWord_6209377 prefixEnd_6209377 3188394965973057517631101 := by
  unfold tailWord_6209377
  simp only [CollatzResearch.WordTrace]
  refine ⟨226474584825495081007810385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150983056550330054005206923 226474584825495081007810385)
  ·
    refine ⟨169855938619121310755857789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226474584825495081007810385 169855938619121310755857789)
    ·
      refine ⟨63695976982170491533446671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169855938619121310755857789 63695976982170491533446671)
      ·
        refine ⟨95543965473255737300170007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63695976982170491533446671 95543965473255737300170007)
        ·
          refine ⟨143315948209883605950255011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95543965473255737300170007 143315948209883605950255011)
          ·
            refine ⟨214973922314825408925382517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143315948209883605950255011 214973922314825408925382517)
            ·
              refine ⟨20153805217014882086754611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 214973922314825408925382517 20153805217014882086754611)
              ·
                refine ⟨30230707825522323130131917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20153805217014882086754611 30230707825522323130131917)
                ·
                  refine ⟨11336515434570871173799469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30230707825522323130131917 11336515434570871173799469)
                  ·
                    refine ⟨4251193287964076690174801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11336515434570871173799469 4251193287964076690174801)
                    ·
                      refine ⟨3188394965973057517631101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4251193287964076690174801 3188394965973057517631101)
                      ·
                        rfl

theorem cell23_6209377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_6209377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209377 prefixEnd_6209377 := by exact prefixLift 6209377
  have htrace : WordTrace (prefixWord ++ tailWord_6209377) baseStart_6209377 baseEnd_6209377 := by
    simpa [prefixWord, tailWord_6209377, baseEnd_6209377] using wordTrace_append hprefix tailTrace_6209377
  have hstable : (prefixWord ++ tailWord_6209377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209377).length < 2 ^ (prefixWord ++ tailWord_6209377).sum := by decide
  have hdescent : baseEnd_6209377 < baseStart_6209377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209403 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 6]
def baseStart_6209403 : Nat := 118140960795 + 6209403 * 2 ^ 59
def prefixEnd_6209403 : Nat := 4983230072969 + 3 ^ 40 * 6209403 * 2
def baseEnd_6209403 : Nat := 3188408316470074415905981

theorem tailTrace_6209403 : CollatzResearch.WordTrace tailWord_6209403 prefixEnd_6209403 3188408316470074415905981 := by
  unfold tailWord_6209403
  simp only [CollatzResearch.WordTrace]
  refine ⟨226475533123400887448256863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150983688748933924965504575 226475533123400887448256863)
  ·
    refine ⟨339713299685101331172385295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226475533123400887448256863 339713299685101331172385295)
    ·
      refine ⟨509569949527651996758577943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339713299685101331172385295 509569949527651996758577943)
      ·
        refine ⟨764354924291477995137866915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509569949527651996758577943 764354924291477995137866915)
        ·
          refine ⟨1146532386437216992706800373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 764354924291477995137866915 1146532386437216992706800373)
          ·
            refine ⟨107487411228489093066262535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1146532386437216992706800373 107487411228489093066262535)
            ·
              refine ⟨161231116842733639599393803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107487411228489093066262535 161231116842733639599393803)
              ·
                refine ⟨241846675264100459399090705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161231116842733639599393803 241846675264100459399090705)
                ·
                  refine ⟨181385006448075344549318029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241846675264100459399090705 181385006448075344549318029)
                  ·
                    refine ⟨68019377418028254205994261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 181385006448075344549318029 68019377418028254205994261)
                    ·
                      refine ⟨3188408316470074415905981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68019377418028254205994261 3188408316470074415905981)
                      ·
                        rfl

theorem cell23_6209403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 6].length) (baseStart_6209403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209403 prefixEnd_6209403 := by exact prefixLift 6209403
  have htrace : WordTrace (prefixWord ++ tailWord_6209403) baseStart_6209403 baseEnd_6209403 := by
    simpa [prefixWord, tailWord_6209403, baseEnd_6209403] using wordTrace_append hprefix tailTrace_6209403
  have hstable : (prefixWord ++ tailWord_6209403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209403).length < 2 ^ (prefixWord ++ tailWord_6209403).sum := by decide
  have hdescent : baseEnd_6209403 < baseStart_6209403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209423 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 7]
def baseStart_6209423 : Nat := 118140960795 + 6209423 * 2 ^ 59
def prefixEnd_6209423 : Nat := 4983230072969 + 3 ^ 40 * 6209423 * 2
def baseEnd_6209423 : Nat := 3188418586083164337655889

theorem tailTrace_6209423 : CollatzResearch.WordTrace tailWord_6209423 prefixEnd_6209423 3188418586083164337655889 := by
  unfold tailWord_6209423
  simp only [CollatzResearch.WordTrace]
  refine ⟨226476262583328430863984923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150984175055552287242656615 226476262583328430863984923)
  ·
    refine ⟨339714393874992646295977385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226476262583328430863984923 339714393874992646295977385)
    ·
      refine ⟨254785795406244484721983039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339714393874992646295977385 254785795406244484721983039)
      ·
        refine ⟨382178693109366727082974559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254785795406244484721983039 382178693109366727082974559)
        ·
          refine ⟨573268039664050090624461839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382178693109366727082974559 573268039664050090624461839)
          ·
            refine ⟨859902059496075135936692759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573268039664050090624461839 859902059496075135936692759)
            ·
              refine ⟨1289853089244112703905039139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859902059496075135936692759 1289853089244112703905039139)
              ·
                refine ⟨1934779633866169055857558709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1289853089244112703905039139 1934779633866169055857558709)
                ·
                  refine ⟨181385590674953348986646129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1934779633866169055857558709 181385590674953348986646129)
                  ·
                    refine ⟨136039193006215011739984597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 181385590674953348986646129 136039193006215011739984597)
                    ·
                      refine ⟨3188418586083164337655889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136039193006215011739984597 3188418586083164337655889)
                      ·
                        rfl

theorem cell23_6209423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_6209423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209423 prefixEnd_6209423 := by exact prefixLift 6209423
  have htrace : WordTrace (prefixWord ++ tailWord_6209423) baseStart_6209423 baseEnd_6209423 := by
    simpa [prefixWord, tailWord_6209423, baseEnd_6209423] using wordTrace_append hprefix tailTrace_6209423
  have hstable : (prefixWord ++ tailWord_6209423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209423).length < 2 ^ (prefixWord ++ tailWord_6209423).sum := by decide
  have hdescent : baseEnd_6209423 < baseStart_6209423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209440 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 3]
def baseStart_6209440 : Nat := 118140960795 + 6209440 * 2 ^ 59
def prefixEnd_6209440 : Nat := 4983230072969 + 3 ^ 40 * 6209440 * 2
def baseEnd_6209440 : Nat := 3188427315254290771143311

theorem tailTrace_6209440 : CollatzResearch.WordTrace tailWord_6209440 prefixEnd_6209440 3188427315254290771143311 := by
  unfold tailWord_6209440
  simp only [CollatzResearch.WordTrace]
  refine ⟨113238441312133421383676887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150984588416177895178235849 113238441312133421383676887)
  ·
    refine ⟨169857661968200132075515331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113238441312133421383676887 169857661968200132075515331)
    ·
      refine ⟨254786492952300198113272997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169857661968200132075515331 254786492952300198113272997)
      ·
        refine ⟨47772467428556287146238687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254786492952300198113272997 47772467428556287146238687)
        ·
          refine ⟨71658701142834430719358031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47772467428556287146238687 71658701142834430719358031)
          ·
            refine ⟨107488051714251646079037047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71658701142834430719358031 107488051714251646079037047)
            ·
              refine ⟨161232077571377469118555571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107488051714251646079037047 161232077571377469118555571)
              ·
                refine ⟨241848116357066203677833357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 161232077571377469118555571 241848116357066203677833357)
                ·
                  refine ⟨90693043633899826379187509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241848116357066203677833357 90693043633899826379187509)
                  ·
                    refine ⟨8502472840678108723048829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 90693043633899826379187509 8502472840678108723048829)
                    ·
                      refine ⟨3188427315254290771143311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8502472840678108723048829 3188427315254290771143311)
                      ·
                        rfl

theorem cell23_6209440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_6209440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209440 prefixEnd_6209440 := by exact prefixLift 6209440
  have htrace : WordTrace (prefixWord ++ tailWord_6209440) baseStart_6209440 baseEnd_6209440 := by
    simpa [prefixWord, tailWord_6209440, baseEnd_6209440] using wordTrace_append hprefix tailTrace_6209440
  have hstable : (prefixWord ++ tailWord_6209440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209440).length < 2 ^ (prefixWord ++ tailWord_6209440).sum := by decide
  have hdescent : baseEnd_6209440 < baseStart_6209440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209457 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 2, 3, 3]
def baseStart_6209457 : Nat := 118140960795 + 6209457 * 2 ^ 59
def prefixEnd_6209457 : Nat := 4983230072969 + 3 ^ 40 * 6209457 * 2
def baseEnd_6209457 : Nat := 3188436044425417204630733

theorem tailTrace_6209457 : CollatzResearch.WordTrace tailWord_6209457 prefixEnd_6209457 3188436044425417204630733 := by
  unfold tailWord_6209457
  simp only [CollatzResearch.WordTrace]
  refine ⟨226477502665205254670722625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150985001776803503113815083 226477502665205254670722625)
  ·
    refine ⟨169858126998903941003041969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226477502665205254670722625 169858126998903941003041969)
    ·
      refine ⟨127393595249177955752281477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169858126998903941003041969 127393595249177955752281477)
      ·
        refine ⟨23886299109220866703552777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127393595249177955752281477 23886299109220866703552777)
        ·
          refine ⟨17914724331915650027664583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23886299109220866703552777 17914724331915650027664583)
          ·
            refine ⟨26872086497873475041496875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17914724331915650027664583 26872086497873475041496875)
            ·
              refine ⟨40308129746810212562245313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26872086497873475041496875 40308129746810212562245313)
              ·
                refine ⟨30231097310107659421683985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40308129746810212562245313 30231097310107659421683985)
                ·
                  refine ⟨22673322982580744566262989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30231097310107659421683985 22673322982580744566262989)
                  ·
                    refine ⟨8502496118467779212348621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22673322982580744566262989 8502496118467779212348621)
                    ·
                      refine ⟨3188436044425417204630733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8502496118467779212348621 3188436044425417204630733)
                      ·
                        rfl

theorem cell23_6209457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_6209457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209457 prefixEnd_6209457 := by exact prefixLift 6209457
  have htrace : WordTrace (prefixWord ++ tailWord_6209457) baseStart_6209457 baseEnd_6209457 := by
    simpa [prefixWord, tailWord_6209457, baseEnd_6209457] using wordTrace_append hprefix tailTrace_6209457
  have hstable : (prefixWord ++ tailWord_6209457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209457).length < 2 ^ (prefixWord ++ tailWord_6209457).sum := by decide
  have hdescent : baseEnd_6209457 < baseStart_6209457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209520 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 8]
def baseStart_6209520 : Nat := 118140960795 + 6209520 * 2 ^ 59
def prefixEnd_6209520 : Nat := 4983230072969 + 3 ^ 40 * 6209520 * 2
def baseEnd_6209520 : Nat := 354274265967405606460327

theorem tailTrace_6209520 : CollatzResearch.WordTrace tailWord_6209520 prefixEnd_6209520 354274265967405606460327 := by
  unfold tailWord_6209520
  simp only [CollatzResearch.WordTrace]
  refine ⟨113239900231988508215133007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150986533642651344286844009 113239900231988508215133007)
  ·
    refine ⟨169859850347982762322699511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113239900231988508215133007 169859850347982762322699511)
    ·
      refine ⟨254789775521974143484049267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169859850347982762322699511 254789775521974143484049267)
      ·
        refine ⟨382184663282961215226073901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254789775521974143484049267 382184663282961215226073901)
        ·
          refine ⟨143319248731110455709777713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382184663282961215226073901 143319248731110455709777713)
          ·
            refine ⟨107489436548332841782333285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143319248731110455709777713 107489436548332841782333285)
            ·
              refine ⟨20154269352812407834187491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107489436548332841782333285 20154269352812407834187491)
              ·
                refine ⟨30231404029218611751281237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20154269352812407834187491 30231404029218611751281237)
                ·
                  refine ⟨354274265967405606460327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30231404029218611751281237 354274265967405606460327)
                  ·
                    rfl

theorem cell23_6209520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 8].length) (baseStart_6209520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209520 prefixEnd_6209520 := by exact prefixLift 6209520
  have htrace : WordTrace (prefixWord ++ tailWord_6209520) baseStart_6209520 baseEnd_6209520 := by
    simpa [prefixWord, tailWord_6209520, baseEnd_6209520] using wordTrace_append hprefix tailTrace_6209520
  have hstable : (prefixWord ++ tailWord_6209520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209520).length < 2 ^ (prefixWord ++ tailWord_6209520).sum := by decide
  have hdescent : baseEnd_6209520 < baseStart_6209520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209537 : List Nat := [1, 2, 4, 1, 2, 1, 3, 3, 6]
def baseStart_6209537 : Nat := 118140960795 + 6209537 * 2 ^ 59
def prefixEnd_6209537 : Nat := 4983230072969 + 3 ^ 40 * 6209537 * 2
def baseEnd_6209537 : Nat := 354275235875308543514485

theorem tailTrace_6209537 : CollatzResearch.WordTrace tailWord_6209537 prefixEnd_6209537 354275235875308543514485 := by
  unfold tailWord_6209537
  simp only [CollatzResearch.WordTrace]
  refine ⟨226480420504915428333634865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150986947003276952222423243 226480420504915428333634865)
  ·
    refine ⟨169860315378686571250226149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226480420504915428333634865 169860315378686571250226149)
    ·
      refine ⟨31848809133503732109417403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169860315378686571250226149 31848809133503732109417403)
      ·
        refine ⟨47773213700255598164126105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31848809133503732109417403 47773213700255598164126105)
        ·
          refine ⟨35829910275191698623094579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47773213700255598164126105 35829910275191698623094579)
          ·
            refine ⟨53744865412787547934641869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35829910275191698623094579 53744865412787547934641869)
            ·
              refine ⟨20154324529795330475490701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53744865412787547934641869 20154324529795330475490701)
              ·
                refine ⟨7557871698673248928309013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20154324529795330475490701 7557871698673248928309013)
                ·
                  refine ⟨354275235875308543514485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7557871698673248928309013 354275235875308543514485)
                  ·
                    rfl

theorem cell23_6209537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 6].length) (baseStart_6209537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209537 prefixEnd_6209537 := by exact prefixLift 6209537
  have htrace : WordTrace (prefixWord ++ tailWord_6209537) baseStart_6209537 baseEnd_6209537 := by
    simpa [prefixWord, tailWord_6209537, baseEnd_6209537] using wordTrace_append hprefix tailTrace_6209537
  have hstable : (prefixWord ++ tailWord_6209537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209537).length < 2 ^ (prefixWord ++ tailWord_6209537).sum := by decide
  have hdescent : baseEnd_6209537 < baseStart_6209537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209587 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 4]
def baseStart_6209587 : Nat := 118140960795 + 6209587 * 2 ^ 59
def prefixEnd_6209587 : Nat := 4983230072969 + 3 ^ 40 * 6209587 * 2
def baseEnd_6209587 : Nat := 3188502796910501696005135

theorem tailTrace_6209587 : CollatzResearch.WordTrace tailWord_6209587 prefixEnd_6209587 3188502796910501696005135 := by
  unfold tailWord_6209587
  simp only [CollatzResearch.WordTrace]
  refine ⟨226482244154734286872955015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150988162769822857915303343 226482244154734286872955015)
  ·
    refine ⟨339723366232101430309432523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226482244154734286872955015 339723366232101430309432523)
    ·
      refine ⟨509585049348152145464148785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339723366232101430309432523 509585049348152145464148785)
      ·
        refine ⟨382188787011114109098111589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 509585049348152145464148785 382188787011114109098111589)
        ·
          refine ⟨71660397564583895455895923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 382188787011114109098111589 71660397564583895455895923)
          ·
            refine ⟨107490596346875843183843885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71660397564583895455895923 107490596346875843183843885)
            ·
              refine ⟨40308973630078441193941457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107490596346875843183843885 40308973630078441193941457)
              ·
                refine ⟨30231730222558830895456093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40308973630078441193941457 30231730222558830895456093)
                ·
                  refine ⟨11336898833459561585796035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30231730222558830895456093 11336898833459561585796035)
                  ·
                    refine ⟨17005348250189342378694053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11336898833459561585796035 17005348250189342378694053)
                    ·
                      refine ⟨3188502796910501696005135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17005348250189342378694053 3188502796910501696005135)
                      ·
                        rfl

theorem cell23_6209587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 4].length) (baseStart_6209587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209587 prefixEnd_6209587 := by exact prefixLift 6209587
  have htrace : WordTrace (prefixWord ++ tailWord_6209587) baseStart_6209587 baseEnd_6209587 := by
    simpa [prefixWord, tailWord_6209587, baseEnd_6209587] using wordTrace_append hprefix tailTrace_6209587
  have hstable : (prefixWord ++ tailWord_6209587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209587).length < 2 ^ (prefixWord ++ tailWord_6209587).sum := by decide
  have hdescent : baseEnd_6209587 < baseStart_6209587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209598 : List Nat := [4, 2, 1, 3, 2, 1, 1, 2, 3, 1, 3]
def baseStart_6209598 : Nat := 118140960795 + 6209598 * 2 ^ 59
def prefixEnd_6209598 : Nat := 4983230072969 + 3 ^ 40 * 6209598 * 2
def baseEnd_6209598 : Nat := 3188508445197701152967585

theorem tailTrace_6209598 : CollatzResearch.WordTrace tailWord_6209598 prefixEnd_6209598 3188508445197701152967585 := by
  unfold tailWord_6209598
  simp only [CollatzResearch.WordTrace]
  refine ⟨28310330669711804468950681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 150988430238462957167736965 28310330669711804468950681)
  ·
    refine ⟨21232748002283853351713011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28310330669711804468950681 21232748002283853351713011)
    ·
      refine ⟨31849122003425780027569517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21232748002283853351713011 31849122003425780027569517)
      ·
        refine ⟨11943420751284667510338569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31849122003425780027569517 11943420751284667510338569)
        ·
          refine ⟨8957565563463500632753927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11943420751284667510338569 8957565563463500632753927)
          ·
            refine ⟨13436348345195250949130891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8957565563463500632753927 13436348345195250949130891)
            ·
              refine ⟨20154522517792876423696337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13436348345195250949130891 20154522517792876423696337)
              ·
                refine ⟨15115891888344657317772253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20154522517792876423696337 15115891888344657317772253)
                ·
                  refine ⟨5668459458129246494164595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15115891888344657317772253 5668459458129246494164595)
                  ·
                    refine ⟨8502689187193869741246893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5668459458129246494164595 8502689187193869741246893)
                    ·
                      refine ⟨3188508445197701152967585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8502689187193869741246893 3188508445197701152967585)
                      ·
                        rfl

theorem cell23_6209598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_6209598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209598 prefixEnd_6209598 := by exact prefixLift 6209598
  have htrace : WordTrace (prefixWord ++ tailWord_6209598) baseStart_6209598 baseEnd_6209598 := by
    simpa [prefixWord, tailWord_6209598, baseEnd_6209598] using wordTrace_append hprefix tailTrace_6209598
  have hstable : (prefixWord ++ tailWord_6209598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209598).length < 2 ^ (prefixWord ++ tailWord_6209598).sum := by decide
  have hdescent : baseEnd_6209598 < baseStart_6209598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209618 : List Nat := [3, 2, 2, 1, 4, 2, 2, 1, 1, 5]
def baseStart_6209618 : Nat := 118140960795 + 6209618 * 2 ^ 59
def prefixEnd_6209618 : Nat := 4983230072969 + 3 ^ 40 * 6209618 * 2
def baseEnd_6209618 : Nat := 1062839571603597024905831

theorem tailTrace_6209618 : CollatzResearch.WordTrace tailWord_6209618 prefixEnd_6209618 1062839571603597024905831 := by
  unfold tailWord_6209618
  simp only [CollatzResearch.WordTrace]
  refine ⟨56620843704405494791833377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 150988916545081319444889005 56620843704405494791833377)
  ·
    refine ⟨42465632778304121093875033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56620843704405494791833377 42465632778304121093875033)
    ·
      refine ⟨31849224583728090820406275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42465632778304121093875033 31849224583728090820406275)
      ·
        refine ⟨47773836875592136230609413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31849224583728090820406275 47773836875592136230609413)
        ·
          refine ⟨8957594414173525543239265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47773836875592136230609413 8957594414173525543239265)
          ·
            refine ⟨6718195810630144157429449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8957594414173525543239265 6718195810630144157429449)
            ·
              refine ⟨5038646857972608118072087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6718195810630144157429449 5038646857972608118072087)
              ·
                refine ⟨7557970286958912177108131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5038646857972608118072087 7557970286958912177108131)
                ·
                  refine ⟨11336955430438368265662197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7557970286958912177108131 11336955430438368265662197)
                  ·
                    refine ⟨1062839571603597024905831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11336955430438368265662197 1062839571603597024905831)
                    ·
                      rfl

theorem cell23_6209618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_6209618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209618 prefixEnd_6209618 := by exact prefixLift 6209618
  have htrace : WordTrace (prefixWord ++ tailWord_6209618) baseStart_6209618 baseEnd_6209618 := by
    simpa [prefixWord, tailWord_6209618, baseEnd_6209618] using wordTrace_append hprefix tailTrace_6209618
  have hstable : (prefixWord ++ tailWord_6209618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209618).length < 2 ^ (prefixWord ++ tailWord_6209618).sum := by decide
  have hdescent : baseEnd_6209618 < baseStart_6209618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209621 : List Nat := [1, 3, 2, 2, 1, 3, 4, 1, 1, 1, 4]
def baseStart_6209621 : Nat := 118140960795 + 6209621 * 2 ^ 59
def prefixEnd_6209621 : Nat := 4983230072969 + 3 ^ 40 * 6209621 * 2
def baseEnd_6209621 : Nat := 3188520255252754562979979

theorem tailTrace_6209621 : CollatzResearch.WordTrace tailWord_6209621 prefixEnd_6209621 3188520255252754562979979 := by
  unfold tailWord_6209621
  simp only [CollatzResearch.WordTrace]
  refine ⟨226483484236611110679692717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150988989491074073786461811 226483484236611110679692717)
  ·
    refine ⟨84931306588729166504884769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226483484236611110679692717 84931306588729166504884769)
    ·
      refine ⟨63698479941546874878663577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84931306588729166504884769 63698479941546874878663577)
      ·
        refine ⟨47773859956160156158997683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63698479941546874878663577 47773859956160156158997683)
        ·
          refine ⟨71660789934240234238496525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47773859956160156158997683 71660789934240234238496525)
          ·
            refine ⟨26872796225340087839436197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71660789934240234238496525 26872796225340087839436197)
            ·
              refine ⟨5038649292251266469894287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26872796225340087839436197 5038649292251266469894287)
              ·
                refine ⟨7557973938376899704841431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5038649292251266469894287 7557973938376899704841431)
                ·
                  refine ⟨11336960907565349557262147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7557973938376899704841431 11336960907565349557262147)
                  ·
                    refine ⟨17005441361348024335893221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11336960907565349557262147 17005441361348024335893221)
                    ·
                      refine ⟨3188520255252754562979979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17005441361348024335893221 3188520255252754562979979)
                      ·
                        rfl

theorem cell23_6209621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_6209621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209621 prefixEnd_6209621 := by exact prefixLift 6209621
  have htrace : WordTrace (prefixWord ++ tailWord_6209621) baseStart_6209621 baseEnd_6209621 := by
    simpa [prefixWord, tailWord_6209621, baseEnd_6209621] using wordTrace_append hprefix tailTrace_6209621
  have hstable : (prefixWord ++ tailWord_6209621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209621).length < 2 ^ (prefixWord ++ tailWord_6209621).sum := by decide
  have hdescent : baseEnd_6209621 < baseStart_6209621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209667 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 5]
def baseStart_6209667 : Nat := 118140960795 + 6209667 * 2 ^ 59
def prefixEnd_6209667 : Nat := 4983230072969 + 3 ^ 40 * 6209667 * 2
def baseEnd_6209667 : Nat := 3188543875362861383004767

theorem tailTrace_6209667 : CollatzResearch.WordTrace tailWord_6209667 prefixEnd_6209667 3188543875362861383004767 := by
  unfold tailWord_6209667
  simp only [CollatzResearch.WordTrace]
  refine ⟨226485161994444460535867255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150990107996296307023911503 226485161994444460535867255)
  ·
    refine ⟨339727742991666690803800883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226485161994444460535867255 339727742991666690803800883)
    ·
      refine ⟨509591614487500036205701325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339727742991666690803800883 509591614487500036205701325)
      ·
        refine ⟨191096855432812513577137997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 509591614487500036205701325 191096855432812513577137997)
        ·
          refine ⟨71661320787304692591426749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191096855432812513577137997 71661320787304692591426749)
          ·
            refine ⟨26872995295239259721785031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71661320787304692591426749 26872995295239259721785031)
            ·
              refine ⟨40309492942858889582677547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26872995295239259721785031 40309492942858889582677547)
              ·
                refine ⟨60464239414288334374016321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40309492942858889582677547 60464239414288334374016321)
                ·
                  refine ⟨45348179560716250780512241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60464239414288334374016321 45348179560716250780512241)
                  ·
                    refine ⟨34011134670537188085384181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45348179560716250780512241 34011134670537188085384181)
                    ·
                      refine ⟨3188543875362861383004767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34011134670537188085384181 3188543875362861383004767)
                      ·
                        rfl

theorem cell23_6209667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_6209667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209667 prefixEnd_6209667 := by exact prefixLift 6209667
  have htrace : WordTrace (prefixWord ++ tailWord_6209667) baseStart_6209667 baseEnd_6209667 := by
    simpa [prefixWord, tailWord_6209667, baseEnd_6209667] using wordTrace_append hprefix tailTrace_6209667
  have hstable : (prefixWord ++ tailWord_6209667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209667).length < 2 ^ (prefixWord ++ tailWord_6209667).sum := by decide
  have hdescent : baseEnd_6209667 < baseStart_6209667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209672 : List Nat := [2, 1, 3, 4, 1, 3, 1, 3, 1, 2, 2]
def baseStart_6209672 : Nat := 118140960795 + 6209672 * 2 ^ 59
def prefixEnd_6209672 : Nat := 4983230072969 + 3 ^ 40 * 6209672 * 2
def baseEnd_6209672 : Nat := 3188546442766133863442245

theorem tailTrace_6209672 : CollatzResearch.WordTrace tailWord_6209672 prefixEnd_6209672 3188546442766133863442245 := by
  unfold tailWord_6209672
  simp only [CollatzResearch.WordTrace]
  refine ⟨113242672179713173194899635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150990229572950897593199513 113242672179713173194899635)
  ·
    refine ⟨169864008269569759792349453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113242672179713173194899635 169864008269569759792349453)
    ·
      refine ⟨63699003101088659922131045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169864008269569759792349453 63699003101088659922131045)
      ·
        refine ⟨11943563081454123735399571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63699003101088659922131045 11943563081454123735399571)
        ·
          refine ⟨17915344622181185603099357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11943563081454123735399571 17915344622181185603099357)
          ·
            refine ⟨6718254233317944601162259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17915344622181185603099357 6718254233317944601162259)
            ·
              refine ⟨10077381349976916901743389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6718254233317944601162259 10077381349976916901743389)
              ·
                refine ⟨3779018006241343838153771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10077381349976916901743389 3779018006241343838153771)
                ·
                  refine ⟨5668527009362015757230657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3779018006241343838153771 5668527009362015757230657)
                  ·
                    refine ⟨4251395257021511817922993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5668527009362015757230657 4251395257021511817922993)
                    ·
                      refine ⟨3188546442766133863442245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4251395257021511817922993 3188546442766133863442245)
                      ·
                        rfl

theorem cell23_6209672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_6209672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209672 prefixEnd_6209672 := by exact prefixLift 6209672
  have htrace : WordTrace (prefixWord ++ tailWord_6209672) baseStart_6209672 baseEnd_6209672 := by
    simpa [prefixWord, tailWord_6209672, baseEnd_6209672] using wordTrace_append hprefix tailTrace_6209672
  have hstable : (prefixWord ++ tailWord_6209672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209672).length < 2 ^ (prefixWord ++ tailWord_6209672).sum := by decide
  have hdescent : baseEnd_6209672 < baseStart_6209672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209707 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 4]
def baseStart_6209707 : Nat := 118140960795 + 6209707 * 2 ^ 59
def prefixEnd_6209707 : Nat := 4983230072969 + 3 ^ 40 * 6209707 * 2
def baseEnd_6209707 : Nat := 3188564414589041226504583

theorem tailTrace_6209707 : CollatzResearch.WordTrace tailWord_6209707 prefixEnd_6209707 3188564414589041226504583 := by
  unfold tailWord_6209707
  simp only [CollatzResearch.WordTrace]
  refine ⟨226486620914299547367323375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150991080609533031578215583 226486620914299547367323375)
  ·
    refine ⟨339729931371449321050985063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226486620914299547367323375 339729931371449321050985063)
    ·
      refine ⟨509594897057173981576477595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339729931371449321050985063 509594897057173981576477595)
      ·
        refine ⟨764392345585760972364716393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509594897057173981576477595 764392345585760972364716393)
        ·
          refine ⟨573294259189320729273537295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 764392345585760972364716393 573294259189320729273537295)
          ·
            refine ⟨859941388783981093910305943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 573294259189320729273537295 859941388783981093910305943)
            ·
              refine ⟨1289912083175971640865458915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 859941388783981093910305943 1289912083175971640865458915)
              ·
                refine ⟨1934868124763957461298188373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1289912083175971640865458915 1934868124763957461298188373)
                ·
                  refine ⟨22674235837077626499588145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1934868124763957461298188373 22674235837077626499588145)
                  ·
                    refine ⟨17005676877808219874691109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22674235837077626499588145 17005676877808219874691109)
                    ·
                      refine ⟨3188564414589041226504583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17005676877808219874691109 3188564414589041226504583)
                      ·
                        rfl

theorem cell23_6209707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 4].length) (baseStart_6209707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209707 prefixEnd_6209707 := by exact prefixLift 6209707
  have htrace : WordTrace (prefixWord ++ tailWord_6209707) baseStart_6209707 baseEnd_6209707 := by
    simpa [prefixWord, tailWord_6209707, baseEnd_6209707] using wordTrace_append hprefix tailTrace_6209707
  have hstable : (prefixWord ++ tailWord_6209707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209707).length < 2 ^ (prefixWord ++ tailWord_6209707).sum := by decide
  have hdescent : baseEnd_6209707 < baseStart_6209707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209801 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 2, 4, 2]
def baseStart_6209801 : Nat := 118140960795 + 6209801 * 2 ^ 59
def prefixEnd_6209801 : Nat := 4983230072969 + 3 ^ 40 * 6209801 * 2
def baseEnd_6209801 : Nat := 3188612681770563858729151

theorem tailTrace_6209801 : CollatzResearch.WordTrace tailWord_6209801 prefixEnd_6209801 3188612681770563858729151 := by
  unfold tailWord_6209801
  simp only [CollatzResearch.WordTrace]
  refine ⟨226490049375959001421245257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150993366250639334280830171 226490049375959001421245257)
  ·
    refine ⟨169867537031969251065933943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226490049375959001421245257 169867537031969251065933943)
    ·
      refine ⟨254801305547953876598900915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169867537031969251065933943 254801305547953876598900915)
      ·
        refine ⟨382201958321930814898351373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254801305547953876598900915 382201958321930814898351373)
        ·
          refine ⟨143325734370724055586881765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 382201958321930814898351373 143325734370724055586881765)
          ·
            refine ⟨26873575194510760422540331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143325734370724055586881765 26873575194510760422540331)
            ·
              refine ⟨40310362791766140633810497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26873575194510760422540331 40310362791766140633810497)
              ·
                refine ⟨30232772093824605475357873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40310362791766140633810497 30232772093824605475357873)
                ·
                  refine ⟨22674579070368454106518405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30232772093824605475357873 22674579070368454106518405)
                  ·
                    refine ⟨4251483575694085144972201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22674579070368454106518405 4251483575694085144972201)
                    ·
                      refine ⟨3188612681770563858729151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4251483575694085144972201 3188612681770563858729151)
                      ·
                        rfl

theorem cell23_6209801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 4, 2].length) (baseStart_6209801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209801 prefixEnd_6209801 := by exact prefixLift 6209801
  have htrace : WordTrace (prefixWord ++ tailWord_6209801) baseStart_6209801 baseEnd_6209801 := by
    simpa [prefixWord, tailWord_6209801, baseEnd_6209801] using wordTrace_append hprefix tailTrace_6209801
  have hstable : (prefixWord ++ tailWord_6209801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209801).length < 2 ^ (prefixWord ++ tailWord_6209801).sum := by decide
  have hdescent : baseEnd_6209801 < baseStart_6209801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209891 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 4]
def baseStart_6209891 : Nat := 118140960795 + 6209891 * 2 ^ 59
def prefixEnd_6209891 : Nat := 4983230072969 + 3 ^ 40 * 6209891 * 2
def baseEnd_6209891 : Nat := 3188658895029468506603737

theorem tailTrace_6209891 : CollatzResearch.WordTrace tailWord_6209891 prefixEnd_6209891 3188658895029468506603737 := by
  unfold tailWord_6209891
  simp only [CollatzResearch.WordTrace]
  refine ⟨226493331945632946792021527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150995554630421964528014351 226493331945632946792021527)
  ·
    refine ⟨339739997918449420188032291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226493331945632946792021527 339739997918449420188032291)
    ·
      refine ⟨509609996877674130282048437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339739997918449420188032291 509609996877674130282048437)
      ·
        refine ⟨47775937207281949713942041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 509609996877674130282048437 47775937207281949713942041)
        ·
          refine ⟨35831952905461462285456531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47775937207281949713942041 35831952905461462285456531)
          ·
            refine ⟨53747929358192193428184797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35831952905461462285456531 53747929358192193428184797)
            ·
              refine ⟨20155473509322072535569299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53747929358192193428184797 20155473509322072535569299)
              ·
                refine ⟨30233210263983108803353949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20155473509322072535569299 30233210263983108803353949)
                ·
                  refine ⟨11337453848993665801257731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30233210263983108803353949 11337453848993665801257731)
                  ·
                    refine ⟨17006180773490498701886597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11337453848993665801257731 17006180773490498701886597)
                    ·
                      refine ⟨3188658895029468506603737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17006180773490498701886597 3188658895029468506603737)
                      ·
                        rfl

theorem cell23_6209891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_6209891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209891 prefixEnd_6209891 := by exact prefixLift 6209891
  have htrace : WordTrace (prefixWord ++ tailWord_6209891) baseStart_6209891 baseEnd_6209891 := by
    simpa [prefixWord, tailWord_6209891, baseEnd_6209891] using wordTrace_append hprefix tailTrace_6209891
  have hstable : (prefixWord ++ tailWord_6209891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209891).length < 2 ^ (prefixWord ++ tailWord_6209891).sum := by decide
  have hdescent : baseEnd_6209891 < baseStart_6209891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209895 : List Nat := [1, 1, 5, 1, 3, 2, 2, 1, 2, 3, 2]
def baseStart_6209895 : Nat := 118140960795 + 6209895 * 2 ^ 59
def prefixEnd_6209895 : Nat := 4983230072969 + 3 ^ 40 * 6209895 * 2
def baseEnd_6209895 : Nat := 3188660948952086490953719

theorem tailTrace_6209895 : CollatzResearch.WordTrace tailWord_6209895 prefixEnd_6209895 3188660948952086490953719 := by
  unfold tailWord_6209895
  simp only [CollatzResearch.WordTrace]
  refine ⟨226493477837618455475167139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150995651891745636983444759 226493477837618455475167139)
  ·
    refine ⟨339740216756427683212750709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226493477837618455475167139 339740216756427683212750709)
    ·
      refine ⟨31850645320915095301195379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 339740216756427683212750709 31850645320915095301195379)
      ·
        refine ⟨47775967981372642951793069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31850645320915095301195379 47775967981372642951793069)
        ·
          refine ⟨17915987993014741106922401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47775967981372642951793069 17915987993014741106922401)
          ·
            refine ⟨13436990994761055830191801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17915987993014741106922401 13436990994761055830191801)
            ·
              refine ⟨10077743246070791872643851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13436990994761055830191801 10077743246070791872643851)
              ·
                refine ⟨15116614869106187808965777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10077743246070791872643851 15116614869106187808965777)
                ·
                  refine ⟨11337461151829640856724333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15116614869106187808965777 11337461151829640856724333)
                  ·
                    refine ⟨4251547931936115321271625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11337461151829640856724333 4251547931936115321271625)
                    ·
                      refine ⟨3188660948952086490953719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4251547931936115321271625 3188660948952086490953719)
                      ·
                        rfl

theorem cell23_6209895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_6209895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209895 prefixEnd_6209895 := by exact prefixLift 6209895
  have htrace : WordTrace (prefixWord ++ tailWord_6209895) baseStart_6209895 baseEnd_6209895 := by
    simpa [prefixWord, tailWord_6209895, baseEnd_6209895] using wordTrace_append hprefix tailTrace_6209895
  have hstable : (prefixWord ++ tailWord_6209895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209895).length < 2 ^ (prefixWord ++ tailWord_6209895).sum := by decide
  have hdescent : baseEnd_6209895 < baseStart_6209895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209901 : List Nat := [1, 5, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_6209901 : Nat := 118140960795 + 6209901 * 2 ^ 59
def prefixEnd_6209901 : Nat := 4983230072969 + 3 ^ 40 * 6209901 * 2
def baseEnd_6209901 : Nat := 1062888009945337822492897

theorem tailTrace_6209901 : CollatzResearch.WordTrace tailWord_6209901 prefixEnd_6209901 1062888009945337822492897 := by
  unfold tailWord_6209901
  simp only [CollatzResearch.WordTrace]
  refine ⟨226493696675596718499885557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150995797783731145666590371 226493696675596718499885557)
  ·
    refine ⟨21233784063337192359364271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 226493696675596718499885557 21233784063337192359364271)
    ·
      refine ⟨31850676095005788539046407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21233784063337192359364271 31850676095005788539046407)
      ·
        refine ⟨47776014142508682808569611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31850676095005788539046407 47776014142508682808569611)
        ·
          refine ⟨71664021213763024212854417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47776014142508682808569611 71664021213763024212854417)
          ·
            refine ⟨53748015910322268159640813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71664021213763024212854417 53748015910322268159640813)
            ·
              refine ⟨20155505966370850559865305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53748015910322268159640813 20155505966370850559865305)
              ·
                refine ⟨15116629474778137919898979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20155505966370850559865305 15116629474778137919898979)
                ·
                  refine ⟨22674944212167206879848469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15116629474778137919898979 22674944212167206879848469)
                  ·
                    refine ⟨1062888009945337822492897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22674944212167206879848469 1062888009945337822492897)
                    ·
                      rfl

theorem cell23_6209901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_6209901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209901 prefixEnd_6209901 := by exact prefixLift 6209901
  have htrace : WordTrace (prefixWord ++ tailWord_6209901) baseStart_6209901 baseEnd_6209901 := by
    simpa [prefixWord, tailWord_6209901, baseEnd_6209901] using wordTrace_append hprefix tailTrace_6209901
  have hstable : (prefixWord ++ tailWord_6209901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209901).length < 2 ^ (prefixWord ++ tailWord_6209901).sum := by decide
  have hdescent : baseEnd_6209901 < baseStart_6209901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209931 : List Nat := [1, 1, 1, 1, 4, 6, 1, 8]
def baseStart_6209931 : Nat := 118140960795 + 6209931 * 2 ^ 59
def prefixEnd_6209931 : Nat := 4983230072969 + 3 ^ 40 * 6209931 * 2
def baseEnd_6209931 : Nat := 118099238305764753707539

theorem tailTrace_6209931 : CollatzResearch.WordTrace tailWord_6209931 prefixEnd_6209931 118099238305764753707539 := by
  unfold tailWord_6209931
  simp only [CollatzResearch.WordTrace]
  refine ⟨226494790865488033623477647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150996527243658689082318431 226494790865488033623477647)
  ·
    refine ⟨339742186298232050435216471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226494790865488033623477647 339742186298232050435216471)
    ·
      refine ⟨509613279447348075652824707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339742186298232050435216471 509613279447348075652824707)
      ·
        refine ⟨764419919171022113479237061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509613279447348075652824707 764419919171022113479237061)
        ·
          refine ⟨143328734844566646277356949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 764419919171022113479237061 143328734844566646277356949)
          ·
            refine ⟨6718534445839061544251107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 143328734844566646277356949 6718534445839061544251107)
            ·
              refine ⟨10077801668758592316376661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6718534445839061544251107 10077801668758592316376661)
              ·
                refine ⟨118099238305764753707539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10077801668758592316376661 118099238305764753707539)
                ·
                  rfl

theorem cell23_6209931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 8].length) (baseStart_6209931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209931 prefixEnd_6209931 := by exact prefixLift 6209931
  have htrace : WordTrace (prefixWord ++ tailWord_6209931) baseStart_6209931 baseEnd_6209931 := by
    simpa [prefixWord, tailWord_6209931, baseEnd_6209931] using wordTrace_append hprefix tailTrace_6209931
  have hstable : (prefixWord ++ tailWord_6209931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209931).length < 2 ^ (prefixWord ++ tailWord_6209931).sum := by decide
  have hdescent : baseEnd_6209931 < baseStart_6209931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209959 : List Nat := [1, 1, 6, 1, 1, 3, 2, 3, 1, 2, 2]
def baseStart_6209959 : Nat := 118140960795 + 6209959 * 2 ^ 59
def prefixEnd_6209959 : Nat := 4983230072969 + 3 ^ 40 * 6209959 * 2
def baseEnd_6209959 : Nat := 3188693811713974240553425

theorem tailTrace_6209959 : CollatzResearch.WordTrace tailWord_6209959 prefixEnd_6209959 3188693811713974240553425 := by
  unfold tailWord_6209959
  simp only [CollatzResearch.WordTrace]
  refine ⟨226495812109386594405496931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150997208072924396270331287 226495812109386594405496931)
  ·
    refine ⟨339743718164079891608245397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226495812109386594405496931 339743718164079891608245397)
    ·
      refine ⟨15925486788941244919136503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 339743718164079891608245397 15925486788941244919136503)
      ·
        refine ⟨23888230183411867378704755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15925486788941244919136503 23888230183411867378704755)
        ·
          refine ⟨35832345275117801068057133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23888230183411867378704755 35832345275117801068057133)
          ·
            refine ⟨13437129478169175400521425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35832345275117801068057133 13437129478169175400521425)
            ·
              refine ⟨10077847108626881550391069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13437129478169175400521425 10077847108626881550391069)
              ·
                refine ⟨3779192665735080581396651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10077847108626881550391069 3779192665735080581396651)
                ·
                  refine ⟨5668788998602620872094977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3779192665735080581396651 5668788998602620872094977)
                  ·
                    refine ⟨4251591748951965654071233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5668788998602620872094977 4251591748951965654071233)
                    ·
                      refine ⟨3188693811713974240553425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4251591748951965654071233 3188693811713974240553425)
                      ·
                        rfl

theorem cell23_6209959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_6209959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209959 prefixEnd_6209959 := by exact prefixLift 6209959
  have htrace : WordTrace (prefixWord ++ tailWord_6209959) baseStart_6209959 baseEnd_6209959 := by
    simpa [prefixWord, tailWord_6209959, baseEnd_6209959] using wordTrace_append hprefix tailTrace_6209959
  have hstable : (prefixWord ++ tailWord_6209959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209959).length < 2 ^ (prefixWord ++ tailWord_6209959).sum := by decide
  have hdescent : baseEnd_6209959 < baseStart_6209959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209975 : List Nat := [1, 1, 3, 1, 3, 3, 3, 2, 2, 1, 3]
def baseStart_6209975 : Nat := 118140960795 + 6209975 * 2 ^ 59
def prefixEnd_6209975 : Nat := 4983230072969 + 3 ^ 40 * 6209975 * 2
def baseEnd_6209975 : Nat := 3188702027404446177953351

theorem tailTrace_6209975 : CollatzResearch.WordTrace tailWord_6209975 prefixEnd_6209975 3188702027404446177953351 := by
  unfold tailWord_6209975
  simp only [CollatzResearch.WordTrace]
  refine ⟨226496395677328629138079379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150997597118219086092052919 226496395677328629138079379)
  ·
    refine ⟨339744593515992943707119069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226496395677328629138079379 339744593515992943707119069)
    ·
      refine ⟨127404222568497353890169651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339744593515992943707119069 127404222568497353890169651)
      ·
        refine ⟨191106333852746030835254477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127404222568497353890169651 191106333852746030835254477)
        ·
          refine ⟨71664875194779761563220429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 191106333852746030835254477 71664875194779761563220429)
          ·
            refine ⟨26874328198042410586207661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71664875194779761563220429 26874328198042410586207661)
            ·
              refine ⟨10077873074265903969827873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26874328198042410586207661 10077873074265903969827873)
              ·
                refine ⟨7558404805699427977370905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10077873074265903969827873 7558404805699427977370905)
                ·
                  refine ⟨5668803604274570983028179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7558404805699427977370905 5668803604274570983028179)
                  ·
                    refine ⟨8503205406411856474542269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5668803604274570983028179 8503205406411856474542269)
                    ·
                      refine ⟨3188702027404446177953351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8503205406411856474542269 3188702027404446177953351)
                      ·
                        rfl

theorem cell23_6209975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 1, 3].length) (baseStart_6209975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209975 prefixEnd_6209975 := by exact prefixLift 6209975
  have htrace : WordTrace (prefixWord ++ tailWord_6209975) baseStart_6209975 baseEnd_6209975 := by
    simpa [prefixWord, tailWord_6209975, baseEnd_6209975] using wordTrace_append hprefix tailTrace_6209975
  have hstable : (prefixWord ++ tailWord_6209975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209975).length < 2 ^ (prefixWord ++ tailWord_6209975).sum := by decide
  have hdescent : baseEnd_6209975 < baseStart_6209975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209991 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 2, 6]
def baseStart_6209991 : Nat := 118140960795 + 6209991 * 2 ^ 59
def prefixEnd_6209991 : Nat := 4983230072969 + 3 ^ 40 * 6209991 * 2
def baseEnd_6209991 : Nat := 1062903414364972705117759

theorem tailTrace_6209991 : CollatzResearch.WordTrace tailWord_6209991 prefixEnd_6209991 1062903414364972705117759 := by
  unfold tailWord_6209991
  simp only [CollatzResearch.WordTrace]
  refine ⟨226496979245270663870661827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150997986163513775913774551 226496979245270663870661827)
  ·
    refine ⟨339745468867905995805992741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226496979245270663870661827 339745468867905995805992741)
    ·
      refine ⟨63702275412732374213623639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 339745468867905995805992741 63702275412732374213623639)
      ·
        refine ⟨95553413119098561320435459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63702275412732374213623639 95553413119098561320435459)
        ·
          refine ⟨143330119678647841980653189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95553413119098561320435459 143330119678647841980653189)
          ·
            refine ⟨26874397439746470371372473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 143330119678647841980653189 26874397439746470371372473)
            ·
              refine ⟨20155798079809852778529355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26874397439746470371372473 20155798079809852778529355)
              ·
                refine ⟨30233697119714779167794033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20155798079809852778529355 30233697119714779167794033)
                ·
                  refine ⟨22675272839786084375845525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30233697119714779167794033 22675272839786084375845525)
                  ·
                    refine ⟨1062903414364972705117759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22675272839786084375845525 1062903414364972705117759)
                    ·
                      rfl

theorem cell23_6209991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_6209991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209991 prefixEnd_6209991 := by exact prefixLift 6209991
  have htrace : WordTrace (prefixWord ++ tailWord_6209991) baseStart_6209991 baseEnd_6209991 := by
    simpa [prefixWord, tailWord_6209991, baseEnd_6209991] using wordTrace_append hprefix tailTrace_6209991
  have hstable : (prefixWord ++ tailWord_6209991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209991).length < 2 ^ (prefixWord ++ tailWord_6209991).sum := by decide
  have hdescent : baseEnd_6209991 < baseStart_6209991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6209992 : List Nat := [2, 1, 3, 1, 3, 3, 3, 1, 2, 1, 3]
def baseStart_6209992 : Nat := 118140960795 + 6209992 * 2 ^ 59
def prefixEnd_6209992 : Nat := 4983230072969 + 3 ^ 40 * 6209992 * 2
def baseEnd_6209992 : Nat := 3188710756575572611440773

theorem tailTrace_6209992 : CollatzResearch.WordTrace tailWord_6209992 prefixEnd_6209992 3188710756575572611440773 := by
  unfold tailWord_6209992
  simp only [CollatzResearch.WordTrace]
  refine ⟨113248507859133520520724115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 150998010478844694027632153 113248507859133520520724115)
  ·
    refine ⟨169872761788700280781086173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113248507859133520520724115 169872761788700280781086173)
    ·
      refine ⟨63702285670762605292907315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169872761788700280781086173 63702285670762605292907315)
      ·
        refine ⟨95553428506143907939360973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63702285670762605292907315 95553428506143907939360973)
        ·
          refine ⟨35832535689803965477260365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95553428506143907939360973 35832535689803965477260365)
          ·
            refine ⟨13437200883676487053972637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35832535689803965477260365 13437200883676487053972637)
            ·
              refine ⟨5038950331378682645239739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13437200883676487053972637 5038950331378682645239739)
              ·
                refine ⟨7558425497068023967859609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5038950331378682645239739 7558425497068023967859609)
                ·
                  refine ⟨5668819122801017975894707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7558425497068023967859609 5668819122801017975894707)
                  ·
                    refine ⟨8503228684201526963842061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5668819122801017975894707 8503228684201526963842061)
                    ·
                      refine ⟨3188710756575572611440773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8503228684201526963842061 3188710756575572611440773)
                      ·
                        rfl

theorem cell23_6209992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_6209992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6209992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6209992 prefixEnd_6209992 := by exact prefixLift 6209992
  have htrace : WordTrace (prefixWord ++ tailWord_6209992) baseStart_6209992 baseEnd_6209992 := by
    simpa [prefixWord, tailWord_6209992, baseEnd_6209992] using wordTrace_append hprefix tailTrace_6209992
  have hstable : (prefixWord ++ tailWord_6209992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6209992).length < 2 ^ (prefixWord ++ tailWord_6209992).sum := by decide
  have hdescent : baseEnd_6209992 < baseStart_6209992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6209992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210001 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 2, 4, 3]
def baseStart_6210001 : Nat := 118140960795 + 6210001 * 2 ^ 59
def prefixEnd_6210001 : Nat := 4983230072969 + 3 ^ 40 * 6210001 * 2
def baseEnd_6210001 : Nat := 3188715377901463076228231

theorem tailTrace_6210001 : CollatzResearch.WordTrace tailWord_6210001 prefixEnd_6210001 3188715377901463076228231 := by
  unfold tailWord_6210001
  simp only [CollatzResearch.WordTrace]
  refine ⟨226497343975234435578525857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150998229316822957052350571 226497343975234435578525857)
  ·
    refine ⟨169873007981425826683894393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226497343975234435578525857 169873007981425826683894393)
    ·
      refine ⟨127404755986069370012920795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169873007981425826683894393 127404755986069370012920795)
      ·
        refine ⟨191107133979104055019381193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127404755986069370012920795 191107133979104055019381193)
        ·
          refine ⟨143330350484328041264535895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191107133979104055019381193 143330350484328041264535895)
          ·
            refine ⟨214995525726492061896803843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143330350484328041264535895 214995525726492061896803843)
            ·
              refine ⟨322493288589738092845205765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 214995525726492061896803843 322493288589738092845205765)
              ·
                refine ⟨60467491610575892408476081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 322493288589738092845205765 60467491610575892408476081)
                ·
                  refine ⟨45350618707931919306357061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60467491610575892408476081 45350618707931919306357061)
                  ·
                    refine ⟨8503241007737234869941949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45350618707931919306357061 8503241007737234869941949)
                    ·
                      refine ⟨3188715377901463076228231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8503241007737234869941949 3188715377901463076228231)
                      ·
                        rfl

theorem cell23_6210001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_6210001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210001 prefixEnd_6210001 := by exact prefixLift 6210001
  have htrace : WordTrace (prefixWord ++ tailWord_6210001) baseStart_6210001 baseEnd_6210001 := by
    simpa [prefixWord, tailWord_6210001, baseEnd_6210001] using wordTrace_append hprefix tailTrace_6210001
  have hstable : (prefixWord ++ tailWord_6210001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210001).length < 2 ^ (prefixWord ++ tailWord_6210001).sum := by decide
  have hdescent : baseEnd_6210001 < baseStart_6210001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210015 : List Nat := [1, 1, 2, 3, 3, 2, 1, 2, 4, 2, 2]
def baseStart_6210015 : Nat := 118140960795 + 6210015 * 2 ^ 59
def prefixEnd_6210015 : Nat := 4983230072969 + 3 ^ 40 * 6210015 * 2
def baseEnd_6210015 : Nat := 3188722566630626021453167

theorem tailTrace_6210015 : CollatzResearch.WordTrace tailWord_6210015 prefixEnd_6210015 3188722566630626021453167 := by
  unfold tailWord_6210015
  simp only [CollatzResearch.WordTrace]
  refine ⟨226497854597183715969535499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150998569731455810646356999 226497854597183715969535499)
  ·
    refine ⟨339746781895775573954303249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226497854597183715969535499 339746781895775573954303249)
    ·
      refine ⟨254810086421831680465727437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339746781895775573954303249 254810086421831680465727437)
      ·
        refine ⟨95553782408186880174647789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 254810086421831680465727437 95553782408186880174647789)
        ·
          refine ⟨35832668403070080065492921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 95553782408186880174647789 35832668403070080065492921)
          ·
            refine ⟨26874501302302560049119691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35832668403070080065492921 26874501302302560049119691)
            ·
              refine ⟨40311751953453840073679537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26874501302302560049119691 40311751953453840073679537)
              ·
                refine ⟨30233813965090380055259653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40311751953453840073679537 30233813965090380055259653)
                ·
                  refine ⟨5668840118454446260361185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30233813965090380055259653 5668840118454446260361185)
                  ·
                    refine ⟨4251630088840834695270889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5668840118454446260361185 4251630088840834695270889)
                    ·
                      refine ⟨3188722566630626021453167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4251630088840834695270889 3188722566630626021453167)
                      ·
                        rfl

theorem cell23_6210015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_6210015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210015 prefixEnd_6210015 := by exact prefixLift 6210015
  have htrace : WordTrace (prefixWord ++ tailWord_6210015) baseStart_6210015 baseEnd_6210015 := by
    simpa [prefixWord, tailWord_6210015, baseEnd_6210015] using wordTrace_append hprefix tailTrace_6210015
  have hstable : (prefixWord ++ tailWord_6210015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210015).length < 2 ^ (prefixWord ++ tailWord_6210015).sum := by decide
  have hdescent : baseEnd_6210015 < baseStart_6210015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210049 : List Nat := [1, 2, 4, 1, 3, 1, 4, 1, 2, 2, 2]
def baseStart_6210049 : Nat := 118140960795 + 6210049 * 2 ^ 59
def prefixEnd_6210049 : Nat := 4983230072969 + 3 ^ 40 * 6210049 * 2
def baseEnd_6210049 : Nat := 3188740024972878888428011

theorem tailTrace_6210049 : CollatzResearch.WordTrace tailWord_6210049 prefixEnd_6210049 3188740024972878888428011 := by
  unfold tailWord_6210049
  simp only [CollatzResearch.WordTrace]
  refine ⟨226499094679060539776273201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150999396452707026517515467 226499094679060539776273201)
  ·
    refine ⟨169874321009295404832204901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226499094679060539776273201 169874321009295404832204901)
    ·
      refine ⟨31851435189242888406038419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 169874321009295404832204901 31851435189242888406038419)
      ·
        refine ⟨47777152783864332609057629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31851435189242888406038419 47777152783864332609057629)
        ·
          refine ⟨17916432293949124728396611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47777152783864332609057629 17916432293949124728396611)
          ·
            refine ⟨26874648440923687092594917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17916432293949124728396611 26874648440923687092594917)
            ·
              refine ⟨5038996582673191329861547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26874648440923687092594917 5038996582673191329861547)
              ·
                refine ⟨7558494874009786994792321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5038996582673191329861547 7558494874009786994792321)
                ·
                  refine ⟨5668871155507340246094241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7558494874009786994792321 5668871155507340246094241)
                  ·
                    refine ⟨4251653366630505184570681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5668871155507340246094241 4251653366630505184570681)
                    ·
                      refine ⟨3188740024972878888428011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4251653366630505184570681 3188740024972878888428011)
                      ·
                        rfl

theorem cell23_6210049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_6210049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210049 prefixEnd_6210049 := by exact prefixLift 6210049
  have htrace : WordTrace (prefixWord ++ tailWord_6210049) baseStart_6210049 baseEnd_6210049 := by
    simpa [prefixWord, tailWord_6210049, baseEnd_6210049] using wordTrace_append hprefix tailTrace_6210049
  have hstable : (prefixWord ++ tailWord_6210049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210049).length < 2 ^ (prefixWord ++ tailWord_6210049).sum := by decide
  have hdescent : baseEnd_6210049 < baseStart_6210049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210051 : List Nat := [1, 1, 1, 3, 2, 1, 3, 2, 4, 5]
def baseStart_6210051 : Nat := 118140960795 + 6210051 * 2 ^ 59
def prefixEnd_6210051 : Nat := 4983230072969 + 3 ^ 40 * 6210051 * 2
def baseEnd_6210051 : Nat := 1062913683978062626867667

theorem tailTrace_6210051 : CollatzResearch.WordTrace tailWord_6210051 prefixEnd_6210051 1062913683978062626867667 := by
  unfold tailWord_6210051
  simp only [CollatzResearch.WordTrace]
  refine ⟨226499167625053294117846007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 150999445083368862745230671 226499167625053294117846007)
  ·
    refine ⟨339748751437579941176769011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226499167625053294117846007 339748751437579941176769011)
    ·
      refine ⟨509623127156369911765153517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339748751437579941176769011 509623127156369911765153517)
      ·
        refine ⟨191108672683638716911932569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 509623127156369911765153517 191108672683638716911932569)
        ·
          refine ⟨143331504512729037683949427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191108672683638716911932569 143331504512729037683949427)
          ·
            refine ⟨214997256769093556525924141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143331504512729037683949427 214997256769093556525924141)
            ·
              refine ⟨80623971288410083697221553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 214997256769093556525924141 80623971288410083697221553)
              ·
                refine ⟨60467978466307562772916165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80623971288410083697221553 60467978466307562772916165)
                ·
                  refine ⟨11337745962432668019921781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60467978466307562772916165 11337745962432668019921781)
                  ·
                    refine ⟨1062913683978062626867667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11337745962432668019921781 1062913683978062626867667)
                    ·
                      rfl

theorem cell23_6210051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 5].length) (baseStart_6210051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210051 prefixEnd_6210051 := by exact prefixLift 6210051
  have htrace : WordTrace (prefixWord ++ tailWord_6210051) baseStart_6210051 baseEnd_6210051 := by
    simpa [prefixWord, tailWord_6210051, baseEnd_6210051] using wordTrace_append hprefix tailTrace_6210051
  have hstable : (prefixWord ++ tailWord_6210051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210051).length < 2 ^ (prefixWord ++ tailWord_6210051).sum := by decide
  have hdescent : baseEnd_6210051 < baseStart_6210051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210105 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 2, 4, 2]
def baseStart_6210105 : Nat := 118140960795 + 6210105 * 2 ^ 59
def prefixEnd_6210105 : Nat := 4983230072969 + 3 ^ 40 * 6210105 * 2
def baseEnd_6210105 : Nat := 3188768779889530669327753

theorem tailTrace_6210105 : CollatzResearch.WordTrace tailWord_6210105 prefixEnd_6210105 3188768779889530669327753 := by
  unfold tailWord_6210105
  simp only [CollatzResearch.WordTrace]
  refine ⟨226501137166857661340311769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151000758111238440893541179 226501137166857661340311769)
  ·
    refine ⟨169875852875143246005233827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226501137166857661340311769 169875852875143246005233827)
    ·
      refine ⟨254813779312714869007850741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169875852875143246005233827 254813779312714869007850741)
      ·
        refine ⟨23888791810567018969486007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 254813779312714869007850741 23888791810567018969486007)
        ·
          refine ⟨35833187715850528454229011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23888791810567018969486007 35833187715850528454229011)
          ·
            refine ⟨53749781573775792681343517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35833187715850528454229011 53749781573775792681343517)
            ·
              refine ⟨20156168090165922255503819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53749781573775792681343517 20156168090165922255503819)
              ·
                refine ⟨30234252135248883383255729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20156168090165922255503819 30234252135248883383255729)
                ·
                  refine ⟨22675689101436662537441797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30234252135248883383255729 22675689101436662537441797)
                  ·
                    refine ⟨4251691706519374225770337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22675689101436662537441797 4251691706519374225770337)
                    ·
                      refine ⟨3188768779889530669327753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4251691706519374225770337 3188768779889530669327753)
                      ·
                        rfl

theorem cell23_6210105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_6210105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210105 prefixEnd_6210105 := by exact prefixLift 6210105
  have htrace : WordTrace (prefixWord ++ tailWord_6210105) baseStart_6210105 baseEnd_6210105 := by
    simpa [prefixWord, tailWord_6210105, baseEnd_6210105] using wordTrace_append hprefix tailTrace_6210105
  have hstable : (prefixWord ++ tailWord_6210105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210105).length < 2 ^ (prefixWord ++ tailWord_6210105).sum := by decide
  have hdescent : baseEnd_6210105 < baseStart_6210105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210132 : List Nat := [2, 4, 1, 1, 1, 3, 1, 5, 1, 4]
def baseStart_6210132 : Nat := 118140960795 + 6210132 * 2 ^ 59
def prefixEnd_6210132 : Nat := 4983230072969 + 3 ^ 40 * 6210132 * 2
def baseEnd_6210132 : Nat := 1062927547955734021230043

theorem tailTrace_6210132 : CollatzResearch.WordTrace tailWord_6210132 prefixEnd_6210132 1062927547955734021230043 := by
  unfold tailWord_6210132
  simp only [CollatzResearch.WordTrace]
  refine ⟨113251060968879922475772325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151001414625173229967696433 113251060968879922475772325)
  ·
    refine ⟨21234573931664985464207311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113251060968879922475772325 21234573931664985464207311)
    ·
      refine ⟨31851860897497478196310967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21234573931664985464207311 31851860897497478196310967)
      ·
        refine ⟨47777791346246217294466451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31851860897497478196310967 47777791346246217294466451)
        ·
          refine ⟨71666687019369325941699677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47777791346246217294466451 71666687019369325941699677)
          ·
            refine ⟨26875007632263497228137379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71666687019369325941699677 26875007632263497228137379)
            ·
              refine ⟨40312511448395245842206069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26875007632263497228137379 40312511448395245842206069)
              ·
                refine ⟨3779297948287054297706819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40312511448395245842206069 3779297948287054297706819)
                ·
                  refine ⟨5668946922430581446560229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3779297948287054297706819 5668946922430581446560229)
                  ·
                    refine ⟨1062927547955734021230043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5668946922430581446560229 1062927547955734021230043)
                    ·
                      rfl

theorem cell23_6210132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_6210132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210132 prefixEnd_6210132 := by exact prefixLift 6210132
  have htrace : WordTrace (prefixWord ++ tailWord_6210132) baseStart_6210132 baseEnd_6210132 := by
    simpa [prefixWord, tailWord_6210132, baseEnd_6210132] using wordTrace_append hprefix tailTrace_6210132
  have hstable : (prefixWord ++ tailWord_6210132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210132).length < 2 ^ (prefixWord ++ tailWord_6210132).sum := by decide
  have hdescent : baseEnd_6210132 < baseStart_6210132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210145 : List Nat := [1, 2, 3, 1, 1, 6, 1, 2, 6]
def baseStart_6210145 : Nat := 118140960795 + 6210145 * 2 ^ 59
def prefixEnd_6210145 : Nat := 4983230072969 + 3 ^ 40 * 6210145 * 2
def baseEnd_6210145 : Nat := 354309924346190056980841

theorem tailTrace_6210145 : CollatzResearch.WordTrace tailWord_6210145 prefixEnd_6210145 354309924346190056980841 := by
  unfold tailWord_6210145
  simp only [CollatzResearch.WordTrace]
  refine ⟨226502596086712748171767889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151001730724475165447845259 226502596086712748171767889)
  ·
    refine ⟨169876947065034561128825917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226502596086712748171767889 169876947065034561128825917)
    ·
      refine ⟨63703855149387960423309719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 169876947065034561128825917 63703855149387960423309719)
      ·
        refine ⟨95555782724081940634964579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63703855149387960423309719 95555782724081940634964579)
        ·
          refine ⟨143333674086122910952446869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95555782724081940634964579 143333674086122910952446869)
          ·
            refine ⟨6718765972787011450895947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 143333674086122910952446869 6718765972787011450895947)
            ·
              refine ⟨10078148959180517176343921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6718765972787011450895947 10078148959180517176343921)
              ·
                refine ⟨7558611719385387882257941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10078148959180517176343921 7558611719385387882257941)
                ·
                  refine ⟨354309924346190056980841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7558611719385387882257941 354309924346190056980841)
                  ·
                    rfl

theorem cell23_6210145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 6].length) (baseStart_6210145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210145 prefixEnd_6210145 := by exact prefixLift 6210145
  have htrace : WordTrace (prefixWord ++ tailWord_6210145) baseStart_6210145 baseEnd_6210145 := by
    simpa [prefixWord, tailWord_6210145, baseEnd_6210145] using wordTrace_append hprefix tailTrace_6210145
  have hstable : (prefixWord ++ tailWord_6210145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210145).length < 2 ^ (prefixWord ++ tailWord_6210145).sum := by decide
  have hdescent : baseEnd_6210145 < baseStart_6210145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210162 : List Nat := [3, 2, 1, 2, 4, 1, 3, 1, 6]
def baseStart_6210162 : Nat := 118140960795 + 6210162 * 2 ^ 59
def prefixEnd_6210162 : Nat := 4983230072969 + 3 ^ 40 * 6210162 * 2
def baseEnd_6210162 : Nat := 354310894254092994034999

theorem tailTrace_6210162 : CollatzResearch.WordTrace tailWord_6210162 prefixEnd_6210162 354310894254092994034999 := by
  unfold tailWord_6210162
  simp only [CollatzResearch.WordTrace]
  refine ⟨56625804031912790018784185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151002144085100773383424493 56625804031912790018784185)
  ·
    refine ⟨42469353023934592514088139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56625804031912790018784185 42469353023934592514088139)
    ·
      refine ⟨63704029535901888771132209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42469353023934592514088139 63704029535901888771132209)
      ·
        refine ⟨47778022151926416578349157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63704029535901888771132209 47778022151926416578349157)
        ·
          refine ⟨8958379153486203108440467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47778022151926416578349157 8958379153486203108440467)
          ·
            refine ⟨13437568730229304662660701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8958379153486203108440467 13437568730229304662660701)
            ·
              refine ⟨5039088273835989248497763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13437568730229304662660701 5039088273835989248497763)
              ·
                refine ⟨7558632410753983872746645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5039088273835989248497763 7558632410753983872746645)
                ·
                  refine ⟨354310894254092994034999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7558632410753983872746645 354310894254092994034999)
                  ·
                    rfl

theorem cell23_6210162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_6210162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210162 prefixEnd_6210162 := by exact prefixLift 6210162
  have htrace : WordTrace (prefixWord ++ tailWord_6210162) baseStart_6210162 baseEnd_6210162 := by
    simpa [prefixWord, tailWord_6210162, baseEnd_6210162] using wordTrace_append hprefix tailTrace_6210162
  have hstable : (prefixWord ++ tailWord_6210162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210162).length < 2 ^ (prefixWord ++ tailWord_6210162).sum := by decide
  have hdescent : baseEnd_6210162 < baseStart_6210162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210205 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 4, 4]
def baseStart_6210205 : Nat := 118140960795 + 6210205 * 2 ^ 59
def prefixEnd_6210205 : Nat := 4983230072969 + 3 ^ 40 * 6210205 * 2
def baseEnd_6210205 : Nat := 1062940042651660092692431

theorem tailTrace_6210205 : CollatzResearch.WordTrace tailWord_6210205 prefixEnd_6210205 1062940042651660092692431 := by
  unfold tailWord_6210205
  simp only [CollatzResearch.WordTrace]
  refine ⟨226504784466495378418952069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151003189644330252279301379 226504784466495378418952069)
  ·
    refine ⟨42469647087467883453553513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 226504784466495378418952069 42469647087467883453553513)
    ·
      refine ⟨31852235315600912590165135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42469647087467883453553513 31852235315600912590165135)
      ·
        refine ⟨47778352973401368885247703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31852235315600912590165135 47778352973401368885247703)
        ·
          refine ⟨71667529460102053327871555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47778352973401368885247703 71667529460102053327871555)
          ·
            refine ⟨107501294190153079991807333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71667529460102053327871555 107501294190153079991807333)
            ·
              refine ⟨20156492660653702498463875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 107501294190153079991807333 20156492660653702498463875)
              ·
                refine ⟨30234738990980553747695813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20156492660653702498463875 30234738990980553747695813)
                ·
                  refine ⟨5669013560808853827692965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30234738990980553747695813 5669013560808853827692965)
                  ·
                    refine ⟨1062940042651660092692431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5669013560808853827692965 1062940042651660092692431)
                    ·
                      rfl

theorem cell23_6210205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_6210205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210205 prefixEnd_6210205 := by exact prefixLift 6210205
  have htrace : WordTrace (prefixWord ++ tailWord_6210205) baseStart_6210205 baseEnd_6210205 := by
    simpa [prefixWord, tailWord_6210205, baseEnd_6210205] using wordTrace_append hprefix tailTrace_6210205
  have hstable : (prefixWord ++ tailWord_6210205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210205).length < 2 ^ (prefixWord ++ tailWord_6210205).sum := by decide
  have hdescent : baseEnd_6210205 < baseStart_6210205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210229 : List Nat := [1, 3, 3, 3, 1, 3, 1, 2, 1, 1, 4]
def baseStart_6210229 : Nat := 118140960795 + 6210229 * 2 ^ 59
def prefixEnd_6210229 : Nat := 4983230072969 + 3 ^ 40 * 6210229 * 2
def baseEnd_6210229 : Nat := 3188832451490688184177183

theorem tailTrace_6210229 : CollatzResearch.WordTrace tailWord_6210229 prefixEnd_6210229 3188832451490688184177183 := by
  unfold tailWord_6210229
  simp only [CollatzResearch.WordTrace]
  refine ⟨226505659818408430517825741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151003773212272287011883827 226505659818408430517825741)
  ·
    refine ⟨84939622431903161444184653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226505659818408430517825741 84939622431903161444184653)
    ·
      refine ⟨31852358411963685541569245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84939622431903161444184653 31852358411963685541569245)
      ·
        refine ⟨11944634404486382078088467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31852358411963685541569245 11944634404486382078088467)
        ·
          refine ⟨17916951606729573117132701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11944634404486382078088467 17916951606729573117132701)
          ·
            refine ⟨6718856852523589918924763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17916951606729573117132701 6718856852523589918924763)
            ·
              refine ⟨10078285278785384878387145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6718856852523589918924763 10078285278785384878387145)
              ·
                refine ⟨7558713959089038658790359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10078285278785384878387145 7558713959089038658790359)
                ·
                  refine ⟨11338070938633557988185539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7558713959089038658790359 11338070938633557988185539)
                  ·
                    refine ⟨17007106407950336982278309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11338070938633557988185539 17007106407950336982278309)
                    ·
                      refine ⟨3188832451490688184177183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17007106407950336982278309 3188832451490688184177183)
                      ·
                        rfl

theorem cell23_6210229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_6210229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210229 prefixEnd_6210229 := by exact prefixLift 6210229
  have htrace : WordTrace (prefixWord ++ tailWord_6210229) baseStart_6210229 baseEnd_6210229 := by
    simpa [prefixWord, tailWord_6210229, baseEnd_6210229] using wordTrace_append hprefix tailTrace_6210229
  have hstable : (prefixWord ++ tailWord_6210229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210229).length < 2 ^ (prefixWord ++ tailWord_6210229).sum := by decide
  have hdescent : baseEnd_6210229 < baseStart_6210229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210263 : List Nat := [1, 1, 3, 2, 1, 6, 2, 2, 1, 2, 2]
def baseStart_6210263 : Nat := 118140960795 + 6210263 * 2 ^ 59
def prefixEnd_6210263 : Nat := 4983230072969 + 3 ^ 40 * 6210263 * 2
def baseEnd_6210263 : Nat := 3188849909832941051152027

theorem tailTrace_6210263 : CollatzResearch.WordTrace tailWord_6210263 prefixEnd_6210263 3188849909832941051152027 := by
  unfold tailWord_6210263
  simp only [CollatzResearch.WordTrace]
  refine ⟨226506899900285254324563443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151004599933523502883042295 226506899900285254324563443)
  ·
    refine ⟨339760349850427881486845165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226506899900285254324563443 339760349850427881486845165)
    ·
      refine ⟨127410131193910455557566937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339760349850427881486845165 127410131193910455557566937)
      ·
        refine ⟨95557598395432841668175203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127410131193910455557566937 95557598395432841668175203)
        ·
          refine ⟨143336397593149262502262805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95557598395432841668175203 143336397593149262502262805)
          ·
            refine ⟨6718893637178871679793569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 143336397593149262502262805 6718893637178871679793569)
            ·
              refine ⟨5039170227884153759845177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6718893637178871679793569 5039170227884153759845177)
              ·
                refine ⟨3779377670913115319883883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5039170227884153759845177 3779377670913115319883883)
                ·
                  refine ⟨5669066506369672979825825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3779377670913115319883883 5669066506369672979825825)
                  ·
                    refine ⟨4251799879777254734869369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5669066506369672979825825 4251799879777254734869369)
                    ·
                      refine ⟨3188849909832941051152027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4251799879777254734869369 3188849909832941051152027)
                      ·
                        rfl

theorem cell23_6210263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 1, 2, 2].length) (baseStart_6210263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210263 prefixEnd_6210263 := by exact prefixLift 6210263
  have htrace : WordTrace (prefixWord ++ tailWord_6210263) baseStart_6210263 baseEnd_6210263 := by
    simpa [prefixWord, tailWord_6210263, baseEnd_6210263] using wordTrace_append hprefix tailTrace_6210263
  have hstable : (prefixWord ++ tailWord_6210263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210263).length < 2 ^ (prefixWord ++ tailWord_6210263).sum := by decide
  have hdescent : baseEnd_6210263 < baseStart_6210263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210285 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_6210285 : Nat := 118140960795 + 6210285 * 2 ^ 59
def prefixEnd_6210285 : Nat := 4983230072969 + 3 ^ 40 * 6210285 * 2
def baseEnd_6210285 : Nat := 3188861206407339965076925

theorem tailTrace_6210285 : CollatzResearch.WordTrace tailWord_6210285 prefixEnd_6210285 3188861206407339965076925 := by
  unfold tailWord_6210285
  simp only [CollatzResearch.WordTrace]
  refine ⟨226507702306205552081864309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151005134870803701387909539 226507702306205552081864309)
  ·
    refine ⟨21235097091206770507674779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 226507702306205552081864309 21235097091206770507674779)
    ·
      refine ⟨31852645636810155761512169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21235097091206770507674779 31852645636810155761512169)
      ·
        refine ⟨23889484227607616821134127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31852645636810155761512169 23889484227607616821134127)
        ·
          refine ⟨35834226341411425231701191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23889484227607616821134127 35834226341411425231701191)
          ·
            refine ⟨53751339512117137847551787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35834226341411425231701191 53751339512117137847551787)
            ·
              refine ⟨80627009268175706771327681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53751339512117137847551787 80627009268175706771327681)
              ·
                refine ⟨60470256951131780078495761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80627009268175706771327681 60470256951131780078495761)
                ·
                  refine ⟨45352692713348835058871821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60470256951131780078495761 45352692713348835058871821)
                  ·
                    refine ⟨17007259767505813147076933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45352692713348835058871821 17007259767505813147076933)
                    ·
                      refine ⟨3188861206407339965076925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17007259767505813147076933 3188861206407339965076925)
                      ·
                        rfl

theorem cell23_6210285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_6210285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210285 prefixEnd_6210285 := by exact prefixLift 6210285
  have htrace : WordTrace (prefixWord ++ tailWord_6210285) baseStart_6210285 baseEnd_6210285 := by
    simpa [prefixWord, tailWord_6210285, baseEnd_6210285] using wordTrace_append hprefix tailTrace_6210285
  have hstable : (prefixWord ++ tailWord_6210285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210285).length < 2 ^ (prefixWord ++ tailWord_6210285).sum := by decide
  have hdescent : baseEnd_6210285 < baseStart_6210285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210306 : List Nat := [3, 4, 1, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_6210306 : Nat := 118140960795 + 6210306 * 2 ^ 59
def prefixEnd_6210306 : Nat := 4983230072969 + 3 ^ 40 * 6210306 * 2
def baseEnd_6210306 : Nat := 3188871989501084382914329

theorem tailTrace_6210306 : CollatzResearch.WordTrace tailWord_6210306 prefixEnd_6210306 3188871989501084382914329 := by
  unfold tailWord_6210306
  simp only [CollatzResearch.WordTrace]
  refine ⟨56627117059782368167094693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151005645492752981778919181 56627117059782368167094693)
  ·
    refine ⟨10617584448709194031330255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56627117059782368167094693 10617584448709194031330255)
    ·
      refine ⟨15926376673063791046995383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10617584448709194031330255 15926376673063791046995383)
      ·
        refine ⟨23889565009595686570493075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15926376673063791046995383 23889565009595686570493075)
        ·
          refine ⟨35834347514393529855739613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23889565009595686570493075 35834347514393529855739613)
          ·
            refine ⟨13437880317897573695902355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35834347514393529855739613 13437880317897573695902355)
            ·
              refine ⟨20156820476846360543853533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13437880317897573695902355 20156820476846360543853533)
              ·
                refine ⟨7558807678817385203945075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20156820476846360543853533 7558807678817385203945075)
                ·
                  refine ⟨11338211518226077805917613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7558807678817385203945075 11338211518226077805917613)
                  ·
                    refine ⟨4251829319334779177219105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11338211518226077805917613 4251829319334779177219105)
                    ·
                      refine ⟨3188871989501084382914329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4251829319334779177219105 3188871989501084382914329)
                      ·
                        rfl

theorem cell23_6210306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_6210306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210306 prefixEnd_6210306 := by exact prefixLift 6210306
  have htrace : WordTrace (prefixWord ++ tailWord_6210306) baseStart_6210306 baseEnd_6210306 := by
    simpa [prefixWord, tailWord_6210306, baseEnd_6210306] using wordTrace_append hprefix tailTrace_6210306
  have hstable : (prefixWord ++ tailWord_6210306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210306).length < 2 ^ (prefixWord ++ tailWord_6210306).sum := by decide
  have hdescent : baseEnd_6210306 < baseStart_6210306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210325 : List Nat := [1, 3, 2, 1, 2, 2, 4, 1, 7]
def baseStart_6210325 : Nat := 118140960795 + 6210325 * 2 ^ 59
def prefixEnd_6210325 : Nat := 4983230072969 + 3 ^ 40 * 6210325 * 2
def baseEnd_6210325 : Nat := 354320193959279978730749

theorem tailTrace_6210325 : CollatzResearch.WordTrace tailWord_6210325 prefixEnd_6210325 354320193959279978730749 := by
  unfold tailWord_6210325
  simp only [CollatzResearch.WordTrace]
  refine ⟨226509161226060638913320429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151006107484040425942213619 226509161226060638913320429)
  ·
    refine ⟨84940935459772739592495161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226509161226060638913320429 84940935459772739592495161)
    ·
      refine ⟨63705701594829554694371371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84940935459772739592495161 63705701594829554694371371)
      ·
        refine ⟨95558552392244332041557057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63705701594829554694371371 95558552392244332041557057)
        ·
          refine ⟨71668914294183249031167793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 95558552392244332041557057 71668914294183249031167793)
          ·
            refine ⟨53751685720637436773375845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71668914294183249031167793 53751685720637436773375845)
            ·
              refine ⟨10078441072619519395007971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53751685720637436773375845 10078441072619519395007971)
              ·
                refine ⟨15117661608929279092511957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10078441072619519395007971 15117661608929279092511957)
                ·
                  refine ⟨354320193959279978730749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15117661608929279092511957 354320193959279978730749)
                  ·
                    rfl

theorem cell23_6210325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 7].length) (baseStart_6210325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210325 prefixEnd_6210325 := by exact prefixLift 6210325
  have htrace : WordTrace (prefixWord ++ tailWord_6210325) baseStart_6210325 baseEnd_6210325 := by
    simpa [prefixWord, tailWord_6210325, baseEnd_6210325] using wordTrace_append hprefix tailTrace_6210325
  have hstable : (prefixWord ++ tailWord_6210325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210325).length < 2 ^ (prefixWord ++ tailWord_6210325).sum := by decide
  have hdescent : baseEnd_6210325 < baseStart_6210325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210355 : List Nat := [1, 1, 1, 2, 6, 1, 2, 1, 1, 7]
def baseStart_6210355 : Nat := 118140960795 + 6210355 * 2 ^ 59
def prefixEnd_6210355 : Nat := 4983230072969 + 3 ^ 40 * 6210355 * 2
def baseEnd_6210355 : Nat := 1062965716684384897067201

theorem tailTrace_6210355 : CollatzResearch.WordTrace tailWord_6210355 prefixEnd_6210355 1062965716684384897067201 := by
  unfold tailWord_6210355
  simp only [CollatzResearch.WordTrace]
  refine ⟨226510255415951954036912519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151006836943967969357941679 226510255415951954036912519)
  ·
    refine ⟨339765383123927931055368779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226510255415951954036912519 339765383123927931055368779)
    ·
      refine ⟨509648074685891896583053169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339765383123927931055368779 509648074685891896583053169)
      ·
        refine ⟨382236056014418922437289877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 509648074685891896583053169 382236056014418922437289877)
        ·
          refine ⟨17917315125675886989247963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 382236056014418922437289877 17917315125675886989247963)
          ·
            refine ⟨26875972688513830483871945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17917315125675886989247963 26875972688513830483871945)
            ·
              refine ⟨20156979516385372862903959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26875972688513830483871945 20156979516385372862903959)
              ·
                refine ⟨30235469274578059294355939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20156979516385372862903959 30235469274578059294355939)
                ·
                  refine ⟨45353203911867088941533909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30235469274578059294355939 45353203911867088941533909)
                  ·
                    refine ⟨1062965716684384897067201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 45353203911867088941533909 1062965716684384897067201)
                    ·
                      rfl

theorem cell23_6210355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 7].length) (baseStart_6210355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210355 prefixEnd_6210355 := by exact prefixLift 6210355
  have htrace : WordTrace (prefixWord ++ tailWord_6210355) baseStart_6210355 baseEnd_6210355 := by
    simpa [prefixWord, tailWord_6210355, baseEnd_6210355] using wordTrace_append hprefix tailTrace_6210355
  have hstable : (prefixWord ++ tailWord_6210355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210355).length < 2 ^ (prefixWord ++ tailWord_6210355).sum := by decide
  have hdescent : baseEnd_6210355 < baseStart_6210355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210392 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 2, 4, 2]
def baseStart_6210392 : Nat := 118140960795 + 6210392 * 2 ^ 59
def prefixEnd_6210392 : Nat := 4983230072969 + 3 ^ 40 * 6210392 * 2
def baseEnd_6210392 : Nat := 3188916148837371046438933

theorem tailTrace_6210392 : CollatzResearch.WordTrace tailWord_6210392 prefixEnd_6210392 3188916148837371046438933 := by
  unfold tailWord_6210392
  simp only [CollatzResearch.WordTrace]
  refine ⟨113255802458408954678004715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151007736611211939570672953 113255802458408954678004715)
  ·
    refine ⟨169883703687613432017007073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113255802458408954678004715 169883703687613432017007073)
    ·
      refine ⟨127412777765710074012755305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169883703687613432017007073 127412777765710074012755305)
      ·
        refine ⟨95559583324282555509566479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127412777765710074012755305 95559583324282555509566479)
        ·
          refine ⟨143339374986423833264349719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95559583324282555509566479 143339374986423833264349719)
          ·
            refine ⟨215009062479635749896524579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143339374986423833264349719 215009062479635749896524579)
            ·
              refine ⟨322513593719453624844786869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215009062479635749896524579 322513593719453624844786869)
              ·
                refine ⟨30235649411198777329198769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 322513593719453624844786869 30235649411198777329198769)
                ·
                  refine ⟨22676737058399082996899077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30235649411198777329198769 22676737058399082996899077)
                  ·
                    refine ⟨4251888198449828061918577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22676737058399082996899077 4251888198449828061918577)
                    ·
                      refine ⟨3188916148837371046438933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4251888198449828061918577 3188916148837371046438933)
                      ·
                        rfl

theorem cell23_6210392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_6210392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210392 prefixEnd_6210392 := by exact prefixLift 6210392
  have htrace : WordTrace (prefixWord ++ tailWord_6210392) baseStart_6210392 baseEnd_6210392 := by
    simpa [prefixWord, tailWord_6210392, baseEnd_6210392] using wordTrace_append hprefix tailTrace_6210392
  have hstable : (prefixWord ++ tailWord_6210392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210392).length < 2 ^ (prefixWord ++ tailWord_6210392).sum := by decide
  have hdescent : baseEnd_6210392 < baseStart_6210392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210405 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 2, 4, 4]
def baseStart_6210405 : Nat := 118140960795 + 6210405 * 2 ^ 59
def prefixEnd_6210405 : Nat := 4983230072969 + 3 ^ 40 * 6210405 * 2
def baseEnd_6210405 : Nat := 3188922824085879495576373

theorem tailTrace_6210405 : CollatzResearch.WordTrace tailWord_6210405 prefixEnd_6210405 3188922824085879495576373 := by
  unfold tailWord_6210405
  simp only [CollatzResearch.WordTrace]
  refine ⟨226512079065770812576232669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151008052710513875050821779 226512079065770812576232669)
  ·
    refine ⟨84942029649664054716087251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226512079065770812576232669 84942029649664054716087251)
    ·
      refine ⟨127413044474496082074130877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84942029649664054716087251 127413044474496082074130877)
      ·
        refine ⟨47779891677936030777799079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127413044474496082074130877 47779891677936030777799079)
        ·
          refine ⟨71669837516904046166698619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47779891677936030777799079 71669837516904046166698619)
          ·
            refine ⟨107504756275356069250047929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71669837516904046166698619 107504756275356069250047929)
            ·
              refine ⟨80628567206517051937535947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107504756275356069250047929 80628567206517051937535947)
              ·
                refine ⟨120942850809775577906303921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80628567206517051937535947 120942850809775577906303921)
                ·
                  refine ⟨90707138107331683429727941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120942850809775577906303921 90707138107331683429727941)
                  ·
                    refine ⟨17007588395124690643073989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 90707138107331683429727941 17007588395124690643073989)
                    ·
                      refine ⟨3188922824085879495576373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17007588395124690643073989 3188922824085879495576373)
                      ·
                        rfl

theorem cell23_6210405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_6210405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210405 prefixEnd_6210405 := by exact prefixLift 6210405
  have htrace : WordTrace (prefixWord ++ tailWord_6210405) baseStart_6210405 baseEnd_6210405 := by
    simpa [prefixWord, tailWord_6210405, baseEnd_6210405] using wordTrace_append hprefix tailTrace_6210405
  have hstable : (prefixWord ++ tailWord_6210405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210405).length < 2 ^ (prefixWord ++ tailWord_6210405).sum := by decide
  have hdescent : baseEnd_6210405 < baseStart_6210405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210435 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 6]
def baseStart_6210435 : Nat := 118140960795 + 6210435 * 2 ^ 59
def prefixEnd_6210435 : Nat := 4983230072969 + 3 ^ 40 * 6210435 * 2
def baseEnd_6210435 : Nat := 3188938228505514378201235

theorem tailTrace_6210435 : CollatzResearch.WordTrace tailWord_6210435 prefixEnd_6210435 3188938228505514378201235 := by
  unfold tailWord_6210435
  simp only [CollatzResearch.WordTrace]
  refine ⟨226513173255662127699824759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151008782170441418466549839 226513173255662127699824759)
  ·
    refine ⟨339769759883493191549737139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226513173255662127699824759 339769759883493191549737139)
    ·
      refine ⟨509654639825239787324605709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339769759883493191549737139 509654639825239787324605709)
      ·
        refine ⟨191120489934464920246727141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 509654639825239787324605709 191120489934464920246727141)
        ·
          refine ⟨35835091862712172546261339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 191120489934464920246727141 35835091862712172546261339)
          ·
            refine ⟨53752637794068258819392009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35835091862712172546261339 53752637794068258819392009)
            ·
              refine ⟨40314478345551194114544007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53752637794068258819392009 40314478345551194114544007)
              ·
                refine ⟨60471717518326791171816011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40314478345551194114544007 60471717518326791171816011)
                ·
                  refine ⟨90707576277490186757724017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 60471717518326791171816011 90707576277490186757724017)
                  ·
                    refine ⟨68030682208117640068293013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 90707576277490186757724017 68030682208117640068293013)
                    ·
                      refine ⟨3188938228505514378201235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 68030682208117640068293013 3188938228505514378201235)
                      ·
                        rfl

theorem cell23_6210435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_6210435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210435 prefixEnd_6210435 := by exact prefixLift 6210435
  have htrace : WordTrace (prefixWord ++ tailWord_6210435) baseStart_6210435 baseEnd_6210435 := by
    simpa [prefixWord, tailWord_6210435, baseEnd_6210435] using wordTrace_append hprefix tailTrace_6210435
  have hstable : (prefixWord ++ tailWord_6210435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210435).length < 2 ^ (prefixWord ++ tailWord_6210435).sum := by decide
  have hdescent : baseEnd_6210435 < baseStart_6210435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210455 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 7]
def baseStart_6210455 : Nat := 118140960795 + 6210455 * 2 ^ 59
def prefixEnd_6210455 : Nat := 4983230072969 + 3 ^ 40 * 6210455 * 2
def baseEnd_6210455 : Nat := 3188948498118604299951143

theorem tailTrace_6210455 : CollatzResearch.WordTrace tailWord_6210455 prefixEnd_6210455 3188948498118604299951143 := by
  unfold tailWord_6210455
  simp only [CollatzResearch.WordTrace]
  refine ⟨226513902715589671115552819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151009268477059780743701879 226513902715589671115552819)
  ·
    refine ⟨339770854073384506673329229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226513902715589671115552819 339770854073384506673329229)
    ·
      refine ⟨127414070277519190002498461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 339770854073384506673329229 127414070277519190002498461)
      ·
        refine ⟨47780276354069696250936923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 127414070277519190002498461 47780276354069696250936923)
        ·
          refine ⟨71670414531104544376405385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47780276354069696250936923 71670414531104544376405385)
          ·
            refine ⟨53752810898328408282304039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71670414531104544376405385 53752810898328408282304039)
            ·
              refine ⟨80629216347492612423456059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53752810898328408282304039 80629216347492612423456059)
              ·
                refine ⟨120943824521238918635184089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 80629216347492612423456059 120943824521238918635184089)
                ·
                  refine ⟨90707868390929188976388067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 120943824521238918635184089 90707868390929188976388067)
                  ·
                    refine ⟨136061802586393783464582101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 90707868390929188976388067 136061802586393783464582101)
                    ·
                      refine ⟨3188948498118604299951143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 136061802586393783464582101 3188948498118604299951143)
                      ·
                        rfl

theorem cell23_6210455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_6210455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210455 prefixEnd_6210455 := by exact prefixLift 6210455
  have htrace : WordTrace (prefixWord ++ tailWord_6210455) baseStart_6210455 baseEnd_6210455 := by
    simpa [prefixWord, tailWord_6210455, baseEnd_6210455] using wordTrace_append hprefix tailTrace_6210455
  have hstable : (prefixWord ++ tailWord_6210455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210455).length < 2 ^ (prefixWord ++ tailWord_6210455).sum := by decide
  have hdescent : baseEnd_6210455 < baseStart_6210455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210499 : List Nat := [1, 1, 1, 3, 1, 1, 2, 2, 7, 2, 2]
def baseStart_6210499 : Nat := 118140960795 + 6210499 * 2 ^ 59
def prefixEnd_6210499 : Nat := 4983230072969 + 3 ^ 40 * 6210499 * 2
def baseEnd_6210499 : Nat := 3188971091267402127800941

theorem tailTrace_6210499 : CollatzResearch.WordTrace tailWord_6210499 prefixEnd_6210499 3188971091267402127800941 := by
  unfold tailWord_6210499
  simp only [CollatzResearch.WordTrace]
  refine ⟨226515507527430266630154551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151010338351620177753436367 226515507527430266630154551)
  ·
    refine ⟨339773261291145399945231827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226515507527430266630154551 339773261291145399945231827)
    ·
      refine ⟨509659891936718099917847741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339773261291145399945231827 509659891936718099917847741)
      ·
        refine ⟨191122459476269287469192903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 509659891936718099917847741 191122459476269287469192903)
        ·
          refine ⟨286683689214403931203789355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 191122459476269287469192903 286683689214403931203789355)
          ·
            refine ⟨430025533821605896805684033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286683689214403931203789355 430025533821605896805684033)
            ·
              refine ⟨322519150366204422604263025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430025533821605896805684033 322519150366204422604263025)
              ·
                refine ⟨241889362774653316953197269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322519150366204422604263025 241889362774653316953197269)
                ·
                  refine ⟨5669281940030937116090561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 241889362774653316953197269 5669281940030937116090561)
                  ·
                    refine ⟨4251961455023202837067921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5669281940030937116090561 4251961455023202837067921)
                    ·
                      refine ⟨3188971091267402127800941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4251961455023202837067921 3188971091267402127800941)
                      ·
                        rfl

theorem cell23_6210499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 2, 2].length) (baseStart_6210499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210499 prefixEnd_6210499 := by exact prefixLift 6210499
  have htrace : WordTrace (prefixWord ++ tailWord_6210499) baseStart_6210499 baseEnd_6210499 := by
    simpa [prefixWord, tailWord_6210499, baseEnd_6210499] using wordTrace_append hprefix tailTrace_6210499
  have hstable : (prefixWord ++ tailWord_6210499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210499).length < 2 ^ (prefixWord ++ tailWord_6210499).sum := by decide
  have hdescent : baseEnd_6210499 < baseStart_6210499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210516 : List Nat := [2, 4, 1, 2, 1, 3, 2, 2, 1, 1, 4]
def baseStart_6210516 : Nat := 118140960795 + 6210516 * 2 ^ 59
def prefixEnd_6210516 : Nat := 4983230072969 + 3 ^ 40 * 6210516 * 2
def baseEnd_6210516 : Nat := 3188979820438528561288363

theorem tailTrace_6210516 : CollatzResearch.WordTrace tailWord_6210516 prefixEnd_6210516 3188979820438528561288363 := by
  unfold tailWord_6210516
  simp only [CollatzResearch.WordTrace]
  refine ⟨113258063784184339266761701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151010751712245785689015601 113258063784184339266761701)
  ·
    refine ⟨21235886959534563612517819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 113258063784184339266761701 21235886959534563612517819)
    ·
      refine ⟨31853830439301845418776729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21235886959534563612517819 31853830439301845418776729)
      ·
        refine ⟨23890372829476384064082547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31853830439301845418776729 23890372829476384064082547)
        ·
          refine ⟨35835559244214576096123821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23890372829476384064082547 35835559244214576096123821)
          ·
            refine ⟨13438334716580466036046433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35835559244214576096123821 13438334716580466036046433)
            ·
              refine ⟨10078751037435349527034825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13438334716580466036046433 10078751037435349527034825)
              ·
                refine ⟨7559063278076512145276119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10078751037435349527034825 7559063278076512145276119)
                ·
                  refine ⟨11338594917114768217914179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7559063278076512145276119 11338594917114768217914179)
                  ·
                    refine ⟨17007892375672152326871269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11338594917114768217914179 17007892375672152326871269)
                    ·
                      refine ⟨3188979820438528561288363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17007892375672152326871269 3188979820438528561288363)
                      ·
                        rfl

theorem cell23_6210516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_6210516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210516 prefixEnd_6210516 := by exact prefixLift 6210516
  have htrace : WordTrace (prefixWord ++ tailWord_6210516) baseStart_6210516 baseEnd_6210516 := by
    simpa [prefixWord, tailWord_6210516, baseEnd_6210516] using wordTrace_append hprefix tailTrace_6210516
  have hstable : (prefixWord ++ tailWord_6210516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210516).length < 2 ^ (prefixWord ++ tailWord_6210516).sum := by decide
  have hdescent : baseEnd_6210516 < baseStart_6210516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210522 : List Nat := [3, 1, 1, 2, 4, 2, 1, 9]
def baseStart_6210522 : Nat := 118140960795 + 6210522 * 2 ^ 59
def prefixEnd_6210522 : Nat := 4983230072969 + 3 ^ 40 * 6210522 * 2
def baseEnd_6210522 : Nat := 118110477826757612511605

theorem tailTrace_6210522 : CollatzResearch.WordTrace tailWord_6210522 prefixEnd_6210522 118110477826757612511605 := by
  unfold tailWord_6210522
  simp only [CollatzResearch.WordTrace]
  refine ⟨56629086601586735389560455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151010897604231294372161213 56629086601586735389560455)
  ·
    refine ⟨84943629902380103084340683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56629086601586735389560455 84943629902380103084340683)
    ·
      refine ⟨127415444853570154626511025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84943629902380103084340683 127415444853570154626511025)
      ·
        refine ⟨95561583640177615969883269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127415444853570154626511025 95561583640177615969883269)
        ·
          refine ⟨17917796932533302994353113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95561583640177615969883269 17917796932533302994353113)
          ·
            refine ⟨13438347699399977245764835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17917796932533302994353113 13438347699399977245764835)
            ·
              refine ⟨20157521549099965868647253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13438347699399977245764835 20157521549099965868647253)
              ·
                refine ⟨118110477826757612511605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20157521549099965868647253 118110477826757612511605)
                ·
                  rfl

theorem cell23_6210522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 9].length) (baseStart_6210522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210522 prefixEnd_6210522 := by exact prefixLift 6210522
  have htrace : WordTrace (prefixWord ++ tailWord_6210522) baseStart_6210522 baseEnd_6210522 := by
    simpa [prefixWord, tailWord_6210522, baseEnd_6210522] using wordTrace_append hprefix tailTrace_6210522
  have hstable : (prefixWord ++ tailWord_6210522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210522).length < 2 ^ (prefixWord ++ tailWord_6210522).sum := by decide
  have hdescent : baseEnd_6210522 < baseStart_6210522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210550 : List Nat := [5, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2]
def baseStart_6210550 : Nat := 118140960795 + 6210550 * 2 ^ 59
def prefixEnd_6210550 : Nat := 4983230072969 + 3 ^ 40 * 6210550 * 2
def baseEnd_6210550 : Nat := 3188997278780781428263207

theorem tailTrace_6210550 : CollatzResearch.WordTrace tailWord_6210550 prefixEnd_6210550 3188997278780781428263207 := by
  unfold tailWord_6210550
  simp only [CollatzResearch.WordTrace]
  refine ⟨14157335478140343896266319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 151011578433497001560174069 14157335478140343896266319)
  ·
    refine ⟨21236003217210515844399479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14157335478140343896266319 21236003217210515844399479)
    ·
      refine ⟨31854004825815773766599219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21236003217210515844399479 31854004825815773766599219)
      ·
        refine ⟨47781007238723660649898829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31854004825815773766599219 47781007238723660649898829)
        ·
          refine ⟨17917877714521372743712061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47781007238723660649898829 17917877714521372743712061)
          ·
            refine ⟨6719204142945514778892023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17917877714521372743712061 6719204142945514778892023)
            ·
              refine ⟨10078806214418272168338035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6719204142945514778892023 10078806214418272168338035)
              ·
                refine ⟨15118209321627408252507053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10078806214418272168338035 15118209321627408252507053)
                ·
                  refine ⟨5669328495610278094690145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15118209321627408252507053 5669328495610278094690145)
                  ·
                    refine ⟨4251996371707708571017609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5669328495610278094690145 4251996371707708571017609)
                    ·
                      refine ⟨3188997278780781428263207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4251996371707708571017609 3188997278780781428263207)
                      ·
                        rfl

theorem cell23_6210550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_6210550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210550 prefixEnd_6210550 := by exact prefixLift 6210550
  have htrace : WordTrace (prefixWord ++ tailWord_6210550) baseStart_6210550 baseEnd_6210550 := by
    simpa [prefixWord, tailWord_6210550, baseEnd_6210550] using wordTrace_append hprefix tailTrace_6210550
  have hstable : (prefixWord ++ tailWord_6210550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210550).length < 2 ^ (prefixWord ++ tailWord_6210550).sum := by decide
  have hdescent : baseEnd_6210550 < baseStart_6210550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210606 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_6210606 : Nat := 118140960795 + 6210606 * 2 ^ 59
def prefixEnd_6210606 : Nat := 4983230072969 + 3 ^ 40 * 6210606 * 2
def baseEnd_6210606 : Nat := 3189026033697433209162949

theorem tailTrace_6210606 : CollatzResearch.WordTrace tailWord_6210606 prefixEnd_6210606 3189026033697433209162949 := by
  unfold tailWord_6210606
  simp only [CollatzResearch.WordTrace]
  refine ⟨28314926267255327988037459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151012940092028415936199781 28314926267255327988037459)
  ·
    refine ⟨42472389400882991982056189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28314926267255327988037459 42472389400882991982056189)
    ·
      refine ⟨15927146025331121993271071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42472389400882991982056189 15927146025331121993271071)
      ·
        refine ⟨23890719037996682989906607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15927146025331121993271071 23890719037996682989906607)
        ·
          refine ⟨35836078556995024484859911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23890719037996682989906607 35836078556995024484859911)
          ·
            refine ⟨53754117835492536727289867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35836078556995024484859911 53754117835492536727289867)
            ·
              refine ⟨80631176753238805090934801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53754117835492536727289867 80631176753238805090934801)
              ·
                refine ⟨60473382564929103818201101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80631176753238805090934801 60473382564929103818201101)
                ·
                  refine ⟨22677518461848413931825413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60473382564929103818201101 22677518461848413931825413)
                  ·
                    refine ⟨4252034711596577612217265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22677518461848413931825413 4252034711596577612217265)
                    ·
                      refine ⟨3189026033697433209162949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4252034711596577612217265 3189026033697433209162949)
                      ·
                        rfl

theorem cell23_6210606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_6210606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210606 prefixEnd_6210606 := by exact prefixLift 6210606
  have htrace : WordTrace (prefixWord ++ tailWord_6210606) baseStart_6210606 baseEnd_6210606 := by
    simpa [prefixWord, tailWord_6210606, baseEnd_6210606] using wordTrace_append hprefix tailTrace_6210606
  have hstable : (prefixWord ++ tailWord_6210606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210606).length < 2 ^ (prefixWord ++ tailWord_6210606).sum := by decide
  have hdescent : baseEnd_6210606 < baseStart_6210606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210649 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 1, 7, 2]
def baseStart_6210649 : Nat := 118140960795 + 6210649 * 2 ^ 59
def prefixEnd_6210649 : Nat := 4983230072969 + 3 ^ 40 * 6210649 * 2
def baseEnd_6210649 : Nat := 3189048113365576540925251

theorem tailTrace_6210649 : CollatzResearch.WordTrace tailWord_6210649 prefixEnd_6210649 3189048113365576540925251 := by
  unfold tailWord_6210649
  simp only [CollatzResearch.WordTrace]
  refine ⟨226520978476886842248115001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151013985651257894832076667 226520978476886842248115001)
  ·
    refine ⟨169890733857665131686086251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226520978476886842248115001 169890733857665131686086251)
    ·
      refine ⟨254836100786497697529129377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169890733857665131686086251 254836100786497697529129377)
      ·
        refine ⟨191127075589873273146847033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 254836100786497697529129377 191127075589873273146847033)
        ·
          refine ⟨143345306692404954860135275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191127075589873273146847033 143345306692404954860135275)
          ·
            refine ⟨215017960038607432290202913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143345306692404954860135275 215017960038607432290202913)
            ·
              refine ⟨161263470028955574217652185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 215017960038607432290202913 161263470028955574217652185)
              ·
                refine ⟨120947602521716680663239139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 161263470028955574217652185 120947602521716680663239139)
                ·
                  refine ⟨181421403782575020994858709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 120947602521716680663239139 181421403782575020994858709)
                  ·
                    refine ⟨4252064151154102054567001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 181421403782575020994858709 4252064151154102054567001)
                    ·
                      refine ⟨3189048113365576540925251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4252064151154102054567001 3189048113365576540925251)
                      ·
                        rfl

theorem cell23_6210649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 7, 2].length) (baseStart_6210649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210649 prefixEnd_6210649 := by exact prefixLift 6210649
  have htrace : WordTrace (prefixWord ++ tailWord_6210649) baseStart_6210649 baseEnd_6210649 := by
    simpa [prefixWord, tailWord_6210649, baseEnd_6210649] using wordTrace_append hprefix tailTrace_6210649
  have hstable : (prefixWord ++ tailWord_6210649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210649).length < 2 ^ (prefixWord ++ tailWord_6210649).sum := by decide
  have hdescent : baseEnd_6210649 < baseStart_6210649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210699 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 3]
def baseStart_6210699 : Nat := 118140960795 + 6210699 * 2 ^ 59
def prefixEnd_6210699 : Nat := 4983230072969 + 3 ^ 40 * 6210699 * 2
def baseEnd_6210699 : Nat := 3189073787398301345300021

theorem tailTrace_6210699 : CollatzResearch.WordTrace tailWord_6210699 prefixEnd_6210699 3189073787398301345300021 := by
  unfold tailWord_6210699
  simp only [CollatzResearch.WordTrace]
  refine ⟨226522802126705700787435151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151015201417803800524956767 226522802126705700787435151)
  ·
    refine ⟨339784203190058551181152727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226522802126705700787435151 339784203190058551181152727)
    ·
      refine ⟨509676304785087826771729091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339784203190058551181152727 509676304785087826771729091)
      ·
        refine ⟨764514457177631740157593637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509676304785087826771729091 764514457177631740157593637)
        ·
          refine ⟨143346460720805951279548807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 764514457177631740157593637 143346460720805951279548807)
          ·
            refine ⟨215019691081208926919323211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 143346460720805951279548807 215019691081208926919323211)
            ·
              refine ⟨322529536621813390378984817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 215019691081208926919323211 322529536621813390378984817)
              ·
                refine ⟨241897152466360042784238613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322529536621813390378984817 241897152466360042784238613)
                ·
                  refine ⟨11338929021860627005511185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 241897152466360042784238613 11338929021860627005511185)
                  ·
                    refine ⟨8504196766395470254133389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11338929021860627005511185 8504196766395470254133389)
                    ·
                      refine ⟨3189073787398301345300021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8504196766395470254133389 3189073787398301345300021)
                      ·
                        rfl

theorem cell23_6210699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 3].length) (baseStart_6210699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210699 prefixEnd_6210699 := by exact prefixLift 6210699
  have htrace : WordTrace (prefixWord ++ tailWord_6210699) baseStart_6210699 baseEnd_6210699 := by
    simpa [prefixWord, tailWord_6210699, baseEnd_6210699] using wordTrace_append hprefix tailTrace_6210699
  have hstable : (prefixWord ++ tailWord_6210699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210699).length < 2 ^ (prefixWord ++ tailWord_6210699).sum := by decide
  have hdescent : baseEnd_6210699 < baseStart_6210699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210716 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_6210716 : Nat := 118140960795 + 6210716 * 2 ^ 59
def prefixEnd_6210716 : Nat := 4983230072969 + 3 ^ 40 * 6210716 * 2
def baseEnd_6210716 : Nat := 3189082516569427778787443

theorem tailTrace_6210716 : CollatzResearch.WordTrace tailWord_6210716 prefixEnd_6210716 3189082516569427778787443 := by
  unfold tailWord_6210716
  simp only [CollatzResearch.WordTrace]
  refine ⟨113261711083822056345402001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151015614778429408460536001 113261711083822056345402001)
  ·
    refine ⟨84946283312866542259051501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113261711083822056345402001 84946283312866542259051501)
    ·
      refine ⟨31854856242324953347144313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84946283312866542259051501 31854856242324953347144313)
      ·
        refine ⟨23891142181743715010358235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31854856242324953347144313 23891142181743715010358235)
        ·
          refine ⟨35836713272615572515537353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23891142181743715010358235 35836713272615572515537353)
          ·
            refine ⟨26877534954461679386653015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35836713272615572515537353 26877534954461679386653015)
            ·
              refine ⟨40316302431692519079979523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26877534954461679386653015 40316302431692519079979523)
              ·
                refine ⟨60474453647538778619969285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40316302431692519079979523 60474453647538778619969285)
                ·
                  refine ⟨11338960058913520991244241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60474453647538778619969285 11338960058913520991244241)
                  ·
                    refine ⟨8504220044185140743433181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11338960058913520991244241 8504220044185140743433181)
                    ·
                      refine ⟨3189082516569427778787443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8504220044185140743433181 3189082516569427778787443)
                      ·
                        rfl

theorem cell23_6210716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_6210716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210716 prefixEnd_6210716 := by exact prefixLift 6210716
  have htrace : WordTrace (prefixWord ++ tailWord_6210716) baseStart_6210716 baseEnd_6210716 := by
    simpa [prefixWord, tailWord_6210716, baseEnd_6210716] using wordTrace_append hprefix tailTrace_6210716
  have hstable : (prefixWord ++ tailWord_6210716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210716).length < 2 ^ (prefixWord ++ tailWord_6210716).sum := by decide
  have hdescent : baseEnd_6210716 < baseStart_6210716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210746 : List Nat := [3, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3]
def baseStart_6210746 : Nat := 118140960795 + 6210746 * 2 ^ 59
def prefixEnd_6210746 : Nat := 4983230072969 + 3 ^ 40 * 6210746 * 2
def baseEnd_6210746 : Nat := 3189097920989062661412305

theorem tailTrace_6210746 : CollatzResearch.WordTrace tailWord_6210746 prefixEnd_6210746 3189097920989062661412305 := by
  unfold tailWord_6210746
  simp only [CollatzResearch.WordTrace]
  refine ⟨56631129089383856953599023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151016344238356951876264061 56631129089383856953599023)
  ·
    refine ⟨84946693634075785430398535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56631129089383856953599023 84946693634075785430398535)
    ·
      refine ⟨127420040451113678145597803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84946693634075785430398535 127420040451113678145597803)
      ·
        refine ⟨191130060676670517218396705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127420040451113678145597803 191130060676670517218396705)
        ·
          refine ⟨143347545507502887913797529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191130060676670517218396705 143347545507502887913797529)
          ·
            refine ⟨107510659130627165935348147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143347545507502887913797529 107510659130627165935348147)
            ·
              refine ⟨161265988695940748903022221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 107510659130627165935348147 161265988695940748903022221)
              ·
                refine ⟨60474745760977780838633333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 161265988695940748903022221 60474745760977780838633333)
                ·
                  refine ⟨5669507415091666953621875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60474745760977780838633333 5669507415091666953621875)
                  ·
                    refine ⟨8504261122637500430432813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5669507415091666953621875 8504261122637500430432813)
                    ·
                      refine ⟨3189097920989062661412305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8504261122637500430432813 3189097920989062661412305)
                      ·
                        rfl

theorem cell23_6210746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3].length) (baseStart_6210746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210746 prefixEnd_6210746 := by exact prefixLift 6210746
  have htrace : WordTrace (prefixWord ++ tailWord_6210746) baseStart_6210746 baseEnd_6210746 := by
    simpa [prefixWord, tailWord_6210746, baseEnd_6210746] using wordTrace_append hprefix tailTrace_6210746
  have hstable : (prefixWord ++ tailWord_6210746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210746).length < 2 ^ (prefixWord ++ tailWord_6210746).sum := by decide
  have hdescent : baseEnd_6210746 < baseStart_6210746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210796 : List Nat := [2, 2, 1, 1, 2, 5, 2, 1, 1, 6]
def baseStart_6210796 : Nat := 118140960795 + 6210796 * 2 ^ 59
def prefixEnd_6210796 : Nat := 4983230072969 + 3 ^ 40 * 6210796 * 2
def baseEnd_6210796 : Nat := 1063041198340595821929025

theorem tailTrace_6210796 : CollatzResearch.WordTrace tailWord_6210796 prefixEnd_6210796 1063041198340595821929025 := by
  unfold tailWord_6210796
  simp only [CollatzResearch.WordTrace]
  refine ⟨113263170003677143176858121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151017560004902857569144161 113263170003677143176858121)
  ·
    refine ⟨84947377502757857382643591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113263170003677143176858121 84947377502757857382643591)
    ·
      refine ⟨127421066254136786073965387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84947377502757857382643591 127421066254136786073965387)
      ·
        refine ⟨191131599381205179110948081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 127421066254136786073965387 191131599381205179110948081)
        ·
          refine ⟨143348699535903884333211061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 191131599381205179110948081 143348699535903884333211061)
          ·
            refine ⟨13438940581490989156238537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 143348699535903884333211061 13438940581490989156238537)
            ·
              refine ⟨10079205436118241867178903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13438940581490989156238537 10079205436118241867178903)
              ·
                refine ⟨15118808154177362800768355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10079205436118241867178903 15118808154177362800768355)
                ·
                  refine ⟨22678212231266044201152533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15118808154177362800768355 22678212231266044201152533)
                  ·
                    refine ⟨1063041198340595821929025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22678212231266044201152533 1063041198340595821929025)
                    ·
                      rfl

theorem cell23_6210796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_6210796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210796 prefixEnd_6210796 := by exact prefixLift 6210796
  have htrace : WordTrace (prefixWord ++ tailWord_6210796) baseStart_6210796 baseEnd_6210796 := by
    simpa [prefixWord, tailWord_6210796, baseEnd_6210796] using wordTrace_append hprefix tailTrace_6210796
  have hstable : (prefixWord ++ tailWord_6210796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210796).length < 2 ^ (prefixWord ++ tailWord_6210796).sum := by decide
  have hdescent : baseEnd_6210796 < baseStart_6210796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210803 : List Nat := [1, 1, 1, 2, 2, 5, 1, 1, 5, 2, 2]
def baseStart_6210803 : Nat := 118140960795 + 6210803 * 2 ^ 59
def prefixEnd_6210803 : Nat := 4983230072969 + 3 ^ 40 * 6210803 * 2
def baseEnd_6210803 : Nat := 3189127189386368938399543

theorem tailTrace_6210803 : CollatzResearch.WordTrace tailWord_6210803 prefixEnd_6210803 3189127189386368938399543 := by
  unfold tailWord_6210803
  simp only [CollatzResearch.WordTrace]
  refine ⟨226526595318328926549221063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151017730212219284366147375 226526595318328926549221063)
  ·
    refine ⟨339789892977493389823831595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226526595318328926549221063 339789892977493389823831595)
    ·
      refine ⟨509684839466240084735747393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 339789892977493389823831595 509684839466240084735747393)
      ·
        refine ⟨382263629599680063551810545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 509684839466240084735747393 382263629599680063551810545)
        ·
          refine ⟨286697722199760047663857909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 382263629599680063551810545 286697722199760047663857909)
          ·
            refine ⟨26877911456227504468486679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 286697722199760047663857909 26877911456227504468486679)
            ·
              refine ⟨40316867184341256702730019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26877911456227504468486679 40316867184341256702730019)
              ·
                refine ⟨60475300776511885054095029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40316867184341256702730019 60475300776511885054095029)
                ·
                  refine ⟨5669559447797989223821409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60475300776511885054095029 5669559447797989223821409)
                  ·
                    refine ⟨4252169585848491917866057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5669559447797989223821409 4252169585848491917866057)
                    ·
                      refine ⟨3189127189386368938399543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4252169585848491917866057 3189127189386368938399543)
                      ·
                        rfl

theorem cell23_6210803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 2, 2].length) (baseStart_6210803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210803 prefixEnd_6210803 := by exact prefixLift 6210803
  have htrace : WordTrace (prefixWord ++ tailWord_6210803) baseStart_6210803 baseEnd_6210803 := by
    simpa [prefixWord, tailWord_6210803, baseEnd_6210803] using wordTrace_append hprefix tailTrace_6210803
  have hstable : (prefixWord ++ tailWord_6210803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210803).length < 2 ^ (prefixWord ++ tailWord_6210803).sum := by decide
  have hdescent : baseEnd_6210803 < baseStart_6210803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210820 : List Nat := [2, 3, 2, 2, 2, 1, 4, 1, 1, 1, 4]
def baseStart_6210820 : Nat := 118140960795 + 6210820 * 2 ^ 59
def prefixEnd_6210820 : Nat := 4983230072969 + 3 ^ 40 * 6210820 * 2
def baseEnd_6210820 : Nat := 3189135918557495371886965

theorem tailTrace_6210820 : CollatzResearch.WordTrace tailWord_6210820 prefixEnd_6210820 3189135918557495371886965 := by
  unfold tailWord_6210820
  simp only [CollatzResearch.WordTrace]
  refine ⟨113263607679633669226294957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151018143572844892301726609 113263607679633669226294957)
  ·
    refine ⟨42473852879862625959860609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 113263607679633669226294957 42473852879862625959860609)
    ·
      refine ⟨31855389659896969469895457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42473852879862625959860609 31855389659896969469895457)
      ·
        refine ⟨23891542244922727102421593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31855389659896969469895457 23891542244922727102421593)
        ·
          refine ⟨17918656683692045326816195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23891542244922727102421593 17918656683692045326816195)
          ·
            refine ⟨26877985025538067990224293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17918656683692045326816195 26877985025538067990224293)
            ·
              refine ⟨5039622192288387748167055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26877985025538067990224293 5039622192288387748167055)
              ·
                refine ⟨7559433288432581622250583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5039622192288387748167055 7559433288432581622250583)
                ·
                  refine ⟨11339149932648872433375875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7559433288432581622250583 11339149932648872433375875)
                  ·
                    refine ⟨17008724898973308650063813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11339149932648872433375875 17008724898973308650063813)
                    ·
                      refine ⟨3189135918557495371886965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17008724898973308650063813 3189135918557495371886965)
                      ·
                        rfl

theorem cell23_6210820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_6210820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210820 prefixEnd_6210820 := by exact prefixLift 6210820
  have htrace : WordTrace (prefixWord ++ tailWord_6210820) baseStart_6210820 baseEnd_6210820 := by
    simpa [prefixWord, tailWord_6210820, baseEnd_6210820] using wordTrace_append hprefix tailTrace_6210820
  have hstable : (prefixWord ++ tailWord_6210820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210820).length < 2 ^ (prefixWord ++ tailWord_6210820).sum := by decide
  have hdescent : baseEnd_6210820 < baseStart_6210820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210830 : List Nat := [4, 1, 1, 2, 1, 5, 1, 2, 2, 4]
def baseStart_6210830 : Nat := 118140960795 + 6210830 * 2 ^ 59
def prefixEnd_6210830 : Nat := 4983230072969 + 3 ^ 40 * 6210830 * 2
def baseEnd_6210830 : Nat := 1063047017788013444253973

theorem tailTrace_6210830 : CollatzResearch.WordTrace tailWord_6210830 prefixEnd_6210830 1063047017788013444253973 := by
  unfold tailWord_6210830
  simp only [CollatzResearch.WordTrace]
  refine ⟨28315947511153888770056743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 151018386726154073440302629 28315947511153888770056743)
  ·
    refine ⟨42473921266730833155085115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28315947511153888770056743 42473921266730833155085115)
    ·
      refine ⟨63710881900096249732627673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42473921266730833155085115 63710881900096249732627673)
      ·
        refine ⟨47783161425072187299470755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63710881900096249732627673 47783161425072187299470755)
        ·
          refine ⟨71674742137608280949206133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47783161425072187299470755 71674742137608280949206133)
          ·
            refine ⟨6719507075400776338988075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71674742137608280949206133 6719507075400776338988075)
            ·
              refine ⟨10079260613101164508482113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6719507075400776338988075 10079260613101164508482113)
              ·
                refine ⟨7559445459825873381361585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10079260613101164508482113 7559445459825873381361585)
                ·
                  refine ⟨5669584094869405036021189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7559445459825873381361585 5669584094869405036021189)
                  ·
                    refine ⟨1063047017788013444253973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5669584094869405036021189 1063047017788013444253973)
                    ·
                      rfl

theorem cell23_6210830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_6210830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210830 prefixEnd_6210830 := by exact prefixLift 6210830
  have htrace : WordTrace (prefixWord ++ tailWord_6210830) baseStart_6210830 baseEnd_6210830 := by
    simpa [prefixWord, tailWord_6210830, baseEnd_6210830] using wordTrace_append hprefix tailTrace_6210830
  have hstable : (prefixWord ++ tailWord_6210830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210830).length < 2 ^ (prefixWord ++ tailWord_6210830).sum := by decide
  have hdescent : baseEnd_6210830 < baseStart_6210830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210850 : List Nat := [3, 3, 1, 1, 4, 2, 1, 1, 1, 2, 4]
def baseStart_6210850 : Nat := 118140960795 + 6210850 * 2 ^ 59
def prefixEnd_6210850 : Nat := 4983230072969 + 3 ^ 40 * 6210850 * 2
def baseEnd_6210850 : Nat := 3189151322977130254511827

theorem tailTrace_6210850 : CollatzResearch.WordTrace tailWord_6210850 prefixEnd_6210850 3189151322977130254511827 := by
  unfold tailWord_6210850
  simp only [CollatzResearch.WordTrace]
  refine ⟨56632077387289663394045501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151018873032772435717454669 56632077387289663394045501)
  ·
    refine ⟨21237029020233623772767063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56632077387289663394045501 21237029020233623772767063)
    ·
      refine ⟨31855543530350435659150595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21237029020233623772767063 31855543530350435659150595)
      ·
        refine ⟨47783315295525653488725893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31855543530350435659150595 47783315295525653488725893)
        ·
          refine ⟨8959371617911060029136105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47783315295525653488725893 8959371617911060029136105)
          ·
            refine ⟨6719528713433295021852079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8959371617911060029136105 6719528713433295021852079)
            ·
              refine ⟨10079293070149942532778119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6719528713433295021852079 10079293070149942532778119)
              ·
                refine ⟨15118939605224913799167179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10079293070149942532778119 15118939605224913799167179)
                ·
                  refine ⟨22678409407837370698750769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15118939605224913799167179 22678409407837370698750769)
                  ·
                    refine ⟨17008807055878028024063077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22678409407837370698750769 17008807055878028024063077)
                    ·
                      refine ⟨3189151322977130254511827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17008807055878028024063077 3189151322977130254511827)
                      ·
                        rfl

theorem cell23_6210850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_6210850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210850 prefixEnd_6210850 := by exact prefixLift 6210850
  have htrace : WordTrace (prefixWord ++ tailWord_6210850) baseStart_6210850 baseEnd_6210850 := by
    simpa [prefixWord, tailWord_6210850, baseEnd_6210850] using wordTrace_append hprefix tailTrace_6210850
  have hstable : (prefixWord ++ tailWord_6210850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210850).length < 2 ^ (prefixWord ++ tailWord_6210850).sum := by decide
  have hdescent : baseEnd_6210850 < baseStart_6210850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210853 : List Nat := [1, 3, 1, 2, 4, 1, 3, 1, 1, 3, 3]
def baseStart_6210853 : Nat := 118140960795 + 6210853 * 2 ^ 59
def prefixEnd_6210853 : Nat := 4983230072969 + 3 ^ 40 * 6210853 * 2
def baseEnd_6210853 : Nat := 3189152863419093742774313

theorem tailTrace_6210853 : CollatzResearch.WordTrace tailWord_6210853 prefixEnd_6210853 3189152863419093742774313 := by
  unfold tailWord_6210853
  simp only [CollatzResearch.WordTrace]
  refine ⟨226528418968147785088541213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151018945978765190059027475 226528418968147785088541213)
  ·
    refine ⟨84948157113055419408202955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226528418968147785088541213 84948157113055419408202955)
    ·
      refine ⟨127422235669583129112304433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84948157113055419408202955 127422235669583129112304433)
      ·
        refine ⟨95566676752187346834228325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127422235669583129112304433 95566676752187346834228325)
        ·
          refine ⟨17918751891035127531417811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95566676752187346834228325 17918751891035127531417811)
          ·
            refine ⟨26878127836552691297126717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17918751891035127531417811 26878127836552691297126717)
            ·
              refine ⟨10079297938707259236422519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26878127836552691297126717 10079297938707259236422519)
              ·
                refine ⟨15118946908060888854633779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10079297938707259236422519 15118946908060888854633779)
                ·
                  refine ⟨22678420362091333281950669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15118946908060888854633779 22678420362091333281950669)
                  ·
                    refine ⟨8504407635784249980731501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22678420362091333281950669 8504407635784249980731501)
                    ·
                      refine ⟨3189152863419093742774313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8504407635784249980731501 3189152863419093742774313)
                      ·
                        rfl

theorem cell23_6210853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_6210853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210853 prefixEnd_6210853 := by exact prefixLift 6210853
  have htrace : WordTrace (prefixWord ++ tailWord_6210853) baseStart_6210853 baseEnd_6210853 := by
    simpa [prefixWord, tailWord_6210853, baseEnd_6210853] using wordTrace_append hprefix tailTrace_6210853
  have hstable : (prefixWord ++ tailWord_6210853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210853).length < 2 ^ (prefixWord ++ tailWord_6210853).sum := by decide
  have hdescent : baseEnd_6210853 < baseStart_6210853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210866 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_6210866 : Nat := 118140960795 + 6210866 * 2 ^ 59
def prefixEnd_6210866 : Nat := 4983230072969 + 3 ^ 40 * 6210866 * 2
def baseEnd_6210866 : Nat := 3189159538667602191911753

theorem tailTrace_6210866 : CollatzResearch.WordTrace tailWord_6210866 prefixEnd_6210866 3189159538667602191911753 := by
  unfold tailWord_6210866
  simp only [CollatzResearch.WordTrace]
  refine ⟨56632223279275172077191113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151019262078067125539176301 56632223279275172077191113)
  ·
    refine ⟨42474167459456379057893335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56632223279275172077191113 42474167459456379057893335)
    ·
      refine ⟨63711251189184568586840003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42474167459456379057893335 63711251189184568586840003)
      ·
        refine ⟨95566876783776852880260005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63711251189184568586840003 95566876783776852880260005)
        ·
          refine ⟨17918789396958159915048751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95566876783776852880260005 17918789396958159915048751)
          ·
            refine ⟨26878184095437239872573127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17918789396958159915048751 26878184095437239872573127)
            ·
              refine ⟨40317276143155859808859691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26878184095437239872573127 40317276143155859808859691)
              ·
                refine ⟨60475914214733789713289537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40317276143155859808859691 60475914214733789713289537)
                ·
                  refine ⟨45356935661050342284967153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60475914214733789713289537 45356935661050342284967153)
                  ·
                    refine ⟨34017701745787756713725365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45356935661050342284967153 34017701745787756713725365)
                    ·
                      refine ⟨3189159538667602191911753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34017701745787756713725365 3189159538667602191911753)
                      ·
                        rfl

theorem cell23_6210866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_6210866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210866 prefixEnd_6210866 := by exact prefixLift 6210866
  have htrace : WordTrace (prefixWord ++ tailWord_6210866) baseStart_6210866 baseEnd_6210866 := by
    simpa [prefixWord, tailWord_6210866, baseEnd_6210866] using wordTrace_append hprefix tailTrace_6210866
  have hstable : (prefixWord ++ tailWord_6210866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210866).length < 2 ^ (prefixWord ++ tailWord_6210866).sum := by decide
  have hdescent : baseEnd_6210866 < baseStart_6210866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210896 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 3]
def baseStart_6210896 : Nat := 118140960795 + 6210896 * 2 ^ 59
def prefixEnd_6210896 : Nat := 4983230072969 + 3 ^ 40 * 6210896 * 2
def baseEnd_6210896 : Nat := 3189174943087237074536615

theorem tailTrace_6210896 : CollatzResearch.WordTrace tailWord_6210896 prefixEnd_6210896 3189174943087237074536615 := by
  unfold tailWord_6210896
  simp only [CollatzResearch.WordTrace]
  refine ⟨113264993653496001716178271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151019991537994668954904361 113264993653496001716178271)
  ·
    refine ⟨169897490480244002574267407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 113264993653496001716178271 169897490480244002574267407)
    ·
      refine ⟨254846235720366003861401111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 169897490480244002574267407 254846235720366003861401111)
      ·
        refine ⟨382269353580549005792101667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254846235720366003861401111 382269353580549005792101667)
        ·
          refine ⟨573404030370823508688152501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382269353580549005792101667 573404030370823508688152501)
          ·
            refine ⟨53756627847264703939514297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 573404030370823508688152501 53756627847264703939514297)
            ·
              refine ⟨40317470885448527954635723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53756627847264703939514297 40317470885448527954635723)
              ·
                refine ⟨60476206328172791931953585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40317470885448527954635723 60476206328172791931953585)
                ·
                  refine ⟨45357154746129593948965189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 60476206328172791931953585 45357154746129593948965189)
                  ·
                    refine ⟨8504466514899298865430973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 45357154746129593948965189 8504466514899298865430973)
                    ·
                      refine ⟨3189174943087237074536615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8504466514899298865430973 3189174943087237074536615)
                      ·
                        rfl

theorem cell23_6210896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 3].length) (baseStart_6210896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210896 prefixEnd_6210896 := by exact prefixLift 6210896
  have htrace : WordTrace (prefixWord ++ tailWord_6210896) baseStart_6210896 baseEnd_6210896 := by
    simpa [prefixWord, tailWord_6210896, baseEnd_6210896] using wordTrace_append hprefix tailTrace_6210896
  have hstable : (prefixWord ++ tailWord_6210896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210896).length < 2 ^ (prefixWord ++ tailWord_6210896).sum := by decide
  have hdescent : baseEnd_6210896 < baseStart_6210896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210906 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4]
def baseStart_6210906 : Nat := 118140960795 + 6210906 * 2 ^ 59
def prefixEnd_6210906 : Nat := 4983230072969 + 3 ^ 40 * 6210906 * 2
def baseEnd_6210906 : Nat := 3189180077893782035411569

theorem tailTrace_6210906 : CollatzResearch.WordTrace tailWord_6210906 prefixEnd_6210906 3189180077893782035411569 := by
  unfold tailWord_6210906
  simp only [CollatzResearch.WordTrace]
  refine ⟨56632588009238943785055143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151020234691303850093480381 56632588009238943785055143)
  ·
    refine ⟨84948882013858415677582715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56632588009238943785055143 84948882013858415677582715)
    ·
      refine ⟨127423323020787623516374073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84948882013858415677582715 127423323020787623516374073)
      ·
        refine ⟨95567492265590717637280555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127423323020787623516374073 95567492265590717637280555)
        ·
          refine ⟨143351238398386076455920833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95567492265590717637280555 143351238398386076455920833)
          ·
            refine ⟨107513428798789557341940625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 143351238398386076455920833 107513428798789557341940625)
            ·
              refine ⟨80635071599092168006455469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 107513428798789557341940625 80635071599092168006455469)
              ·
                refine ⟨30238151849659563002420801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80635071599092168006455469 30238151849659563002420801)
                ·
                  refine ⟨22678613887244672251815601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30238151849659563002420801 22678613887244672251815601)
                  ·
                    refine ⟨17008960415433504188861701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22678613887244672251815601 17008960415433504188861701)
                    ·
                      refine ⟨3189180077893782035411569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17008960415433504188861701 3189180077893782035411569)
                      ·
                        rfl

theorem cell23_6210906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_6210906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210906 prefixEnd_6210906 := by exact prefixLift 6210906
  have htrace : WordTrace (prefixWord ++ tailWord_6210906) baseStart_6210906 baseEnd_6210906 := by
    simpa [prefixWord, tailWord_6210906, baseEnd_6210906] using wordTrace_append hprefix tailTrace_6210906
  have hstable : (prefixWord ++ tailWord_6210906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210906).length < 2 ^ (prefixWord ++ tailWord_6210906).sum := by decide
  have hdescent : baseEnd_6210906 < baseStart_6210906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210956 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 1, 2, 5]
def baseStart_6210956 : Nat := 118140960795 + 6210956 * 2 ^ 59
def prefixEnd_6210956 : Nat := 4983230072969 + 3 ^ 40 * 6210956 * 2
def baseEnd_6210956 : Nat := 3189205751926506839786339

theorem tailTrace_6210956 : CollatzResearch.WordTrace tailWord_6210956 prefixEnd_6210956 3189205751926506839786339 := by
  unfold tailWord_6210956
  simp only [CollatzResearch.WordTrace]
  refine ⟨113266087843387316839770361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 151021450457849755786360481 113266087843387316839770361)
  ·
    refine ⟨84949565882540487629827771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 113266087843387316839770361 84949565882540487629827771)
    ·
      refine ⟨127424348823810731444741657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84949565882540487629827771 127424348823810731444741657)
      ·
        refine ⟨95568261617858048583556243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 127424348823810731444741657 95568261617858048583556243)
        ·
          refine ⟨143352392426787072875334365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 95568261617858048583556243 143352392426787072875334365)
          ·
            refine ⟨53757147160045152328250387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 143352392426787072875334365 53757147160045152328250387)
            ·
              refine ⟨80635720740067728492375581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53757147160045152328250387 80635720740067728492375581)
              ·
                refine ⟨30238395277525398184640843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 80635720740067728492375581 30238395277525398184640843)
                ·
                  refine ⟨45357592916288097276961265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30238395277525398184640843 45357592916288097276961265)
                  ·
                    refine ⟨34018194687216072957720949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45357592916288097276961265 34018194687216072957720949)
                    ·
                      refine ⟨3189205751926506839786339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34018194687216072957720949 3189205751926506839786339)
                      ·
                        rfl

theorem cell23_6210956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_6210956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210956 prefixEnd_6210956 := by exact prefixLift 6210956
  have htrace : WordTrace (prefixWord ++ tailWord_6210956) baseStart_6210956 baseEnd_6210956 := by
    simpa [prefixWord, tailWord_6210956, baseEnd_6210956] using wordTrace_append hprefix tailTrace_6210956
  have hstable : (prefixWord ++ tailWord_6210956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210956).length < 2 ^ (prefixWord ++ tailWord_6210956).sum := by decide
  have hdescent : baseEnd_6210956 < baseStart_6210956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210983 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_6210983 : Nat := 118140960795 + 6210983 * 2 ^ 59
def prefixEnd_6210983 : Nat := 4983230072969 + 3 ^ 40 * 6210983 * 2
def baseEnd_6210983 : Nat := 3189219615904178234148715

theorem tailTrace_6210983 : CollatzResearch.WordTrace tailWord_6210983 prefixEnd_6210983 3189219615904178234148715 := by
  unfold tailWord_6210983
  simp only [CollatzResearch.WordTrace]
  refine ⟨226533160457676817290773603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151022106971784544860515735 226533160457676817290773603)
  ·
    refine ⟨339799740686515225936160405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226533160457676817290773603 339799740686515225936160405)
    ·
      refine ⟨15928112844680401215757519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 339799740686515225936160405 15928112844680401215757519)
      ·
        refine ⟨23892169267020601823636279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15928112844680401215757519 23892169267020601823636279)
        ·
          refine ⟨35838253900530902735454419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23892169267020601823636279 35838253900530902735454419)
          ·
            refine ⟨53757380850796354103181629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35838253900530902735454419 53757380850796354103181629)
            ·
              refine ⟨20159017819048632788693111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53757380850796354103181629 20159017819048632788693111)
              ·
                refine ⟨30238526728572949183039667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20159017819048632788693111 30238526728572949183039667)
                ·
                  refine ⟨45357790092859423774559501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30238526728572949183039667 45357790092859423774559501)
                  ·
                    refine ⟨17009171284822283915459813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45357790092859423774559501 17009171284822283915459813)
                    ·
                      refine ⟨3189219615904178234148715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17009171284822283915459813 3189219615904178234148715)
                      ·
                        rfl

theorem cell23_6210983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_6210983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210983 prefixEnd_6210983 := by exact prefixLift 6210983
  have htrace : WordTrace (prefixWord ++ tailWord_6210983) baseStart_6210983 baseEnd_6210983 := by
    simpa [prefixWord, tailWord_6210983, baseEnd_6210983] using wordTrace_append hprefix tailTrace_6210983
  have hstable : (prefixWord ++ tailWord_6210983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210983).length < 2 ^ (prefixWord ++ tailWord_6210983).sum := by decide
  have hdescent : baseEnd_6210983 < baseStart_6210983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6210993 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 5, 4]
def baseStart_6210993 : Nat := 118140960795 + 6210993 * 2 ^ 59
def prefixEnd_6210993 : Nat := 4983230072969 + 3 ^ 40 * 6210993 * 2
def baseEnd_6210993 : Nat := 1063074916903574398341223

theorem tailTrace_6210993 : CollatzResearch.WordTrace tailWord_6210993 prefixEnd_6210993 1063074916903574398341223 := by
  unfold tailWord_6210993
  simp only [CollatzResearch.WordTrace]
  refine ⟨226533525187640588998637633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151022350125093725999091755 226533525187640588998637633)
  ·
    refine ⟨169900143890730441748978225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 226533525187640588998637633 169900143890730441748978225)
    ·
      refine ⟨127425107918047831311733669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 169900143890730441748978225 127425107918047831311733669)
      ·
        refine ⟨23892207734633968370950063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 127425107918047831311733669 23892207734633968370950063)
        ·
          refine ⟨35838311601950952556425095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23892207734633968370950063 35838311601950952556425095)
          ·
            refine ⟨53757467402926428834637643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35838311601950952556425095 53757467402926428834637643)
            ·
              refine ⟨80636201104389643251956465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53757467402926428834637643 80636201104389643251956465)
              ·
                refine ⟨60477150828292232438967349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 80636201104389643251956465 60477150828292232438967349)
                ·
                  refine ⟨5669732890152396791153189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60477150828292232438967349 5669732890152396791153189)
                  ·
                    refine ⟨1063074916903574398341223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5669732890152396791153189 1063074916903574398341223)
                    ·
                      rfl

theorem cell23_6210993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 4].length) (baseStart_6210993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6210993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6210993 prefixEnd_6210993 := by exact prefixLift 6210993
  have htrace : WordTrace (prefixWord ++ tailWord_6210993) baseStart_6210993 baseEnd_6210993 := by
    simpa [prefixWord, tailWord_6210993, baseEnd_6210993] using wordTrace_append hprefix tailTrace_6210993
  have hstable : (prefixWord ++ tailWord_6210993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6210993).length < 2 ^ (prefixWord ++ tailWord_6210993).sum := by decide
  have hdescent : baseEnd_6210993 < baseStart_6210993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6210993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211061 : List Nat := [1, 3, 5, 1, 1, 2, 3, 2, 1, 4]
def baseStart_6211061 : Nat := 118140960795 + 6211061 * 2 ^ 59
def prefixEnd_6211061 : Nat := 4983230072969 + 3 ^ 40 * 6211061 * 2
def baseEnd_6211061 : Nat := 1063086555798409642991119

theorem tailTrace_6211061 : CollatzResearch.WordTrace tailWord_6211061 prefixEnd_6211061 1063086555798409642991119 := by
  unfold tailWord_6211061
  simp only [CollatzResearch.WordTrace]
  refine ⟨226536005351394236612113037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151024003567596157741408691 226536005351394236612113037)
  ·
    refine ⟨84951002006772838729542389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 226536005351394236612113037 84951002006772838729542389)
    ·
      refine ⟨7964156438134953630894599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84951002006772838729542389 7964156438134953630894599)
      ·
        refine ⟨11946234657202430446341899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7964156438134953630894599 11946234657202430446341899)
        ·
          refine ⟨17919351985803645669512849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11946234657202430446341899 17919351985803645669512849)
          ·
            refine ⟨13439513989352734252134637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17919351985803645669512849 13439513989352734252134637)
            ·
              refine ⟨5039817746007275344550489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13439513989352734252134637 5039817746007275344550489)
              ·
                refine ⟨3779863309505456508412867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5039817746007275344550489 3779863309505456508412867)
                ·
                  refine ⟨5669794964258184762619301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3779863309505456508412867 5669794964258184762619301)
                  ·
                    refine ⟨1063086555798409642991119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5669794964258184762619301 1063086555798409642991119)
                    ·
                      rfl

theorem cell23_6211061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_6211061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211061 prefixEnd_6211061 := by exact prefixLift 6211061
  have htrace : WordTrace (prefixWord ++ tailWord_6211061) baseStart_6211061 baseEnd_6211061 := by
    simpa [prefixWord, tailWord_6211061, baseEnd_6211061] using wordTrace_append hprefix tailTrace_6211061
  have hstable : (prefixWord ++ tailWord_6211061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211061).length < 2 ^ (prefixWord ++ tailWord_6211061).sum := by decide
  have hdescent : baseEnd_6211061 < baseStart_6211061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211074 : List Nat := [3, 4, 1, 2, 1, 3, 2, 1, 6]
def baseStart_6211074 : Nat := 118140960795 + 6211074 * 2 ^ 59
def prefixEnd_6211074 : Nat := 4983230072969 + 3 ^ 40 * 6211074 * 2
def baseEnd_6211074 : Nat := 354362926960415264234533

theorem tailTrace_6211074 : CollatzResearch.WordTrace tailWord_6211074 prefixEnd_6211074 354362926960415264234533 := by
  unfold tailWord_6211074
  simp only [CollatzResearch.WordTrace]
  refine ⟨56634119875086784958084069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 151024319666898093221557517 56634119875086784958084069)
  ·
    refine ⟨10618897476578772179640763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56634119875086784958084069 10618897476578772179640763)
    ·
      refine ⟨15928346214868158269461145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10618897476578772179640763 15928346214868158269461145)
      ·
        refine ⟨11946259661151118702095859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15928346214868158269461145 11946259661151118702095859)
        ·
          refine ⟨17919389491726678053143789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11946259661151118702095859 17919389491726678053143789)
          ·
            refine ⟨6719771059397504269928921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17919389491726678053143789 6719771059397504269928921)
            ·
              refine ⟨5039828294548128202446691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6719771059397504269928921 5039828294548128202446691)
              ·
                refine ⟨7559742441822192303670037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5039828294548128202446691 7559742441822192303670037)
                ·
                  refine ⟨354362926960415264234533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7559742441822192303670037 354362926960415264234533)
                  ·
                    rfl

theorem cell23_6211074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_6211074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211074 prefixEnd_6211074 := by exact prefixLift 6211074
  have htrace : WordTrace (prefixWord ++ tailWord_6211074) baseStart_6211074 baseEnd_6211074 := by
    simpa [prefixWord, tailWord_6211074, baseEnd_6211074] using wordTrace_append hprefix tailTrace_6211074
  have hstable : (prefixWord ++ tailWord_6211074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211074).length < 2 ^ (prefixWord ++ tailWord_6211074).sum := by decide
  have hdescent : baseEnd_6211074 < baseStart_6211074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6211103 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 4]
def baseStart_6211103 : Nat := 118140960795 + 6211103 * 2 ^ 59
def prefixEnd_6211103 : Nat := 4983230072969 + 3 ^ 40 * 6211103 * 2
def baseEnd_6211103 : Nat := 3189281233582717764648163

theorem tailTrace_6211103 : CollatzResearch.WordTrace tailWord_6211103 prefixEnd_6211103 3189281233582717764648163 := by
  unfold tailWord_6211103
  simp only [CollatzResearch.WordTrace]
  refine ⟨226537537217242077785141963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 151025024811494718523427975 226537537217242077785141963)
  ·
    refine ⟨339806305825863116677712945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 226537537217242077785141963 339806305825863116677712945)
    ·
      refine ⟨254854729369397337508284709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 339806305825863116677712945 254854729369397337508284709)
      ·
        refine ⟨47785261756762000782803383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 254854729369397337508284709 47785261756762000782803383)
        ·
          refine ⟨71677892635143001174205075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47785261756762000782803383 71677892635143001174205075)
          ·
            refine ⟨107516838952714501761307613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71677892635143001174205075 107516838952714501761307613)
            ·
              refine ⟨40318814607267938160490355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 107516838952714501761307613 40318814607267938160490355)
              ·
                refine ⟨60478221910901907240735533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40318814607267938160490355 60478221910901907240735533)
                ·
                  refine ⟨22679333216588215215275825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 60478221910901907240735533 22679333216588215215275825)
                  ·
                    refine ⟨17009499912441161411456869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22679333216588215215275825 17009499912441161411456869)
                    ·
                      refine ⟨3189281233582717764648163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17009499912441161411456869 3189281233582717764648163)
                      ·
                        rfl

theorem cell23_6211103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_6211103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6211103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6211103 prefixEnd_6211103 := by exact prefixLift 6211103
  have htrace : WordTrace (prefixWord ++ tailWord_6211103) baseStart_6211103 baseEnd_6211103 := by
    simpa [prefixWord, tailWord_6211103, baseEnd_6211103] using wordTrace_append hprefix tailTrace_6211103
  have hstable : (prefixWord ++ tailWord_6211103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6211103).length < 2 ^ (prefixWord ++ tailWord_6211103).sum := by decide
  have hdescent : baseEnd_6211103 < baseStart_6211103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6211103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
