import V185TrunkScan23Chunk0821

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4863079 : List Nat := [1, 1, 5, 1, 1, 3, 3, 2, 2, 1, 3]
def baseStart_4863079 : Nat := 118140960795 + 4863079 * 2 ^ 59
def prefixEnd_4863079 : Nat := 4983230072969 + 3 ^ 40 * 4863079 * 2
def baseEnd_4863079 : Nat := 2497096987786283914747613

theorem tailTrace_4863079 : CollatzResearch.WordTrace tailWord_4863079 prefixEnd_4863079 2497096987786283914747613 := by
  unfold tailWord_4863079
  simp only [CollatzResearch.WordTrace]
  refine ⟨177371062748902805615024291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118247375165935203743349527 177371062748902805615024291)
  ·
    refine ⟨266056594123354208422536437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177371062748902805615024291 266056594123354208422536437)
    ·
      refine ⟨24942805699064457039612791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 266056594123354208422536437 24942805699064457039612791)
      ·
        refine ⟨37414208548596685559419187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24942805699064457039612791 37414208548596685559419187)
        ·
          refine ⟨56121312822895028339128781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37414208548596685559419187 56121312822895028339128781)
          ·
            refine ⟨21045492308585635627173293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56121312822895028339128781 21045492308585635627173293)
            ·
              refine ⟨7892059615719613360189985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21045492308585635627173293 7892059615719613360189985)
              ·
                refine ⟨5919044711789710020142489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7892059615719613360189985 5919044711789710020142489)
                ·
                  refine ⟨4439283533842282515106867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5919044711789710020142489 4439283533842282515106867)
                  ·
                    refine ⟨6658925300763423772660301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4439283533842282515106867 6658925300763423772660301)
                    ·
                      refine ⟨2497096987786283914747613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6658925300763423772660301 2497096987786283914747613)
                      ·
                        rfl

theorem cell23_4863079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_4863079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863079 prefixEnd_4863079 := by exact prefixLift 4863079
  have htrace : WordTrace (prefixWord ++ tailWord_4863079) baseStart_4863079 baseEnd_4863079 := by
    simpa [prefixWord, tailWord_4863079, baseEnd_4863079] using wordTrace_append hprefix tailTrace_4863079
  have hstable : (prefixWord ++ tailWord_4863079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863079).length < 2 ^ (prefixWord ++ tailWord_4863079).sum := by decide
  have hdescent : baseEnd_4863079 < baseStart_4863079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863098 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10]
def baseStart_4863098 : Nat := 118140960795 + 4863098 * 2 ^ 59
def prefixEnd_4863098 : Nat := 4983230072969 + 3 ^ 40 * 4863098 * 2
def baseEnd_4863098 : Nat := 2497106743918719340410025

theorem tailTrace_4863098 : CollatzResearch.WordTrace tailWord_4863098 prefixEnd_4863098 2497106743918719340410025 := by
  unfold tailWord_4863098
  simp only [CollatzResearch.WordTrace]
  refine ⟨44342938933958492964991487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118247837157222647906643965 44342938933958492964991487)
  ·
    refine ⟨66514408400937739447487231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44342938933958492964991487 66514408400937739447487231)
    ·
      refine ⟨99771612601406609171230847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66514408400937739447487231 99771612601406609171230847)
      ·
        refine ⟨149657418902109913756846271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99771612601406609171230847 149657418902109913756846271)
        ·
          refine ⟨224486128353164870635269407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149657418902109913756846271 224486128353164870635269407)
          ·
            refine ⟨336729192529747305952904111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224486128353164870635269407 336729192529747305952904111)
            ·
              refine ⟨505093788794620958929356167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336729192529747305952904111 505093788794620958929356167)
              ·
                refine ⟨757640683191931438394034251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505093788794620958929356167 757640683191931438394034251)
                ·
                  refine ⟨1136461024787897157591051377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 757640683191931438394034251 1136461024787897157591051377)
                  ·
                    refine ⟨852345768590922868193288533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1136461024787897157591051377 852345768590922868193288533)
                    ·
                      refine ⟨2497106743918719340410025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 852345768590922868193288533 2497106743918719340410025)
                      ·
                        rfl

theorem cell23_4863098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_4863098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863098 prefixEnd_4863098 := by exact prefixLift 4863098
  have htrace : WordTrace (prefixWord ++ tailWord_4863098) baseStart_4863098 baseEnd_4863098 := by
    simpa [prefixWord, tailWord_4863098, baseEnd_4863098] using wordTrace_append hprefix tailTrace_4863098
  have hstable : (prefixWord ++ tailWord_4863098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863098).length < 2 ^ (prefixWord ++ tailWord_4863098).sum := by decide
  have hdescent : baseEnd_4863098 < baseStart_4863098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863122 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_4863122 : Nat := 118140960795 + 4863122 * 2 ^ 59
def prefixEnd_4863122 : Nat := 4983230072969 + 3 ^ 40 * 4863122 * 2
def baseEnd_4863122 : Nat := 2497119067454427246509915

theorem tailTrace_4863122 : CollatzResearch.WordTrace tailWord_4863122 prefixEnd_4863122 2497119067454427246509915 := by
  unfold tailWord_4863122
  simp only [CollatzResearch.WordTrace]
  refine ⟨44343157771936755989709905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118248420725164682639226413 44343157771936755989709905)
  ·
    refine ⟨33257368328952566992282429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44343157771936755989709905 33257368328952566992282429)
    ·
      refine ⟨12471513123357212622105911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33257368328952566992282429 12471513123357212622105911)
      ·
        refine ⟨18707269685035818933158867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12471513123357212622105911 18707269685035818933158867)
        ·
          refine ⟨28060904527553728399738301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18707269685035818933158867 28060904527553728399738301)
          ·
            refine ⟨10522839197832648149901863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28060904527553728399738301 10522839197832648149901863)
            ·
              refine ⟨15784258796748972224852795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10522839197832648149901863 15784258796748972224852795)
              ·
                refine ⟨23676388195123458337279193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15784258796748972224852795 23676388195123458337279193)
                ·
                  refine ⟨17757291146342593752959395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23676388195123458337279193 17757291146342593752959395)
                  ·
                    refine ⟨26635936719513890629439093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17757291146342593752959395 26635936719513890629439093)
                    ·
                      refine ⟨2497119067454427246509915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26635936719513890629439093 2497119067454427246509915)
                      ·
                        rfl

theorem cell23_4863122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_4863122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863122 prefixEnd_4863122 := by exact prefixLift 4863122
  have htrace : WordTrace (prefixWord ++ tailWord_4863122) baseStart_4863122 baseEnd_4863122 := by
    simpa [prefixWord, tailWord_4863122, baseEnd_4863122] using wordTrace_append hprefix tailTrace_4863122
  have hstable : (prefixWord ++ tailWord_4863122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863122).length < 2 ^ (prefixWord ++ tailWord_4863122).sum := by decide
  have hdescent : baseEnd_4863122 < baseStart_4863122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863153 : List Nat := [1, 2, 2, 5, 1, 1, 4, 1, 2, 2, 2]
def baseStart_4863153 : Nat := 118140960795 + 4863153 * 2 ^ 59
def prefixEnd_4863153 : Nat := 4983230072969 + 3 ^ 40 * 4863153 * 2
def baseEnd_4863153 : Nat := 2497134985354716625222273

theorem tailTrace_4863153 : CollatzResearch.WordTrace tailWord_4863153 prefixEnd_4863153 2497134985354716625222273 := by
  unfold tailWord_4863153
  simp only [CollatzResearch.WordTrace]
  refine ⟨177373761750634716253218113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118249174500423144168812075 177373761750634716253218113)
  ·
    refine ⟨133030321312976037189913585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177373761750634716253218113 133030321312976037189913585)
    ·
      refine ⟨99772740984732027892435189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133030321312976037189913585 99772740984732027892435189)
      ·
        refine ⟨9353694467318627614915799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99772740984732027892435189 9353694467318627614915799)
        ·
          refine ⟨14030541700977941422373699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9353694467318627614915799 14030541700977941422373699)
          ·
            refine ⟨21045812551466912133560549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14030541700977941422373699 21045812551466912133560549)
            ·
              refine ⟨3946089853400046025042603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21045812551466912133560549 3946089853400046025042603)
              ·
                refine ⟨5919134780100069037563905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3946089853400046025042603 5919134780100069037563905)
                ·
                  refine ⟨4439351085075051778172929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5919134780100069037563905 4439351085075051778172929)
                  ·
                    refine ⟨3329513313806288833629697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4439351085075051778172929 3329513313806288833629697)
                    ·
                      refine ⟨2497134985354716625222273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3329513313806288833629697 2497134985354716625222273)
                      ·
                        rfl

theorem cell23_4863153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_4863153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863153 prefixEnd_4863153 := by exact prefixLift 4863153
  have htrace : WordTrace (prefixWord ++ tailWord_4863153) baseStart_4863153 baseEnd_4863153 := by
    simpa [prefixWord, tailWord_4863153, baseEnd_4863153] using wordTrace_append hprefix tailTrace_4863153
  have hstable : (prefixWord ++ tailWord_4863153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863153).length < 2 ^ (prefixWord ++ tailWord_4863153).sum := by decide
  have hdescent : baseEnd_4863153 < baseStart_4863153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863175 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 4]
def baseStart_4863175 : Nat := 118140960795 + 4863175 * 2 ^ 59
def prefixEnd_4863175 : Nat := 4983230072969 + 3 ^ 40 * 4863175 * 2
def baseEnd_4863175 : Nat := 2497146281929115539147171

theorem tailTrace_4863175 : CollatzResearch.WordTrace tailWord_4863175 prefixEnd_4863175 2497146281929115539147171 := by
  unfold tailWord_4863175
  simp only [CollatzResearch.WordTrace]
  refine ⟨177374564156555014010518979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118249709437703342673679319 177374564156555014010518979)
  ·
    refine ⟨266061846234832521015778469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177374564156555014010518979 266061846234832521015778469)
    ·
      refine ⟨49886596169031097690458463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266061846234832521015778469 49886596169031097690458463)
      ·
        refine ⟨74829894253546646535687695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49886596169031097690458463 74829894253546646535687695)
        ·
          refine ⟨112244841380319969803531543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74829894253546646535687695 112244841380319969803531543)
          ·
            refine ⟨168367262070479954705297315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112244841380319969803531543 168367262070479954705297315)
            ·
              refine ⟨252550893105719932057945973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168367262070479954705297315 252550893105719932057945973)
              ·
                refine ⟨23676646228661243630432435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 252550893105719932057945973 23676646228661243630432435)
                ·
                  refine ⟨35514969342991865445648653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23676646228661243630432435 35514969342991865445648653)
                  ·
                    refine ⟨13318113503621949542118245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35514969342991865445648653 13318113503621949542118245)
                    ·
                      refine ⟨2497146281929115539147171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13318113503621949542118245 2497146281929115539147171)
                      ·
                        rfl

theorem cell23_4863175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_4863175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863175 prefixEnd_4863175 := by exact prefixLift 4863175
  have htrace : WordTrace (prefixWord ++ tailWord_4863175) baseStart_4863175 baseEnd_4863175 := by
    simpa [prefixWord, tailWord_4863175, baseEnd_4863175] using wordTrace_append hprefix tailTrace_4863175
  have hstable : (prefixWord ++ tailWord_4863175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863175).length < 2 ^ (prefixWord ++ tailWord_4863175).sum := by decide
  have hdescent : baseEnd_4863175 < baseStart_4863175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863236 : List Nat := [2, 3, 2, 2, 2, 1, 1, 5, 1, 4]
def baseStart_4863236 : Nat := 118140960795 + 4863236 * 2 ^ 59
def prefixEnd_4863236 : Nat := 4983230072969 + 3 ^ 40 * 4863236 * 2
def baseEnd_4863236 : Nat := 832392534749679933494797

theorem tailTrace_4863236 : CollatzResearch.WordTrace tailWord_4863236 prefixEnd_4863236 832392534749679933494797 := by
  unfold tailWord_4863236
  simp only [CollatzResearch.WordTrace]
  refine ⟨88688394504667010714244781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118251192672889347618993041 88688394504667010714244781)
  ·
    refine ⟨33258147939250129017841793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88688394504667010714244781 33258147939250129017841793)
    ·
      refine ⟨24943610954437596763381345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33258147939250129017841793 24943610954437596763381345)
      ·
        refine ⟨18707708215828197572536009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24943610954437596763381345 18707708215828197572536009)
        ·
          refine ⟨14030781161871148179402007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18707708215828197572536009 14030781161871148179402007)
          ·
            refine ⟨21046171742806722269103011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14030781161871148179402007 21046171742806722269103011)
            ·
              refine ⟨31569257614210083403654517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21046171742806722269103011 31569257614210083403654517)
              ·
                refine ⟨2959617901332195319092611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31569257614210083403654517 2959617901332195319092611)
                ·
                  refine ⟨4439426851998292978638917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2959617901332195319092611 4439426851998292978638917)
                  ·
                    refine ⟨832392534749679933494797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4439426851998292978638917 832392534749679933494797)
                    ·
                      rfl

theorem cell23_4863236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_4863236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863236 prefixEnd_4863236 := by exact prefixLift 4863236
  have htrace : WordTrace (prefixWord ++ tailWord_4863236) baseStart_4863236 baseEnd_4863236 := by
    simpa [prefixWord, tailWord_4863236, baseEnd_4863236] using wordTrace_append hprefix tailTrace_4863236
  have hstable : (prefixWord ++ tailWord_4863236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863236).length < 2 ^ (prefixWord ++ tailWord_4863236).sum := by decide
  have hdescent : baseEnd_4863236 < baseStart_4863236 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863266 : List Nat := [3, 3, 1, 1, 4, 1, 3, 1, 6]
def baseStart_4863266 : Nat := 118140960795 + 4863266 * 2 ^ 59
def prefixEnd_4863266 : Nat := 4983230072969 + 3 ^ 40 * 4863266 * 2
def baseEnd_4863266 : Nat := 277465889852074964789917

theorem tailTrace_4863266 : CollatzResearch.WordTrace tailWord_4863266 prefixEnd_4863266 277465889852074964789917 := by
  unfold tailWord_4863266
  simp only [CollatzResearch.WordTrace]
  refine ⟨44344470799806334138020413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118251922132816891034721101 44344470799806334138020413)
  ·
    refine ⟨16629176549927375301757655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44344470799806334138020413 16629176549927375301757655)
    ·
      refine ⟨24943764824891062952636483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16629176549927375301757655 24943764824891062952636483)
      ·
        refine ⟨37415647237336594428954725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24943764824891062952636483 37415647237336594428954725)
        ·
          refine ⟨7015433857000611455429011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37415647237336594428954725 7015433857000611455429011)
          ·
            refine ⟨10523150785500917183143517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7015433857000611455429011 10523150785500917183143517)
            ·
              refine ⟨3946181544562843943678819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10523150785500917183143517 3946181544562843943678819)
              ·
                refine ⟨5919272316844265915518229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3946181544562843943678819 5919272316844265915518229)
                ·
                  refine ⟨277465889852074964789917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5919272316844265915518229 277465889852074964789917)
                  ·
                    rfl

theorem cell23_4863266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_4863266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863266 prefixEnd_4863266 := by exact prefixLift 4863266
  have htrace : WordTrace (prefixWord ++ tailWord_4863266) baseStart_4863266 baseEnd_4863266 := by
    simpa [prefixWord, tailWord_4863266, baseEnd_4863266] using wordTrace_append hprefix tailTrace_4863266
  have hstable : (prefixWord ++ tailWord_4863266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863266).length < 2 ^ (prefixWord ++ tailWord_4863266).sum := by decide
  have hdescent : baseEnd_4863266 < baseStart_4863266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863269 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 1, 5, 2]
def baseStart_4863269 : Nat := 118140960795 + 4863269 * 2 ^ 59
def prefixEnd_4863269 : Nat := 4983230072969 + 3 ^ 40 * 4863269 * 2
def baseEnd_4863269 : Nat := 2497194549110638171371739

theorem tailTrace_4863269 : CollatzResearch.WordTrace tailWord_4863269 prefixEnd_4863269 2497194549110638171371739 := by
  unfold tailWord_4863269
  simp only [CollatzResearch.WordTrace]
  refine ⟨177377992618214468064440861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118251995078809645376293907 177377992618214468064440861)
  ·
    refine ⟨66516747231830425524165323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177377992618214468064440861 66516747231830425524165323)
    ·
      refine ⟨99775120847745638286247985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66516747231830425524165323 99775120847745638286247985)
      ·
        refine ⟨74831340635809228714685989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99775120847745638286247985 74831340635809228714685989)
        ·
          refine ⟨14030876369214230384003623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74831340635809228714685989 14030876369214230384003623)
          ·
            refine ⟨21046314553821345576005435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14030876369214230384003623 21046314553821345576005435)
            ·
              refine ⟨31569471830732018364008153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21046314553821345576005435 31569471830732018364008153)
              ·
                refine ⟨23677103873049013773006115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31569471830732018364008153 23677103873049013773006115)
                ·
                  refine ⟨35515655809573520659509173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23677103873049013773006115 35515655809573520659509173)
                  ·
                    refine ⟨3329592732147517561828985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35515655809573520659509173 3329592732147517561828985)
                    ·
                      refine ⟨2497194549110638171371739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3329592732147517561828985 2497194549110638171371739)
                      ·
                        rfl

theorem cell23_4863269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_4863269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863269 prefixEnd_4863269 := by exact prefixLift 4863269
  have htrace : WordTrace (prefixWord ++ tailWord_4863269) baseStart_4863269 baseEnd_4863269 := by
    simpa [prefixWord, tailWord_4863269, baseEnd_4863269] using wordTrace_append hprefix tailTrace_4863269
  have hstable : (prefixWord ++ tailWord_4863269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863269).length < 2 ^ (prefixWord ++ tailWord_4863269).sum := by decide
  have hdescent : baseEnd_4863269 < baseStart_4863269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863275 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 7, 6]
def baseStart_4863275 : Nat := 118140960795 + 4863275 * 2 ^ 59
def prefixEnd_4863275 : Nat := 4983230072969 + 3 ^ 40 * 4863275 * 2
def baseEnd_4863275 : Nat := 832399209998188382632237

theorem tailTrace_4863275 : CollatzResearch.WordTrace tailWord_4863275 prefixEnd_4863275 832399209998188382632237 := by
  unfold tailWord_4863275
  simp only [CollatzResearch.WordTrace]
  refine ⟨177378211456192731089159279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118252140970795154059439519 177378211456192731089159279)
  ·
    refine ⟨266067317184289096633738919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177378211456192731089159279 266067317184289096633738919)
    ·
      refine ⟨399100975776433644950608379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266067317184289096633738919 399100975776433644950608379)
      ·
        refine ⟨598651463664650467425912569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399100975776433644950608379 598651463664650467425912569)
        ·
          refine ⟨448988597748487850569434427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 598651463664650467425912569 448988597748487850569434427)
          ·
            refine ⟨673482896622731775854151641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448988597748487850569434427 673482896622731775854151641)
            ·
              refine ⟨505112172467048831890613731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 673482896622731775854151641 505112172467048831890613731)
              ·
                refine ⟨757668258700573247835920597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505112172467048831890613731 757668258700573247835920597)
                ·
                  refine ⟨17757849813294685496154389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 757668258700573247835920597 17757849813294685496154389)
                  ·
                    refine ⟨832399209998188382632237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17757849813294685496154389 832399209998188382632237)
                    ·
                      rfl

theorem cell23_4863275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 6].length) (baseStart_4863275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863275 prefixEnd_4863275 := by exact prefixLift 4863275
  have htrace : WordTrace (prefixWord ++ tailWord_4863275) baseStart_4863275 baseEnd_4863275 := by
    simpa [prefixWord, tailWord_4863275, baseEnd_4863275] using wordTrace_append hprefix tailTrace_4863275
  have hstable : (prefixWord ++ tailWord_4863275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863275).length < 2 ^ (prefixWord ++ tailWord_4863275).sum := by decide
  have hdescent : baseEnd_4863275 < baseStart_4863275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863305 : List Nat := [1, 2, 1, 1, 2, 3, 13]
def baseStart_4863305 : Nat := 118140960795 + 4863305 * 2 ^ 59
def prefixEnd_4863305 : Nat := 4983230072969 + 3 ^ 40 * 4863305 * 2
def baseEnd_4863305 : Nat := 30829790548323457166933

theorem tailTrace_4863305 : CollatzResearch.WordTrace tailWord_4863305 prefixEnd_4863305 30829790548323457166933 := by
  unfold tailWord_4863305
  simp only [CollatzResearch.WordTrace]
  refine ⟨177379305646084046212751369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118252870430722697475167579 177379305646084046212751369)
  ·
    refine ⟨133034479234563034659563527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177379305646084046212751369 133034479234563034659563527)
    ·
      refine ⟨199551718851844551989345291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133034479234563034659563527 199551718851844551989345291)
      ·
        refine ⟨299327578277766827984017937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199551718851844551989345291 299327578277766827984017937)
        ·
          refine ⟨224495683708325120988013453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299327578277766827984017937 224495683708325120988013453)
          ·
            refine ⟨84185881390621920370505045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224495683708325120988013453 84185881390621920370505045)
            ·
              refine ⟨30829790548323457166933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 84185881390621920370505045 30829790548323457166933)
              ·
                rfl

theorem cell23_4863305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 13].length) (baseStart_4863305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863305 prefixEnd_4863305 := by exact prefixLift 4863305
  have htrace : WordTrace (prefixWord ++ tailWord_4863305) baseStart_4863305 baseEnd_4863305 := by
    simpa [prefixWord, tailWord_4863305, baseEnd_4863305] using wordTrace_append hprefix tailTrace_4863305
  have hstable : (prefixWord ++ tailWord_4863305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863305).length < 2 ^ (prefixWord ++ tailWord_4863305).sum := by decide
  have hdescent : baseEnd_4863305 < baseStart_4863305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863336 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_4863336 : Nat := 118140960795 + 4863336 * 2 ^ 59
def prefixEnd_4863336 : Nat := 4983230072969 + 3 ^ 40 * 4863336 * 2
def baseEnd_4863336 : Nat := 2497228952314489409233931

theorem tailTrace_4863336 : CollatzResearch.WordTrace tailWord_4863336 prefixEnd_4863336 2497228952314489409233931 := by
  unfold tailWord_4863336
  simp only [CollatzResearch.WordTrace]
  refine ⟨88690218154485869253564931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118253624205981159004753241 88690218154485869253564931)
  ·
    refine ⟨133035327231728803880347397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88690218154485869253564931 133035327231728803880347397)
    ·
      refine ⟨24944123855949150727565137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133035327231728803880347397 24944123855949150727565137)
      ·
        refine ⟨18708092891961863045673853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24944123855949150727565137 18708092891961863045673853)
        ·
          refine ⟨7015534834485698642127695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18708092891961863045673853 7015534834485698642127695)
          ·
            refine ⟨10523302251728547963191543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7015534834485698642127695 10523302251728547963191543)
            ·
              refine ⟨15784953377592821944787315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10523302251728547963191543 15784953377592821944787315)
              ·
                refine ⟨23677430066389232917180973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15784953377592821944787315 23677430066389232917180973)
                ·
                  refine ⟨8879036274895962343942865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23677430066389232917180973 8879036274895962343942865)
                  ·
                    refine ⟨6659277206171971757957149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8879036274895962343942865 6659277206171971757957149)
                    ·
                      refine ⟨2497228952314489409233931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6659277206171971757957149 2497228952314489409233931)
                      ·
                        rfl

theorem cell23_4863336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_4863336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863336 prefixEnd_4863336 := by exact prefixLift 4863336
  have htrace : WordTrace (prefixWord ++ tailWord_4863336) baseStart_4863336 baseEnd_4863336 := by
    simpa [prefixWord, tailWord_4863336, baseEnd_4863336] using wordTrace_append hprefix tailTrace_4863336
  have hstable : (prefixWord ++ tailWord_4863336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863336).length < 2 ^ (prefixWord ++ tailWord_4863336).sum := by decide
  have hdescent : baseEnd_4863336 < baseStart_4863336 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863359 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 7, 3, 2]
def baseStart_4863359 : Nat := 118140960795 + 4863359 * 2 ^ 59
def prefixEnd_4863359 : Nat := 4983230072969 + 3 ^ 40 * 4863359 * 2
def baseEnd_4863359 : Nat := 2497240762369542819246325

theorem tailTrace_4863359 : CollatzResearch.WordTrace tailWord_4863359 prefixEnd_4863359 2497240762369542819246325 := by
  unfold tailWord_4863359
  simp only [CollatzResearch.WordTrace]
  refine ⟨177381275187888413435217131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118254183458592275623478087 177381275187888413435217131)
  ·
    refine ⟨266071912781832620152825697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177381275187888413435217131 266071912781832620152825697)
    ·
      refine ⟨199553934586374465114619273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266071912781832620152825697 199553934586374465114619273)
      ·
        refine ⟨149665450939780848835964455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199553934586374465114619273 149665450939780848835964455)
        ·
          refine ⟨224498176409671273253946683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149665450939780848835964455 224498176409671273253946683)
          ·
            refine ⟨336747264614506909880920025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224498176409671273253946683 336747264614506909880920025)
            ·
              refine ⟨252560448460880182410690019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 336747264614506909880920025 252560448460880182410690019)
              ·
                refine ⟨378840672691320273616035029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252560448460880182410690019 378840672691320273616035029)
                ·
                  refine ⟨8879078266202818912875821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 378840672691320273616035029 8879078266202818912875821)
                  ·
                    refine ⟨3329654349826057092328433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8879078266202818912875821 3329654349826057092328433)
                    ·
                      refine ⟨2497240762369542819246325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3329654349826057092328433 2497240762369542819246325)
                      ·
                        rfl

theorem cell23_4863359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 3, 2].length) (baseStart_4863359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863359 prefixEnd_4863359 := by exact prefixLift 4863359
  have htrace : WordTrace (prefixWord ++ tailWord_4863359) baseStart_4863359 baseEnd_4863359 := by
    simpa [prefixWord, tailWord_4863359, baseEnd_4863359] using wordTrace_append hprefix tailTrace_4863359
  have hstable : (prefixWord ++ tailWord_4863359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863359).length < 2 ^ (prefixWord ++ tailWord_4863359).sum := by decide
  have hdescent : baseEnd_4863359 < baseStart_4863359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863367 : List Nat := [1, 1, 4, 2, 2, 4, 2, 2, 1, 2, 2]
def baseStart_4863367 : Nat := 118140960795 + 4863367 * 2 ^ 59
def prefixEnd_4863367 : Nat := 4983230072969 + 3 ^ 40 * 4863367 * 2
def baseEnd_4863367 : Nat := 2497244870214778787946289

theorem tailTrace_4863367 : CollatzResearch.WordTrace tailWord_4863367 prefixEnd_4863367 2497244870214778787946289 := by
  unfold tailWord_4863367
  simp only [CollatzResearch.WordTrace]
  refine ⟨177381566971859430801508355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118254377981239620534338903 177381566971859430801508355)
  ·
    refine ⟨266072350457789146202262533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177381566971859430801508355 266072350457789146202262533)
    ·
      refine ⟨49888565710835464912924225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266072350457789146202262533 49888565710835464912924225)
      ·
        refine ⟨37416424283126598684693169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49888565710835464912924225 37416424283126598684693169)
        ·
          refine ⟨28062318212344949013519877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37416424283126598684693169 28062318212344949013519877)
          ·
            refine ⟨5261684664814677940034977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28062318212344949013519877 5261684664814677940034977)
            ·
              refine ⟨3946263498611008455026233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5261684664814677940034977 3946263498611008455026233)
              ·
                refine ⟨2959697623958256341269675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3946263498611008455026233 2959697623958256341269675)
                ·
                  refine ⟨4439546435937384511904513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2959697623958256341269675 4439546435937384511904513)
                  ·
                    refine ⟨3329659826953038383928385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4439546435937384511904513 3329659826953038383928385)
                    ·
                      refine ⟨2497244870214778787946289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3329659826953038383928385 2497244870214778787946289)
                      ·
                        rfl

theorem cell23_4863367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_4863367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863367 prefixEnd_4863367 := by exact prefixLift 4863367
  have htrace : WordTrace (prefixWord ++ tailWord_4863367) baseStart_4863367 baseEnd_4863367 := by
    simpa [prefixWord, tailWord_4863367, baseEnd_4863367] using wordTrace_append hprefix tailTrace_4863367
  have hstable : (prefixWord ++ tailWord_4863367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863367).length < 2 ^ (prefixWord ++ tailWord_4863367).sum := by decide
  have hdescent : baseEnd_4863367 < baseStart_4863367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863372 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 1, 5, 4]
def baseStart_4863372 : Nat := 118140960795 + 4863372 * 2 ^ 59
def prefixEnd_4863372 : Nat := 4983230072969 + 3 ^ 40 * 4863372 * 2
def baseEnd_4863372 : Nat := 2497247437618051268383765

theorem tailTrace_4863372 : CollatzResearch.WordTrace tailWord_4863372 prefixEnd_4863372 2497247437618051268383765 := by
  unfold tailWord_4863372
  simp only [CollatzResearch.WordTrace]
  refine ⟨88690874668420658327720185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118254499557894211103626913 88690874668420658327720185)
  ·
    refine ⟨66518156001315493745790139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88690874668420658327720185 66518156001315493745790139)
    ·
      refine ⟨99777234001973240618685209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66518156001315493745790139 99777234001973240618685209)
      ·
        refine ⟨74832925501479930464013907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99777234001973240618685209 74832925501479930464013907)
        ·
          refine ⟨112249388252219895696020861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74832925501479930464013907 112249388252219895696020861)
          ·
            refine ⟨42093520594582460886007823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112249388252219895696020861 42093520594582460886007823)
            ·
              refine ⟨63140280891873691329011735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42093520594582460886007823 63140280891873691329011735)
              ·
                refine ⟨94710421337810536993517603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63140280891873691329011735 94710421337810536993517603)
                ·
                  refine ⟨142065632006715805490276405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94710421337810536993517603 142065632006715805490276405)
                  ·
                    refine ⟨13318653000629606764713413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 142065632006715805490276405 13318653000629606764713413)
                    ·
                      refine ⟨2497247437618051268383765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13318653000629606764713413 2497247437618051268383765)
                      ·
                        rfl

theorem cell23_4863372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_4863372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863372 prefixEnd_4863372 := by exact prefixLift 4863372
  have htrace : WordTrace (prefixWord ++ tailWord_4863372) baseStart_4863372 baseEnd_4863372 := by
    simpa [prefixWord, tailWord_4863372, baseEnd_4863372] using wordTrace_append hprefix tailTrace_4863372
  have hstable : (prefixWord ++ tailWord_4863372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863372).length < 2 ^ (prefixWord ++ tailWord_4863372).sum := by decide
  have hdescent : baseEnd_4863372 < baseStart_4863372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863439 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 3]
def baseStart_4863439 : Nat := 118140960795 + 4863439 * 2 ^ 59
def prefixEnd_4863439 : Nat := 4983230072969 + 3 ^ 40 * 4863439 * 2
def baseEnd_4863439 : Nat := 2497281840821902506245957

theorem tailTrace_4863439 : CollatzResearch.WordTrace tailWord_4863439 prefixEnd_4863439 2497281840821902506245957 := by
  unfold tailWord_4863439
  simp only [CollatzResearch.WordTrace]
  refine ⟨177384193027598587098129371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118256128685065724732086247 177384193027598587098129371)
  ·
    refine ⟨266076289541397880647194057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177384193027598587098129371 266076289541397880647194057)
    ·
      refine ⟨199557217156048410485395543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266076289541397880647194057 199557217156048410485395543)
      ·
        refine ⟨299335825734072615728093315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199557217156048410485395543 299335825734072615728093315)
        ·
          refine ⟨449003738601108923592139973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299335825734072615728093315 449003738601108923592139973)
          ·
            refine ⟨84188200987707923173526245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 449003738601108923592139973 84188200987707923173526245)
            ·
              refine ⟨15785287685195235595036171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84188200987707923173526245 15785287685195235595036171)
              ·
                refine ⟨23677931527792853392554257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15785287685195235595036171 23677931527792853392554257)
                ·
                  refine ⟨17758448645844640044415693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23677931527792853392554257 17758448645844640044415693)
                  ·
                    refine ⟨6659418242191740016655885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17758448645844640044415693 6659418242191740016655885)
                    ·
                      refine ⟨2497281840821902506245957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6659418242191740016655885 2497281840821902506245957)
                      ·
                        rfl

theorem cell23_4863439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 3].length) (baseStart_4863439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863439 prefixEnd_4863439 := by exact prefixLift 4863439
  have htrace : WordTrace (prefixWord ++ tailWord_4863439) baseStart_4863439 baseEnd_4863439 := by
    simpa [prefixWord, tailWord_4863439, baseEnd_4863439] using wordTrace_append hprefix tailTrace_4863439
  have hstable : (prefixWord ++ tailWord_4863439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863439).length < 2 ^ (prefixWord ++ tailWord_4863439).sum := by decide
  have hdescent : baseEnd_4863439 < baseStart_4863439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863446 : List Nat := [5, 2, 1, 1, 1, 2, 2, 2, 7]
def baseStart_4863446 : Nat := 118140960795 + 4863446 * 2 ^ 59
def prefixEnd_4863446 : Nat := 4983230072969 + 3 ^ 40 * 4863446 * 2
def baseEnd_4863446 : Nat := 277476159465164886539825

theorem tailTrace_4863446 : CollatzResearch.WordTrace tailWord_4863446 prefixEnd_4863446 277476159465164886539825 := by
  unfold tailWord_4863446
  simp only [CollatzResearch.WordTrace]
  refine ⟨11086528021160826705852137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118256298892382151529089461 11086528021160826705852137)
  ·
    refine ⟨8314896015870620029389103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11086528021160826705852137 8314896015870620029389103)
    ·
      refine ⟨12472344023805930044083655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8314896015870620029389103 12472344023805930044083655)
      ·
        refine ⟨18708516035708895066125483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12472344023805930044083655 18708516035708895066125483)
        ·
          refine ⟨28062774053563342599188225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18708516035708895066125483 28062774053563342599188225)
          ·
            refine ⟨21047080540172506949391169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28062774053563342599188225 21047080540172506949391169)
            ·
              refine ⟨15785310405129380212043377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21047080540172506949391169 15785310405129380212043377)
              ·
                refine ⟨11838982803847035159032533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15785310405129380212043377 11838982803847035159032533)
                ·
                  refine ⟨277476159465164886539825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11838982803847035159032533 277476159465164886539825)
                  ·
                    rfl

theorem cell23_4863446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_4863446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863446 prefixEnd_4863446 := by exact prefixLift 4863446
  have htrace : WordTrace (prefixWord ++ tailWord_4863446) baseStart_4863446 baseEnd_4863446 := by
    simpa [prefixWord, tailWord_4863446, baseEnd_4863446] using wordTrace_append hprefix tailTrace_4863446
  have hstable : (prefixWord ++ tailWord_4863446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863446).length < 2 ^ (prefixWord ++ tailWord_4863446).sum := by decide
  have hdescent : baseEnd_4863446 < baseStart_4863446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863459 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 1, 7]
def baseStart_4863459 : Nat := 118140960795 + 4863459 * 2 ^ 59
def prefixEnd_4863459 : Nat := 4983230072969 + 3 ^ 40 * 4863459 * 2
def baseEnd_4863459 : Nat := 832430703478330809331955

theorem tailTrace_4863459 : CollatzResearch.WordTrace tailWord_4863459 prefixEnd_4863459 832430703478330809331955 := by
  unfold tailWord_4863459
  simp only [CollatzResearch.WordTrace]
  refine ⟨177384922487526130513857431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118256614991684087009238287 177384922487526130513857431)
  ·
    refine ⟨266077383731289195770786147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177384922487526130513857431 266077383731289195770786147)
    ·
      refine ⟨399116075596933793656179221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266077383731289195770786147 399116075596933793656179221)
      ·
        refine ⟨18708566043606271577633401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 399116075596933793656179221 18708566043606271577633401)
        ·
          refine ⟨14031424532704703683225051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18708566043606271577633401 14031424532704703683225051)
          ·
            refine ⟨21047136799057055524837577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14031424532704703683225051 21047136799057055524837577)
            ·
              refine ⟨15785352599292791643628183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21047136799057055524837577 15785352599292791643628183)
              ·
                refine ⟨23678028898939187465442275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15785352599292791643628183 23678028898939187465442275)
                ·
                  refine ⟨35517043348408781198163413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23678028898939187465442275 35517043348408781198163413)
                  ·
                    refine ⟨832430703478330809331955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35517043348408781198163413 832430703478330809331955)
                    ·
                      rfl

theorem cell23_4863459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 1, 7].length) (baseStart_4863459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863459 prefixEnd_4863459 := by exact prefixLift 4863459
  have htrace : WordTrace (prefixWord ++ tailWord_4863459) baseStart_4863459 baseEnd_4863459 := by
    simpa [prefixWord, tailWord_4863459, baseEnd_4863459] using wordTrace_append hprefix tailTrace_4863459
  have hstable : (prefixWord ++ tailWord_4863459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863459).length < 2 ^ (prefixWord ++ tailWord_4863459).sum := by decide
  have hdescent : baseEnd_4863459 < baseStart_4863459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863463 : List Nat := [1, 1, 5, 2, 1, 4, 1, 3, 5]
def baseStart_4863463 : Nat := 118140960795 + 4863463 * 2 ^ 59
def prefixEnd_4863463 : Nat := 4983230072969 + 3 ^ 40 * 4863463 * 2
def baseEnd_4863463 : Nat := 277477129373067823593983

theorem tailTrace_4863463 : CollatzResearch.WordTrace tailWord_4863463 prefixEnd_4863463 277477129373067823593983 := by
  unfold tailWord_4863463
  simp only [CollatzResearch.WordTrace]
  refine ⟨177385068379511639197003043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118256712253007759464668695 177385068379511639197003043)
  ·
    refine ⟨266077602569267458795504565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177385068379511639197003043 266077602569267458795504565)
    ·
      refine ⟨24944775240868824262078553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 266077602569267458795504565 24944775240868824262078553)
      ·
        refine ⟨18708581430651618196558915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24944775240868824262078553 18708581430651618196558915)
        ·
          refine ⟨28062872145977427294838373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18708581430651618196558915 28062872145977427294838373)
          ·
            refine ⟨5261788527370767617782195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28062872145977427294838373 5261788527370767617782195)
            ·
              refine ⟨7892682791056151426673293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5261788527370767617782195 7892682791056151426673293)
              ·
                refine ⟨2959756046646056785002485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7892682791056151426673293 2959756046646056785002485)
                ·
                  refine ⟨277477129373067823593983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2959756046646056785002485 277477129373067823593983)
                  ·
                    rfl

theorem cell23_4863463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 3, 5].length) (baseStart_4863463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863463 prefixEnd_4863463 := by exact prefixLift 4863463
  have htrace : WordTrace (prefixWord ++ tailWord_4863463) baseStart_4863463 baseEnd_4863463 := by
    simpa [prefixWord, tailWord_4863463, baseEnd_4863463] using wordTrace_append hprefix tailTrace_4863463
  have hstable : (prefixWord ++ tailWord_4863463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863463).length < 2 ^ (prefixWord ++ tailWord_4863463).sum := by decide
  have hdescent : baseEnd_4863463 < baseStart_4863463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863496 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 2, 4, 2]
def baseStart_4863496 : Nat := 118140960795 + 4863496 * 2 ^ 59
def prefixEnd_4863496 : Nat := 4983230072969 + 3 ^ 40 * 4863496 * 2
def baseEnd_4863496 : Nat := 2497311109219208783233195

theorem tailTrace_4863496 : CollatzResearch.WordTrace tailWord_4863496 prefixEnd_4863496 2497311109219208783233195 := by
  unfold tailWord_4863496
  simp only [CollatzResearch.WordTrace]
  refine ⟨88693135994196042916477171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118257514658928057221969561 88693135994196042916477171)
  ·
    refine ⟨133039703991294064374715757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88693135994196042916477171 133039703991294064374715757)
    ·
      refine ⟨49889888996735274140518409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133039703991294064374715757 49889888996735274140518409)
      ·
        refine ⟨37417416747551455605388807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49889888996735274140518409 37417416747551455605388807)
        ·
          refine ⟨56126125121327183408083211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37417416747551455605388807 56126125121327183408083211)
          ·
            refine ⟨84189187681990775112124817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56126125121327183408083211 84189187681990775112124817)
            ·
              refine ⟨63141890761493081334093613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84189187681990775112124817 63141890761493081334093613)
              ·
                refine ⟨23678209035559905500285105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63141890761493081334093613 23678209035559905500285105)
                ·
                  refine ⟨17758656776669929125213829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23678209035559905500285105 17758656776669929125213829)
                  ·
                    refine ⟨3329748145625611710977593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17758656776669929125213829 3329748145625611710977593)
                    ·
                      refine ⟨2497311109219208783233195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3329748145625611710977593 2497311109219208783233195)
                      ·
                        rfl

theorem cell23_4863496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_4863496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863496 prefixEnd_4863496 := by exact prefixLift 4863496
  have htrace : WordTrace (prefixWord ++ tailWord_4863496) baseStart_4863496 baseEnd_4863496 := by
    simpa [prefixWord, tailWord_4863496, baseEnd_4863496] using wordTrace_append hprefix tailTrace_4863496
  have hstable : (prefixWord ++ tailWord_4863496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863496).length < 2 ^ (prefixWord ++ tailWord_4863496).sum := by decide
  have hdescent : baseEnd_4863496 < baseStart_4863496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863566 : List Nat := [4, 1, 1, 1, 1, 2, 1, 6, 1, 5]
def baseStart_4863566 : Nat := 118140960795 + 4863566 * 2 ^ 59
def prefixEnd_4863566 : Nat := 4983230072969 + 3 ^ 40 * 4863566 * 2
def baseEnd_4863566 : Nat := 832449017621674503119291

theorem tailTrace_4863566 : CollatzResearch.WordTrace tailWord_4863566 prefixEnd_4863566 832449017621674503119291 := by
  unfold tailWord_4863566
  simp only [CollatzResearch.WordTrace]
  refine ⟨22173603137267310973500319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118259216732092325192001701 22173603137267310973500319)
  ·
    refine ⟨33260404705900966460250479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22173603137267310973500319 33260404705900966460250479)
    ·
      refine ⟨49890607058851449690375719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33260404705900966460250479 49890607058851449690375719)
      ·
        refine ⟨74835910588277174535563579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49890607058851449690375719 74835910588277174535563579)
        ·
          refine ⟨112253865882415761803345369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74835910588277174535563579 112253865882415761803345369)
          ·
            refine ⟨84190399411811821352509027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112253865882415761803345369 84190399411811821352509027)
            ·
              refine ⟨126285599117717732028763541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84190399411811821352509027 126285599117717732028763541)
              ·
                refine ⟨5919637458643018688848291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 126285599117717732028763541 5919637458643018688848291)
                ·
                  refine ⟨8879456187964528033272437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5919637458643018688848291 8879456187964528033272437)
                  ·
                    refine ⟨832449017621674503119291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8879456187964528033272437 832449017621674503119291)
                    ·
                      rfl

theorem cell23_4863566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_4863566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863566 prefixEnd_4863566 := by exact prefixLift 4863566
  have htrace : WordTrace (prefixWord ++ tailWord_4863566) baseStart_4863566 baseEnd_4863566 := by
    simpa [prefixWord, tailWord_4863566, baseEnd_4863566] using wordTrace_append hprefix tailTrace_4863566
  have hstable : (prefixWord ++ tailWord_4863566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863566).length < 2 ^ (prefixWord ++ tailWord_4863566).sum := by decide
  have hdescent : baseEnd_4863566 < baseStart_4863566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863599 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 6]
def baseStart_4863599 : Nat := 118140960795 + 4863599 * 2 ^ 59
def prefixEnd_4863599 : Nat := 4983230072969 + 3 ^ 40 * 4863599 * 2
def baseEnd_4863599 : Nat := 2497363997726621880245221

theorem tailTrace_4863599 : CollatzResearch.WordTrace tailWord_4863599 prefixEnd_4863599 2497363997726621880245221 := by
  unfold tailWord_4863599
  simp only [CollatzResearch.WordTrace]
  refine ⟨177390028707018934423953851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118260019138012622949302567 177390028707018934423953851)
  ·
    refine ⟨266085043060528401635930777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177390028707018934423953851 266085043060528401635930777)
    ·
      refine ⟨199563782295396301226948083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266085043060528401635930777 199563782295396301226948083)
      ·
        refine ⟨299345673443094451840422125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199563782295396301226948083 299345673443094451840422125)
        ·
          refine ⟨112254627541160419440158297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 299345673443094451840422125 112254627541160419440158297)
          ·
            refine ⟨84190970655870314580118723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112254627541160419440158297 84190970655870314580118723)
            ·
              refine ⟨126286455983805471870178085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84190970655870314580118723 126286455983805471870178085)
              ·
                refine ⟨23678710496963525975658391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126286455983805471870178085 23678710496963525975658391)
                ·
                  refine ⟨35518065745445288963487587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23678710496963525975658391 35518065745445288963487587)
                  ·
                    refine ⟨53277098618167933445231381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35518065745445288963487587 53277098618167933445231381)
                    ·
                      refine ⟨2497363997726621880245221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53277098618167933445231381 2497363997726621880245221)
                      ·
                        rfl

theorem cell23_4863599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_4863599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863599 prefixEnd_4863599 := by exact prefixLift 4863599
  have htrace : WordTrace (prefixWord ++ tailWord_4863599) baseStart_4863599 baseEnd_4863599 := by
    simpa [prefixWord, tailWord_4863599, baseEnd_4863599] using wordTrace_append hprefix tailTrace_4863599
  have hstable : (prefixWord ++ tailWord_4863599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863599).length < 2 ^ (prefixWord ++ tailWord_4863599).sum := by decide
  have hdescent : baseEnd_4863599 < baseStart_4863599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863609 : List Nat := [1, 2, 1, 3, 3, 1, 2, 10]
def baseStart_4863609 : Nat := 118140960795 + 4863609 * 2 ^ 59
def prefixEnd_4863609 : Nat := 4983230072969 + 3 ^ 40 * 4863609 * 2
def baseEnd_4863609 : Nat := 92495153056783957078525

theorem tailTrace_4863609 : CollatzResearch.WordTrace tailWord_4863609 prefixEnd_4863609 92495153056783957078525 := by
  unfold tailWord_4863609
  simp only [CollatzResearch.WordTrace]
  refine ⟨177390393436982706131817881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118260262291321804087878587 177390393436982706131817881)
  ·
    refine ⟨133042795077737029598863411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177390393436982706131817881 133042795077737029598863411)
    ·
      refine ⟨199564192616605544398295117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133042795077737029598863411 199564192616605544398295117)
      ·
        refine ⟨74836572231227079149360669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199564192616605544398295117 74836572231227079149360669)
        ·
          refine ⟨28063714586710154681010251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74836572231227079149360669 28063714586710154681010251)
          ·
            refine ⟨42095571880065232021515377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28063714586710154681010251 42095571880065232021515377)
            ·
              refine ⟨31571678910048924016136533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42095571880065232021515377 31571678910048924016136533)
              ·
                refine ⟨92495153056783957078525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31571678910048924016136533 92495153056783957078525)
                ·
                  rfl

theorem cell23_4863609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 10].length) (baseStart_4863609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863609 prefixEnd_4863609 := by exact prefixLift 4863609
  have htrace : WordTrace (prefixWord ++ tailWord_4863609) baseStart_4863609 baseEnd_4863609 := by
    simpa [prefixWord, tailWord_4863609, baseEnd_4863609] using wordTrace_append hprefix tailTrace_4863609
  have hstable : (prefixWord ++ tailWord_4863609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863609).length < 2 ^ (prefixWord ++ tailWord_4863609).sum := by decide
  have hdescent : baseEnd_4863609 < baseStart_4863609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863613 : List Nat := [1, 4, 1, 1, 4, 3, 1, 1, 1, 6]
def baseStart_4863613 : Nat := 118140960795 + 4863613 * 2 ^ 59
def prefixEnd_4863613 : Nat := 4983230072969 + 3 ^ 40 * 4863613 * 2
def baseEnd_4863613 : Nat := 832457062151928275156719

theorem tailTrace_4863613 : CollatzResearch.WordTrace tailWord_4863613 prefixEnd_4863613 832457062151928275156719 := by
  unfold tailWord_4863613
  simp only [CollatzResearch.WordTrace]
  refine ⟨177390539328968214814963493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118260359552645476543308995 177390539328968214814963493)
  ·
    refine ⟨33260726124181540277805655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177390539328968214814963493 33260726124181540277805655)
    ·
      refine ⟨49891089186272310416708483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33260726124181540277805655 49891089186272310416708483)
      ·
        refine ⟨74836633779408465625062725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49891089186272310416708483 74836633779408465625062725)
        ·
          refine ⟨14031868833639087304699261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74836633779408465625062725 14031868833639087304699261)
          ·
            refine ⟨5261950812614657739262223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14031868833639087304699261 5261950812614657739262223)
            ·
              refine ⟨7892926218921986608893335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5261950812614657739262223 7892926218921986608893335)
              ·
                refine ⟨11839389328382979913340003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7892926218921986608893335 11839389328382979913340003)
                ·
                  refine ⟨17759083992574469870010005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11839389328382979913340003 17759083992574469870010005)
                  ·
                    refine ⟨832457062151928275156719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17759083992574469870010005 832457062151928275156719)
                    ·
                      rfl

theorem cell23_4863613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_4863613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863613 prefixEnd_4863613 := by exact prefixLift 4863613
  have htrace : WordTrace (prefixWord ++ tailWord_4863613) baseStart_4863613 baseEnd_4863613 := by
    simpa [prefixWord, tailWord_4863613, baseEnd_4863613] using wordTrace_append hprefix tailTrace_4863613
  have hstable : (prefixWord ++ tailWord_4863613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863613).length < 2 ^ (prefixWord ++ tailWord_4863613).sum := by decide
  have hdescent : baseEnd_4863613 < baseStart_4863613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863620 : List Nat := [2, 3, 2, 1, 4, 1, 2, 2, 1, 1, 4]
def baseStart_4863620 : Nat := 118140960795 + 4863620 * 2 ^ 59
def prefixEnd_4863620 : Nat := 4983230072969 + 3 ^ 40 * 4863620 * 2
def baseEnd_4863620 : Nat := 2497374780820366298082625

theorem tailTrace_4863620 : CollatzResearch.WordTrace tailWord_4863620 prefixEnd_4863620 2497374780820366298082625 := by
  unfold tailWord_4863620
  simp only [CollatzResearch.WordTrace]
  refine ⟨88695397319971427505234157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118260529759961903340312209 88695397319971427505234157)
  ·
    refine ⟨33260773994989285314462809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88695397319971427505234157 33260773994989285314462809)
    ·
      refine ⟨24945580496241963985847107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33260773994989285314462809 24945580496241963985847107)
      ·
        refine ⟨37418370744362945978770661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24945580496241963985847107 37418370744362945978770661)
        ·
          refine ⟨7015944514568052371019499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37418370744362945978770661 7015944514568052371019499)
          ·
            refine ⟨10523916771852078556529249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7015944514568052371019499 10523916771852078556529249)
            ·
              refine ⟨7892937578889058917396937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10523916771852078556529249 7892937578889058917396937)
              ·
                refine ⟨5919703184166794188047703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7892937578889058917396937 5919703184166794188047703)
                ·
                  refine ⟨8879554776250191282071555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5919703184166794188047703 8879554776250191282071555)
                  ·
                    refine ⟨13319332164375286923107333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8879554776250191282071555 13319332164375286923107333)
                    ·
                      refine ⟨2497374780820366298082625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13319332164375286923107333 2497374780820366298082625)
                      ·
                        rfl

theorem cell23_4863620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_4863620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863620 prefixEnd_4863620 := by exact prefixLift 4863620
  have htrace : WordTrace (prefixWord ++ tailWord_4863620) baseStart_4863620 baseEnd_4863620 := by
    simpa [prefixWord, tailWord_4863620, baseEnd_4863620] using wordTrace_append hprefix tailTrace_4863620
  have hstable : (prefixWord ++ tailWord_4863620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863620).length < 2 ^ (prefixWord ++ tailWord_4863620).sum := by decide
  have hdescent : baseEnd_4863620 < baseStart_4863620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863623 : List Nat := [1, 1, 4, 2, 1, 3, 1, 4, 1, 2, 3]
def baseStart_4863623 : Nat := 118140960795 + 4863623 * 2 ^ 59
def prefixEnd_4863623 : Nat := 4983230072969 + 3 ^ 40 * 4863623 * 2
def baseEnd_4863623 : Nat := 2497376321262329786345111

theorem tailTrace_4863623 : CollatzResearch.WordTrace tailWord_4863623 prefixEnd_4863623 2497376321262329786345111 := by
  unfold tailWord_4863623
  simp only [CollatzResearch.WordTrace]
  refine ⟨177390904058931986522827523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118260602705954657681885015 177390904058931986522827523)
  ·
    refine ⟨266086356088397979784241285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177390904058931986522827523 266086356088397979784241285)
    ·
      refine ⟨49891191766574621209545241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266086356088397979784241285 49891191766574621209545241)
      ·
        refine ⟨37418393824930965907158931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49891191766574621209545241 37418393824930965907158931)
        ·
          refine ⟨56127590737396448860738397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37418393824930965907158931 56127590737396448860738397)
          ·
            refine ⟨21047846526523668322776899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56127590737396448860738397 21047846526523668322776899)
            ·
              refine ⟨31571769789785502484165349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21047846526523668322776899 31571769789785502484165349)
              ·
                refine ⟨5919706835584781715781003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31571769789785502484165349 5919706835584781715781003)
                ·
                  refine ⟨8879560253377172573671505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5919706835584781715781003 8879560253377172573671505)
                  ·
                    refine ⟨6659670190032879430253629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8879560253377172573671505 6659670190032879430253629)
                    ·
                      refine ⟨2497376321262329786345111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6659670190032879430253629 2497376321262329786345111)
                      ·
                        rfl

theorem cell23_4863623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_4863623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863623 prefixEnd_4863623 := by exact prefixLift 4863623
  have htrace : WordTrace (prefixWord ++ tailWord_4863623) baseStart_4863623 baseEnd_4863623 := by
    simpa [prefixWord, tailWord_4863623, baseEnd_4863623] using wordTrace_append hprefix tailTrace_4863623
  have hstable : (prefixWord ++ tailWord_4863623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863623).length < 2 ^ (prefixWord ++ tailWord_4863623).sum := by decide
  have hdescent : baseEnd_4863623 < baseStart_4863623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863626 : List Nat := [3, 1, 2, 3, 2, 2, 1, 9]
def baseStart_4863626 : Nat := 118140960795 + 4863626 * 2 ^ 59
def prefixEnd_4863626 : Nat := 4983230072969 + 3 ^ 40 * 4863626 * 2
def baseEnd_4863626 : Nat := 92495476359418269429911

theorem tailTrace_4863626 : CollatzResearch.WordTrace tailWord_4863626 prefixEnd_4863626 92495476359418269429911 := by
  unfold tailWord_4863626
  simp only [CollatzResearch.WordTrace]
  refine ⟨44347753369480279508796683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118260675651947412023457821 44347753369480279508796683)
  ·
    refine ⟨66521630054220419263195025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44347753369480279508796683 66521630054220419263195025)
    ·
      refine ⟨49891222540665314447396269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66521630054220419263195025 49891222540665314447396269)
      ·
        refine ⟨18709208452749492917773601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49891222540665314447396269 18709208452749492917773601)
        ·
          refine ⟨14031906339562119688330201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18709208452749492917773601 14031906339562119688330201)
          ·
            refine ⟨10523929754671589766247651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14031906339562119688330201 10523929754671589766247651)
            ·
              refine ⟨15785894632007384649371477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10523929754671589766247651 15785894632007384649371477)
              ·
                refine ⟨92495476359418269429911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15785894632007384649371477 92495476359418269429911)
                ·
                  rfl

theorem cell23_4863626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 9].length) (baseStart_4863626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863626 prefixEnd_4863626 := by exact prefixLift 4863626
  have htrace : WordTrace (prefixWord ++ tailWord_4863626) baseStart_4863626 baseEnd_4863626 := by
    simpa [prefixWord, tailWord_4863626, baseEnd_4863626] using wordTrace_append hprefix tailTrace_4863626
  have hstable : (prefixWord ++ tailWord_4863626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863626).length < 2 ^ (prefixWord ++ tailWord_4863626).sum := by decide
  have hdescent : baseEnd_4863626 < baseStart_4863626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863653 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 4, 1, 3]
def baseStart_4863653 : Nat := 118140960795 + 4863653 * 2 ^ 59
def prefixEnd_4863653 : Nat := 4983230072969 + 3 ^ 40 * 4863653 * 2
def baseEnd_4863653 : Nat := 2497391725681964668969973

theorem tailTrace_4863653 : CollatzResearch.WordTrace tailWord_4863653 prefixEnd_4863653 2497391725681964668969973 := by
  unfold tailWord_4863653
  simp only [CollatzResearch.WordTrace]
  refine ⟨177391998248823301646419613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118261332165882201097613075 177391998248823301646419613)
  ·
    refine ⟨66521999343308738117407355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177391998248823301646419613 66521999343308738117407355)
    ·
      refine ⟨99782999014963107176111033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66521999343308738117407355 99782999014963107176111033)
      ·
        refine ⟨74837249261222330382083275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99782999014963107176111033 74837249261222330382083275)
        ·
          refine ⟨112255873891833495573124913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74837249261222330382083275 112255873891833495573124913)
          ·
            refine ⟨84191905418875121679843685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112255873891833495573124913 84191905418875121679843685)
            ·
              refine ⟨15785982266039085314970691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84191905418875121679843685 15785982266039085314970691)
              ·
                refine ⟨23678973399058627972456037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15785982266039085314970691 23678973399058627972456037)
                ·
                  refine ⟨4439807512323492744835507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23678973399058627972456037 4439807512323492744835507)
                  ·
                    refine ⟨6659711268485239117253261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4439807512323492744835507 6659711268485239117253261)
                    ·
                      refine ⟨2497391725681964668969973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6659711268485239117253261 2497391725681964668969973)
                      ·
                        rfl

theorem cell23_4863653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_4863653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863653 prefixEnd_4863653 := by exact prefixLift 4863653
  have htrace : WordTrace (prefixWord ++ tailWord_4863653) baseStart_4863653 baseEnd_4863653 := by
    simpa [prefixWord, tailWord_4863653, baseEnd_4863653] using wordTrace_append hprefix tailTrace_4863653
  have hstable : (prefixWord ++ tailWord_4863653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863653).length < 2 ^ (prefixWord ++ tailWord_4863653).sum := by decide
  have hdescent : baseEnd_4863653 < baseStart_4863653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863663 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 3, 3, 2]
def baseStart_4863663 : Nat := 118140960795 + 4863663 * 2 ^ 59
def prefixEnd_4863663 : Nat := 4983230072969 + 3 ^ 40 * 4863663 * 2
def baseEnd_4863663 : Nat := 2497396860488509629844927

theorem tailTrace_4863663 : CollatzResearch.WordTrace tailWord_4863663 prefixEnd_4863663 2497396860488509629844927 := by
  unfold tailWord_4863663
  simp only [CollatzResearch.WordTrace]
  refine ⟨177392362978787073354283643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118261575319191382236189095 177392362978787073354283643)
  ·
    refine ⟨266088544468180610031425465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177392362978787073354283643 266088544468180610031425465)
    ·
      refine ⟨199566408351135457523569099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266088544468180610031425465 199566408351135457523569099)
      ·
        refine ⟨299349612526703186285353649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199566408351135457523569099 299349612526703186285353649)
        ·
          refine ⟨224512209395027389714015237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299349612526703186285353649 224512209395027389714015237)
          ·
            refine ⟨42096039261567635571377857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 224512209395027389714015237 42096039261567635571377857)
            ·
              refine ⟨31572029446175726678533393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42096039261567635571377857 31572029446175726678533393)
              ·
                refine ⟨23679022084631795008900045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31572029446175726678533393 23679022084631795008900045)
                ·
                  refine ⟨8879633281736923128337517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23679022084631795008900045 8879633281736923128337517)
                  ·
                    refine ⟨3329862480651346173126569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8879633281736923128337517 3329862480651346173126569)
                    ·
                      refine ⟨2497396860488509629844927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3329862480651346173126569 2497396860488509629844927)
                      ·
                        rfl

theorem cell23_4863663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 3, 2].length) (baseStart_4863663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863663 prefixEnd_4863663 := by exact prefixLift 4863663
  have htrace : WordTrace (prefixWord ++ tailWord_4863663) baseStart_4863663 baseEnd_4863663 := by
    simpa [prefixWord, tailWord_4863663, baseEnd_4863663] using wordTrace_append hprefix tailTrace_4863663
  have hstable : (prefixWord ++ tailWord_4863663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863663).length < 2 ^ (prefixWord ++ tailWord_4863663).sum := by decide
  have hdescent : baseEnd_4863663 < baseStart_4863663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863697 : List Nat := [1, 2, 2, 1, 2, 5, 3, 1, 1, 3, 2]
def baseStart_4863697 : Nat := 118140960795 + 4863697 * 2 ^ 59
def prefixEnd_4863697 : Nat := 4983230072969 + 3 ^ 40 * 4863697 * 2
def baseEnd_4863697 : Nat := 2497414318830762496819771

theorem tailTrace_4863697 : CollatzResearch.WordTrace tailWord_4863697 prefixEnd_4863697 2497414318830762496819771 := by
  unfold tailWord_4863697
  simp only [CollatzResearch.WordTrace]
  refine ⟨177393603060663897161021345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118262402040442598107347563 177393603060663897161021345)
  ·
    refine ⟨133045202295497922870766009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177393603060663897161021345 133045202295497922870766009)
    ·
      refine ⟨99783901721623442153074507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133045202295497922870766009 99783901721623442153074507)
      ·
        refine ⟨149675852582435163229611761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99783901721623442153074507 149675852582435163229611761)
        ·
          refine ⟨112256889436826372422208821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149675852582435163229611761 112256889436826372422208821)
          ·
            refine ⟨10524083384702472414582077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112256889436826372422208821 10524083384702472414582077)
            ·
              refine ⟨3946531269263427155468279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10524083384702472414582077 3946531269263427155468279)
              ·
                refine ⟨5919796903895140733202419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3946531269263427155468279 5919796903895140733202419)
                ·
                  refine ⟨8879695355842711099803629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5919796903895140733202419 8879695355842711099803629)
                  ·
                    refine ⟨3329885758441016662426361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8879695355842711099803629 3329885758441016662426361)
                    ·
                      refine ⟨2497414318830762496819771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3329885758441016662426361 2497414318830762496819771)
                      ·
                        rfl

theorem cell23_4863697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 1, 3, 2].length) (baseStart_4863697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863697 prefixEnd_4863697 := by exact prefixLift 4863697
  have htrace : WordTrace (prefixWord ++ tailWord_4863697) baseStart_4863697 baseEnd_4863697 := by
    simpa [prefixWord, tailWord_4863697, baseEnd_4863697] using wordTrace_append hprefix tailTrace_4863697
  have hstable : (prefixWord ++ tailWord_4863697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863697).length < 2 ^ (prefixWord ++ tailWord_4863697).sum := by decide
  have hdescent : baseEnd_4863697 < baseStart_4863697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863716 : List Nat := [2, 3, 1, 1, 1, 3, 2, 3, 7]
def baseStart_4863716 : Nat := 118140960795 + 4863716 * 2 ^ 59
def prefixEnd_4863716 : Nat := 4983230072969 + 3 ^ 40 * 4863716 * 2
def baseEnd_4863716 : Nat := 277491563884799769164687

theorem tailTrace_4863716 : CollatzResearch.WordTrace tailWord_4863716 prefixEnd_4863716 277491563884799769164687 := by
  unfold tailWord_4863716
  simp only [CollatzResearch.WordTrace]
  refine ⟨88697148023797531702981501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118262864031730042270642001 88697148023797531702981501)
  ·
    refine ⟨33261430508924074388618063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88697148023797531702981501 33261430508924074388618063)
    ·
      refine ⟨49892145763386111582927095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33261430508924074388618063 49892145763386111582927095)
      ·
        refine ⟨74838218645079167374390643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49892145763386111582927095 74838218645079167374390643)
        ·
          refine ⟨112257327967618751061585965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74838218645079167374390643 112257327967618751061585965)
          ·
            refine ⟨42096497987857031648094737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112257327967618751061585965 42096497987857031648094737)
            ·
              refine ⟨31572373490892773736071053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42096497987857031648094737 31572373490892773736071053)
              ·
                refine ⟨11839640059084790151026645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31572373490892773736071053 11839640059084790151026645)
                ·
                  refine ⟨277491563884799769164687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11839640059084790151026645 277491563884799769164687)
                  ·
                    rfl

theorem cell23_4863716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 7].length) (baseStart_4863716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863716 prefixEnd_4863716 := by exact prefixLift 4863716
  have htrace : WordTrace (prefixWord ++ tailWord_4863716) baseStart_4863716 baseEnd_4863716 := by
    simpa [prefixWord, tailWord_4863716, baseEnd_4863716] using wordTrace_append hprefix tailTrace_4863716
  have hstable : (prefixWord ++ tailWord_4863716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863716).length < 2 ^ (prefixWord ++ tailWord_4863716).sum := by decide
  have hdescent : baseEnd_4863716 < baseStart_4863716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863756 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 3, 2, 5]
def baseStart_4863756 : Nat := 118140960795 + 4863756 * 2 ^ 59
def prefixEnd_4863756 : Nat := 4983230072969 + 3 ^ 40 * 4863756 * 2
def baseEnd_4863756 : Nat := 2497444614189377765981999

theorem tailTrace_4863756 : CollatzResearch.WordTrace tailWord_4863756 prefixEnd_4863756 2497444614189377765981999 := by
  unfold tailWord_4863756
  simp only [CollatzResearch.WordTrace]
  refine ⟨88697877483725075118709561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118263836644966766824946081 88697877483725075118709561)
  ·
    refine ⟨66523408112793806339032171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88697877483725075118709561 66523408112793806339032171)
    ·
      refine ⟨99785112169190709508548257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66523408112793806339032171 99785112169190709508548257)
      ·
        refine ⟨74838834126893032131411193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99785112169190709508548257 74838834126893032131411193)
        ·
          refine ⟨56129125595169774098558395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74838834126893032131411193 56129125595169774098558395)
          ·
            refine ⟨84193688392754661147837593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56129125595169774098558395 84193688392754661147837593)
            ·
              refine ⟨63145266294565995860878195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84193688392754661147837593 63145266294565995860878195)
              ·
                refine ⟨94717899441848993791317293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63145266294565995860878195 94717899441848993791317293)
                ·
                  refine ⟨35519212290693372671743985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94717899441848993791317293 35519212290693372671743985)
                  ·
                    refine ⟨26639409218020029503807989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35519212290693372671743985 26639409218020029503807989)
                    ·
                      refine ⟨2497444614189377765981999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26639409218020029503807989 2497444614189377765981999)
                      ·
                        rfl

theorem cell23_4863756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_4863756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863756 prefixEnd_4863756 := by exact prefixLift 4863756
  have htrace : WordTrace (prefixWord ++ tailWord_4863756) baseStart_4863756 baseEnd_4863756 := by
    simpa [prefixWord, tailWord_4863756, baseEnd_4863756] using wordTrace_append hprefix tailTrace_4863756
  have hstable : (prefixWord ++ tailWord_4863756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863756).length < 2 ^ (prefixWord ++ tailWord_4863756).sum := by decide
  have hdescent : baseEnd_4863756 < baseStart_4863756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863840 : List Nat := [2, 1, 1, 3, 3, 2, 4, 1, 6]
def baseStart_4863840 : Nat := 118140960795 + 4863840 * 2 ^ 59
def prefixEnd_4863840 : Nat := 4983230072969 + 3 ^ 40 * 4863840 * 2
def baseEnd_4863840 : Nat := 277498638507150604147957

theorem tailTrace_4863840 : CollatzResearch.WordTrace tailWord_4863840 prefixEnd_4863840 277498638507150604147957 := by
  unfold tailWord_4863840
  simp only [CollatzResearch.WordTrace]
  refine ⟨88699409349572916291738487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118265879132763888388984649 88699409349572916291738487)
  ·
    refine ⟨133049114024359374437607731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88699409349572916291738487 133049114024359374437607731)
    ·
      refine ⟨199573671036539061656411597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133049114024359374437607731 199573671036539061656411597)
      ·
        refine ⟨74840126638702148121154349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199573671036539061656411597 74840126638702148121154349)
        ·
          refine ⟨28065047489513305545432881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74840126638702148121154349 28065047489513305545432881)
          ·
            refine ⟨21048785617134979159074661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28065047489513305545432881 21048785617134979159074661)
            ·
              refine ⟨3946647303212808592326499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21048785617134979159074661 3946647303212808592326499)
              ·
                refine ⟨5919970954819212888489749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3946647303212808592326499 5919970954819212888489749)
                ·
                  refine ⟨277498638507150604147957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5919970954819212888489749 277498638507150604147957)
                  ·
                    rfl

theorem cell23_4863840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 6].length) (baseStart_4863840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863840 prefixEnd_4863840 := by exact prefixLift 4863840
  have htrace : WordTrace (prefixWord ++ tailWord_4863840) baseStart_4863840 baseEnd_4863840 := by
    simpa [prefixWord, tailWord_4863840, baseEnd_4863840] using wordTrace_append hprefix tailTrace_4863840
  have hstable : (prefixWord ++ tailWord_4863840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863840).length < 2 ^ (prefixWord ++ tailWord_4863840).sum := by decide
  have hdescent : baseEnd_4863840 < baseStart_4863840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863867 : List Nat := [1, 1, 1, 1, 1, 5, 1, 7, 1, 1, 3]
def baseStart_4863867 : Nat := 118140960795 + 4863867 * 2 ^ 59
def prefixEnd_4863867 : Nat := 4983230072969 + 3 ^ 40 * 4863867 * 2
def baseEnd_4863867 : Nat := 2497501610542026831693989

theorem tailTrace_4863867 : CollatzResearch.WordTrace tailWord_4863867 prefixEnd_4863867 2497501610542026831693989 := by
  unfold tailWord_4863867
  simp only [CollatzResearch.WordTrace]
  refine ⟨177399803470048016194709855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118266535646698677463139903 177399803470048016194709855)
  ·
    refine ⟨266099705205072024292064783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177399803470048016194709855 266099705205072024292064783)
    ·
      refine ⟨399149557807608036438097175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266099705205072024292064783 399149557807608036438097175)
      ·
        refine ⟨598724336711412054657145763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399149557807608036438097175 598724336711412054657145763)
        ·
          refine ⟨898086505067118081985718645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 598724336711412054657145763 898086505067118081985718645)
          ·
            refine ⟨84195609850042320186161123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 898086505067118081985718645 84195609850042320186161123)
            ·
              refine ⟨126293414775063480279241685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84195609850042320186161123 126293414775063480279241685)
              ·
                refine ⟨2960001908790550319044727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 126293414775063480279241685 2960001908790550319044727)
                ·
                  refine ⟨4440002863185825478567091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2960001908790550319044727 4440002863185825478567091)
                  ·
                    refine ⟨6660004294778738217850637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4440002863185825478567091 6660004294778738217850637)
                    ·
                      refine ⟨2497501610542026831693989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6660004294778738217850637 2497501610542026831693989)
                      ·
                        rfl

theorem cell23_4863867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 1, 1, 3].length) (baseStart_4863867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863867 prefixEnd_4863867 := by exact prefixLift 4863867
  have htrace : WordTrace (prefixWord ++ tailWord_4863867) baseStart_4863867 baseEnd_4863867 := by
    simpa [prefixWord, tailWord_4863867, baseEnd_4863867] using wordTrace_append hprefix tailTrace_4863867
  have hstable : (prefixWord ++ tailWord_4863867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863867).length < 2 ^ (prefixWord ++ tailWord_4863867).sum := by decide
  have hdescent : baseEnd_4863867 < baseStart_4863867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863893 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_4863893 : Nat := 118140960795 + 4863893 * 2 ^ 59
def prefixEnd_4863893 : Nat := 4983230072969 + 3 ^ 40 * 4863893 * 2
def baseEnd_4863893 : Nat := 2497514961039043729968869

theorem tailTrace_4863893 : CollatzResearch.WordTrace tailWord_4863893 prefixEnd_4863893 2497514961039043729968869 := by
  unfold tailWord_4863893
  simp only [CollatzResearch.WordTrace]
  refine ⟨177400751767953822635156333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118267167845302548423437555 177400751767953822635156333)
  ·
    refine ⟨66525281912982683488183625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177400751767953822635156333 66525281912982683488183625)
    ·
      refine ⟨49893961434737012616137719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66525281912982683488183625 49893961434737012616137719)
      ·
        refine ⟨74840942152105518924206579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49893961434737012616137719 74840942152105518924206579)
        ·
          refine ⟨112261413228158278386309869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74840942152105518924206579 112261413228158278386309869)
          ·
            refine ⟨42098029960559354394866201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112261413228158278386309869 42098029960559354394866201)
            ·
              refine ⟨31573522470419515796149651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42098029960559354394866201 31573522470419515796149651)
              ·
                refine ⟨47360283705629273694224477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31573522470419515796149651 47360283705629273694224477)
                ·
                  refine ⟨17760106389610977635334179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47360283705629273694224477 17760106389610977635334179)
                  ·
                    refine ⟨26640159584416466453001269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17760106389610977635334179 26640159584416466453001269)
                    ·
                      refine ⟨2497514961039043729968869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26640159584416466453001269 2497514961039043729968869)
                      ·
                        rfl

theorem cell23_4863893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_4863893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863893 prefixEnd_4863893 := by exact prefixLift 4863893
  have htrace : WordTrace (prefixWord ++ tailWord_4863893) baseStart_4863893 baseEnd_4863893 := by
    simpa [prefixWord, tailWord_4863893, baseEnd_4863893] using wordTrace_append hprefix tailTrace_4863893
  have hstable : (prefixWord ++ tailWord_4863893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863893).length < 2 ^ (prefixWord ++ tailWord_4863893).sum := by decide
  have hdescent : baseEnd_4863893 < baseStart_4863893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863900 : List Nat := [2, 2, 3, 3, 1, 1, 1, 3, 1, 6]
def baseStart_4863900 : Nat := 118140960795 + 4863900 * 2 ^ 59
def prefixEnd_4863900 : Nat := 4983230072969 + 3 ^ 40 * 4863900 * 2
def baseEnd_4863900 : Nat := 832506185134541734193779

theorem tailTrace_4863900 : CollatzResearch.WordTrace tailWord_4863900 prefixEnd_4863900 832506185134541734193779 := by
  unfold tailWord_4863900
  simp only [CollatzResearch.WordTrace]
  refine ⟨88700503539464231415330577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118267338052618975220440769 88700503539464231415330577)
  ·
    refine ⟨66525377654598173561497933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88700503539464231415330577 66525377654598173561497933)
    ·
      refine ⟨24947016620474315085561725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66525377654598173561497933 24947016620474315085561725)
      ·
        refine ⟨9355131232677868157085647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24947016620474315085561725 9355131232677868157085647)
        ·
          refine ⟨14032696849016802235628471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9355131232677868157085647 14032696849016802235628471)
          ·
            refine ⟨21049045273525203353442707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14032696849016802235628471 21049045273525203353442707)
            ·
              refine ⟨31573567910287805030164061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21049045273525203353442707 31573567910287805030164061)
              ·
                refine ⟨11840087966357926886311523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31573567910287805030164061 11840087966357926886311523)
                ·
                  refine ⟨17760131949536890329467285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11840087966357926886311523 17760131949536890329467285)
                  ·
                    refine ⟨832506185134541734193779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17760131949536890329467285 832506185134541734193779)
                    ·
                      rfl

theorem cell23_4863900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_4863900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863900 prefixEnd_4863900 := by exact prefixLift 4863900
  have htrace : WordTrace (prefixWord ++ tailWord_4863900) baseStart_4863900 baseEnd_4863900 := by
    simpa [prefixWord, tailWord_4863900, baseEnd_4863900] using wordTrace_append hprefix tailTrace_4863900
  have hstable : (prefixWord ++ tailWord_4863900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863900).length < 2 ^ (prefixWord ++ tailWord_4863900).sum := by decide
  have hdescent : baseEnd_4863900 < baseStart_4863900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863934 : List Nat := [4, 2, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_4863934 : Nat := 118140960795 + 4863934 * 2 ^ 59
def prefixEnd_4863934 : Nat := 4983230072969 + 3 ^ 40 * 4863934 * 2
def baseEnd_4863934 : Nat := 832512004581959356518727

theorem tailTrace_4863934 : CollatzResearch.WordTrace tailWord_4863934 prefixEnd_4863934 832512004581959356518727 := by
  unfold tailWord_4863934
  simp only [CollatzResearch.WordTrace]
  refine ⟨22175280895100660829674857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118268164773870191091599237 22175280895100660829674857)
  ·
    refine ⟨16631460671325495622256143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22175280895100660829674857 16631460671325495622256143)
    ·
      refine ⟨24947191006988243433384215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16631460671325495622256143 24947191006988243433384215)
      ·
        refine ⟨37420786510482365150076323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24947191006988243433384215 37420786510482365150076323)
        ·
          refine ⟨56131179765723547725114485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37420786510482365150076323 56131179765723547725114485)
          ·
            refine ⟨5262298103036582599229483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56131179765723547725114485 5262298103036582599229483)
            ·
              refine ⟨7893447154554873898844225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5262298103036582599229483 7893447154554873898844225)
              ·
                refine ⟨5920085365916155424133169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7893447154554873898844225 5920085365916155424133169)
                ·
                  refine ⟨4440064024437116568099877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5920085365916155424133169 4440064024437116568099877)
                  ·
                    refine ⟨832512004581959356518727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4440064024437116568099877 832512004581959356518727)
                    ·
                      rfl

theorem cell23_4863934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_4863934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863934 prefixEnd_4863934 := by exact prefixLift 4863934
  have htrace : WordTrace (prefixWord ++ tailWord_4863934) baseStart_4863934 baseEnd_4863934 := by
    simpa [prefixWord, tailWord_4863934, baseEnd_4863934] using wordTrace_append hprefix tailTrace_4863934
  have hstable : (prefixWord ++ tailWord_4863934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863934).length < 2 ^ (prefixWord ++ tailWord_4863934).sum := by decide
  have hdescent : baseEnd_4863934 < baseStart_4863934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863954 : List Nat := [3, 2, 2, 3, 2, 2, 1, 1, 1, 2, 4]
def baseStart_4863954 : Nat := 118140960795 + 4863954 * 2 ^ 59
def prefixEnd_4863954 : Nat := 4983230072969 + 3 ^ 40 * 4863954 * 2
def baseEnd_4863954 : Nat := 2497546283358967991306089

theorem tailTrace_4863954 : CollatzResearch.WordTrace tailWord_4863954 prefixEnd_4863954 2497546283358967991306089 := by
  unfold tailWord_4863954
  simp only [CollatzResearch.WordTrace]
  refine ⟨44350744155183207513281729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118268651080488553368751277 44350744155183207513281729)
  ·
    refine ⟨33263058116387405634961297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44350744155183207513281729 33263058116387405634961297)
    ·
      refine ⟨24947293587290554226220973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33263058116387405634961297 24947293587290554226220973)
      ·
        refine ⟨9355235095233957834832865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24947293587290554226220973 9355235095233957834832865)
        ·
          refine ⟨7016426321425468376124649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9355235095233957834832865 7016426321425468376124649)
          ·
            refine ⟨5262319741069101282093487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7016426321425468376124649 5262319741069101282093487)
            ·
              refine ⟨7893479611603651923140231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5262319741069101282093487 7893479611603651923140231)
              ·
                refine ⟨11840219417405477884710347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7893479611603651923140231 11840219417405477884710347)
                ·
                  refine ⟨17760329126108216827065521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11840219417405477884710347 17760329126108216827065521)
                  ·
                    refine ⟨13320246844581162620299141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17760329126108216827065521 13320246844581162620299141)
                    ·
                      refine ⟨2497546283358967991306089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13320246844581162620299141 2497546283358967991306089)
                      ·
                        rfl

theorem cell23_4863954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_4863954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863954 prefixEnd_4863954 := by exact prefixLift 4863954
  have htrace : WordTrace (prefixWord ++ tailWord_4863954) baseStart_4863954 baseEnd_4863954 := by
    simpa [prefixWord, tailWord_4863954, baseEnd_4863954] using wordTrace_append hprefix tailTrace_4863954
  have hstable : (prefixWord ++ tailWord_4863954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863954).length < 2 ^ (prefixWord ++ tailWord_4863954).sum := by decide
  have hdescent : baseEnd_4863954 < baseStart_4863954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863957 : List Nat := [1, 3, 2, 3, 2, 1, 3, 1, 1, 3, 3]
def baseStart_4863957 : Nat := 118140960795 + 4863957 * 2 ^ 59
def prefixEnd_4863957 : Nat := 4983230072969 + 3 ^ 40 * 4863957 * 2
def baseEnd_4863957 : Nat := 2497547823800931479568575

theorem tailTrace_4863957 : CollatzResearch.WordTrace tailWord_4863957 prefixEnd_4863957 2497547823800931479568575 := by
  unfold tailWord_4863957
  simp only [CollatzResearch.WordTrace]
  refine ⟨177403086039721961565486125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118268724026481307710324083 177403086039721961565486125)
  ·
    refine ⟨66526157264895735587057297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177403086039721961565486125 66526157264895735587057297)
    ·
      refine ⟨49894617948671801690292973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66526157264895735587057297 49894617948671801690292973)
      ·
        refine ⟨18710481730751925633859865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49894617948671801690292973 18710481730751925633859865)
        ·
          refine ⟨14032861298063944225394899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18710481730751925633859865 14032861298063944225394899)
          ·
            refine ⟨21049291947095916338092349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14032861298063944225394899 21049291947095916338092349)
            ·
              refine ⟨7893484480160968626784631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21049291947095916338092349 7893484480160968626784631)
              ·
                refine ⟨11840226720241452940176947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7893484480160968626784631 11840226720241452940176947)
                ·
                  refine ⟨17760340080362179410265421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11840226720241452940176947 17760340080362179410265421)
                  ·
                    refine ⟨6660127530135817278849533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17760340080362179410265421 6660127530135817278849533)
                    ·
                      refine ⟨2497547823800931479568575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6660127530135817278849533 2497547823800931479568575)
                      ·
                        rfl

theorem cell23_4863957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_4863957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863957 prefixEnd_4863957 := by exact prefixLift 4863957
  have htrace : WordTrace (prefixWord ++ tailWord_4863957) baseStart_4863957 baseEnd_4863957 := by
    simpa [prefixWord, tailWord_4863957, baseEnd_4863957] using wordTrace_append hprefix tailTrace_4863957
  have hstable : (prefixWord ++ tailWord_4863957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863957).length < 2 ^ (prefixWord ++ tailWord_4863957).sum := by decide
  have hdescent : baseEnd_4863957 < baseStart_4863957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863964 : List Nat := [2, 2, 6, 1, 1, 1, 1, 9]
def baseStart_4863964 : Nat := 118140960795 + 4863964 * 2 ^ 59
def prefixEnd_4863964 : Nat := 4983230072969 + 3 ^ 40 * 4863964 * 2
def baseEnd_4863964 : Nat := 92501904376500479710409

theorem tailTrace_4863964 : CollatzResearch.WordTrace tailWord_4863964 prefixEnd_4863964 92501904376500479710409 := by
  unfold tailWord_4863964
  simp only [CollatzResearch.WordTrace]
  refine ⟨88701670675348300880495473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118268894233797734507327297 88701670675348300880495473)
  ·
    refine ⟨66526253006511225660371605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88701670675348300880495473 66526253006511225660371605)
    ·
      refine ⟨3118418109680213702829919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 66526253006511225660371605 3118418109680213702829919)
      ·
        refine ⟨4677627164520320554244879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3118418109680213702829919 4677627164520320554244879)
        ·
          refine ⟨7016440746780480831367319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4677627164520320554244879 7016440746780480831367319)
          ·
            refine ⟨10524661120170721247050979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7016440746780480831367319 10524661120170721247050979)
            ·
              refine ⟨15786991680256081870576469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10524661120170721247050979 15786991680256081870576469)
              ·
                refine ⟨92501904376500479710409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15786991680256081870576469 92501904376500479710409)
                ·
                  rfl

theorem cell23_4863964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 9].length) (baseStart_4863964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863964 prefixEnd_4863964 := by exact prefixLift 4863964
  have htrace : WordTrace (prefixWord ++ tailWord_4863964) baseStart_4863964 baseEnd_4863964 := by
    simpa [prefixWord, tailWord_4863964, baseEnd_4863964] using wordTrace_append hprefix tailTrace_4863964
  have hstable : (prefixWord ++ tailWord_4863964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863964).length < 2 ^ (prefixWord ++ tailWord_4863964).sum := by decide
  have hdescent : baseEnd_4863964 < baseStart_4863964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4863975 : List Nat := [1, 1, 5, 2, 4, 1, 1, 3, 1, 2, 2]
def baseStart_4863975 : Nat := 118140960795 + 4863975 * 2 ^ 59
def prefixEnd_4863975 : Nat := 4983230072969 + 3 ^ 40 * 4863975 * 2
def baseEnd_4863975 : Nat := 2497557066452712409143493

theorem tailTrace_4863975 : CollatzResearch.WordTrace tailWord_4863975 prefixEnd_4863975 2497557066452712409143493 := by
  unfold tailWord_4863975
  simp only [CollatzResearch.WordTrace]
  refine ⟨177403742553656750639641379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118269161702437833759760919 177403742553656750639641379)
  ·
    refine ⟨266105613830485125959462069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177403742553656750639641379 266105613830485125959462069)
    ·
      refine ⟨24947401296607980558699569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 266105613830485125959462069 24947401296607980558699569)
      ·
        refine ⟨18710550972455985419024677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24947401296607980558699569 18710550972455985419024677)
        ·
          refine ⟨3508228307335497266067127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18710550972455985419024677 3508228307335497266067127)
          ·
            refine ⟨5262342461003245899100691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3508228307335497266067127 5262342461003245899100691)
            ·
              refine ⟨7893513691504868848651037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5262342461003245899100691 7893513691504868848651037)
              ·
                refine ⟨2960067634314325818244139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7893513691504868848651037 2960067634314325818244139)
                ·
                  refine ⟨4440101451471488727366209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2960067634314325818244139 4440101451471488727366209)
                  ·
                    refine ⟨3330076088603616545524657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4440101451471488727366209 3330076088603616545524657)
                    ·
                      refine ⟨2497557066452712409143493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3330076088603616545524657 2497557066452712409143493)
                      ·
                        rfl

theorem cell23_4863975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_4863975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4863975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4863975 prefixEnd_4863975 := by exact prefixLift 4863975
  have htrace : WordTrace (prefixWord ++ tailWord_4863975) baseStart_4863975 baseEnd_4863975 := by
    simpa [prefixWord, tailWord_4863975, baseEnd_4863975] using wordTrace_append hprefix tailTrace_4863975
  have hstable : (prefixWord ++ tailWord_4863975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4863975).length < 2 ^ (prefixWord ++ tailWord_4863975).sum := by decide
  have hdescent : baseEnd_4863975 < baseStart_4863975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4863975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864054 : List Nat := [5, 1, 2, 1, 1, 1, 3, 4, 5]
def baseStart_4864054 : Nat := 118140960795 + 4864054 * 2 ^ 59
def prefixEnd_4864054 : Nat := 4983230072969 + 3 ^ 40 * 4864054 * 2
def baseEnd_4864054 : Nat := 277510847936046400006181

theorem tailTrace_4864054 : CollatzResearch.WordTrace tailWord_4864054 prefixEnd_4864054 277510847936046400006181 := by
  unfold tailWord_4864054
  simp only [CollatzResearch.WordTrace]
  refine ⟨11087913995023159195735451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118271082613580364754511477 11087913995023159195735451)
  ·
    refine ⟨16631870992534738793603177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11087913995023159195735451 16631870992534738793603177)
    ·
      refine ⟨12473903244401054095202383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16631870992534738793603177 12473903244401054095202383)
      ·
        refine ⟨18710854866601581142803575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12473903244401054095202383 18710854866601581142803575)
        ·
          refine ⟨28066282299902371714205363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18710854866601581142803575 28066282299902371714205363)
          ·
            refine ⟨42099423449853557571308045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28066282299902371714205363 42099423449853557571308045)
            ·
              refine ⟨15787283793695084089240517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42099423449853557571308045 15787283793695084089240517)
              ·
                refine ⟨2960115711317828266732597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15787283793695084089240517 2960115711317828266732597)
                ·
                  refine ⟨277510847936046400006181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2960115711317828266732597 277510847936046400006181)
                  ·
                    rfl

theorem cell23_4864054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_4864054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864054 prefixEnd_4864054 := by exact prefixLift 4864054
  have htrace : WordTrace (prefixWord ++ tailWord_4864054) baseStart_4864054 baseEnd_4864054 := by
    simpa [prefixWord, tailWord_4864054, baseEnd_4864054] using wordTrace_append hprefix tailTrace_4864054
  have hstable : (prefixWord ++ tailWord_4864054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864054).length < 2 ^ (prefixWord ++ tailWord_4864054).sum := by decide
  have hdescent : baseEnd_4864054 < baseStart_4864054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864060 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 1, 2, 5]
def baseStart_4864060 : Nat := 118140960795 + 4864060 * 2 ^ 59
def prefixEnd_4864060 : Nat := 4983230072969 + 3 ^ 40 * 4864060 * 2
def baseEnd_4864060 : Nat := 2497600712308344576580601

theorem tailTrace_4864060 : CollatzResearch.WordTrace tailWord_4864060 prefixEnd_4864060 2497600712308344576580601 := by
  unfold tailWord_4864060
  simp only [CollatzResearch.WordTrace]
  refine ⟨88703421379174405078242817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118271228505565873437657089 88703421379174405078242817)
  ·
    refine ⟨66527566034380803808682113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88703421379174405078242817 66527566034380803808682113)
    ·
      refine ⟨49895674525785602856511585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66527566034380803808682113 49895674525785602856511585)
      ·
        refine ⟨37421755894339202142383689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49895674525785602856511585 37421755894339202142383689)
        ·
          refine ⟨28066316920754401606787767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37421755894339202142383689 28066316920754401606787767)
          ·
            refine ⟨42099475381131602410181651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28066316920754401606787767 42099475381131602410181651)
            ·
              refine ⟨63149213071697403615272477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42099475381131602410181651 63149213071697403615272477)
              ·
                refine ⟨23680954901886526355727179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63149213071697403615272477 23680954901886526355727179)
                ·
                  refine ⟨35521432352829789533590769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23680954901886526355727179 35521432352829789533590769)
                  ·
                    refine ⟨26641074264622342150193077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35521432352829789533590769 26641074264622342150193077)
                    ·
                      refine ⟨2497600712308344576580601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26641074264622342150193077 2497600712308344576580601)
                      ·
                        rfl

theorem cell23_4864060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_4864060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864060 prefixEnd_4864060 := by exact prefixLift 4864060
  have htrace : WordTrace (prefixWord ++ tailWord_4864060) baseStart_4864060 baseEnd_4864060 := by
    simpa [prefixWord, tailWord_4864060, baseEnd_4864060] using wordTrace_append hprefix tailTrace_4864060
  have hstable : (prefixWord ++ tailWord_4864060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864060).length < 2 ^ (prefixWord ++ tailWord_4864060).sum := by decide
  have hdescent : baseEnd_4864060 < baseStart_4864060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864087 : List Nat := [1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 4]
def baseStart_4864087 : Nat := 118140960795 + 4864087 * 2 ^ 59
def prefixEnd_4864087 : Nat := 4983230072969 + 3 ^ 40 * 4864087 * 2
def baseEnd_4864087 : Nat := 2497614576286015970942977

theorem tailTrace_4864087 : CollatzResearch.WordTrace tailWord_4864087 prefixEnd_4864087 2497614576286015970942977 := by
  unfold tailWord_4864087
  simp only [CollatzResearch.WordTrace]
  refine ⟨177407827529250993767718515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118271885019500662511812343 177407827529250993767718515)
  ·
    refine ⟨266111741293876490651577773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177407827529250993767718515 266111741293876490651577773)
    ·
      refine ⟨99791902985203683994341665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266111741293876490651577773 99791902985203683994341665)
      ·
        refine ⟨74843927238902762995756249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99791902985203683994341665 74843927238902762995756249)
        ·
          refine ⟨56132945429177072246817187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74843927238902762995756249 56132945429177072246817187)
          ·
            refine ⟨84199418143765608370225781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56132945429177072246817187 84199418143765608370225781)
            ·
              refine ⟨7893695450978025784708667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84199418143765608370225781 7893695450978025784708667)
              ·
                refine ⟨11840543176467038677063001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7893695450978025784708667 11840543176467038677063001)
                ·
                  refine ⟨8880407382350279007797251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11840543176467038677063001 8880407382350279007797251)
                  ·
                    refine ⟨13320611073525418511695877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8880407382350279007797251 13320611073525418511695877)
                    ·
                      refine ⟨2497614576286015970942977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13320611073525418511695877 2497614576286015970942977)
                      ·
                        rfl

theorem cell23_4864087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_4864087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864087 prefixEnd_4864087 := by exact prefixLift 4864087
  have htrace : WordTrace (prefixWord ++ tailWord_4864087) baseStart_4864087 baseEnd_4864087 := by
    simpa [prefixWord, tailWord_4864087, baseEnd_4864087] using wordTrace_append hprefix tailTrace_4864087
  have hstable : (prefixWord ++ tailWord_4864087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864087).length < 2 ^ (prefixWord ++ tailWord_4864087).sum := by decide
  have hdescent : baseEnd_4864087 < baseStart_4864087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864100 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 2, 1, 6]
def baseStart_4864100 : Nat := 118140960795 + 4864100 * 2 ^ 59
def prefixEnd_4864100 : Nat := 4983230072969 + 3 ^ 40 * 4864100 * 2
def baseEnd_4864100 : Nat := 2497621251534524420080417

theorem tailTrace_4864100 : CollatzResearch.WordTrace tailWord_4864100 prefixEnd_4864100 2497621251534524420080417 := by
  unfold tailWord_4864100
  simp only [CollatzResearch.WordTrace]
  refine ⟨88704150839101948493970877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118272201118802597991961169 88704150839101948493970877)
  ·
    refine ⟨33264056564663230685239079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88704150839101948493970877 33264056564663230685239079)
    ·
      refine ⟨49896084846994846027858619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33264056564663230685239079 49896084846994846027858619)
      ·
        refine ⟨74844127270492269041787929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49896084846994846027858619 74844127270492269041787929)
        ·
          refine ⟨56133095452869201781340947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74844127270492269041787929 56133095452869201781340947)
          ·
            refine ⟨84199643179303802672011421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56133095452869201781340947 84199643179303802672011421)
            ·
              refine ⟨31574866192238926002004283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84199643179303802672011421 31574866192238926002004283)
              ·
                refine ⟨47362299288358389003006425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31574866192238926002004283 47362299288358389003006425)
                ·
                  refine ⟨35521724466268791752254819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47362299288358389003006425 35521724466268791752254819)
                  ·
                    refine ⟨53282586699403187628382229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35521724466268791752254819 53282586699403187628382229)
                    ·
                      refine ⟨2497621251534524420080417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53282586699403187628382229 2497621251534524420080417)
                      ·
                        rfl

theorem cell23_4864100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_4864100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864100 prefixEnd_4864100 := by exact prefixLift 4864100
  have htrace : WordTrace (prefixWord ++ tailWord_4864100) baseStart_4864100 baseEnd_4864100 := by
    simpa [prefixWord, tailWord_4864100, baseEnd_4864100] using wordTrace_append hprefix tailTrace_4864100
  have hstable : (prefixWord ++ tailWord_4864100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864100).length < 2 ^ (prefixWord ++ tailWord_4864100).sum := by decide
  have hdescent : baseEnd_4864100 < baseStart_4864100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864114 : List Nat := [3, 2, 1, 2, 2, 3, 2, 1, 3, 4]
def baseStart_4864114 : Nat := 118140960795 + 4864114 * 2 ^ 59
def prefixEnd_4864114 : Nat := 4983230072969 + 3 ^ 40 * 4864114 * 2
def baseEnd_4864114 : Nat := 832542813421229121768451

theorem tailTrace_4864114 : CollatzResearch.WordTrace tailWord_4864114 prefixEnd_4864114 832542813421229121768451 := by
  unfold tailWord_4864114
  simp only [CollatzResearch.WordTrace]
  refine ⟨44352203075038294344737849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118272541533435451585967597 44352203075038294344737849)
  ·
    refine ⟨33264152306278720758553387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44352203075038294344737849 33264152306278720758553387)
    ·
      refine ⟨49896228459418081137830081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33264152306278720758553387 49896228459418081137830081)
      ·
        refine ⟨37422171344563560853372561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49896228459418081137830081 37422171344563560853372561)
        ·
          refine ⟨28066628508422670640029421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37422171344563560853372561 28066628508422670640029421)
          ·
            refine ⟨10524985690658501490011033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28066628508422670640029421 10524985690658501490011033)
            ·
              refine ⟨7893739267993876117508275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10524985690658501490011033 7893739267993876117508275)
              ·
                refine ⟨11840608901990814176262413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7893739267993876117508275 11840608901990814176262413)
                ·
                  refine ⟨4440228338246555316098405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11840608901990814176262413 4440228338246555316098405)
                  ·
                    refine ⟨832542813421229121768451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4440228338246555316098405 832542813421229121768451)
                    ·
                      rfl

theorem cell23_4864114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_4864114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864114 prefixEnd_4864114 := by exact prefixLift 4864114
  have htrace : WordTrace (prefixWord ++ tailWord_4864114) baseStart_4864114 baseEnd_4864114 := by
    simpa [prefixWord, tailWord_4864114, baseEnd_4864114] using wordTrace_append hprefix tailTrace_4864114
  have hstable : (prefixWord ++ tailWord_4864114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864114).length < 2 ^ (prefixWord ++ tailWord_4864114).sum := by decide
  have hdescent : baseEnd_4864114 < baseStart_4864114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864207 : List Nat := [1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 4]
def baseStart_4864207 : Nat := 118140960795 + 4864207 * 2 ^ 59
def prefixEnd_4864207 : Nat := 4983230072969 + 3 ^ 40 * 4864207 * 2
def baseEnd_4864207 : Nat := 2497676193964555501442425

theorem tailTrace_4864207 : CollatzResearch.WordTrace tailWord_4864207 prefixEnd_4864207 2497676193964555501442425 := by
  unfold tailWord_4864207
  simp only [CollatzResearch.WordTrace]
  refine ⟨177412204288816254262086875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118274802859210836174724583 177412204288816254262086875)
  ·
    refine ⟨266118306433224381393130313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177412204288816254262086875 266118306433224381393130313)
    ·
      refine ⟨199588729824918286044847735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266118306433224381393130313 199588729824918286044847735)
      ·
        refine ⟨299383094737377429067271603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199588729824918286044847735 299383094737377429067271603)
        ·
          refine ⟨449074642106066143600907405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299383094737377429067271603 449074642106066143600907405)
          ·
            refine ⟨168402990789774803850340277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 449074642106066143600907405 168402990789774803850340277)
            ·
              refine ⟨15787780386541387860969401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 168402990789774803850340277 15787780386541387860969401)
              ·
                refine ⟨11840835289906040895727051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15787780386541387860969401 11840835289906040895727051)
                ·
                  refine ⟨17761252934859061343590577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11840835289906040895727051 17761252934859061343590577)
                  ·
                    refine ⟨13320939701144296007692933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17761252934859061343590577 13320939701144296007692933)
                    ·
                      refine ⟨2497676193964555501442425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13320939701144296007692933 2497676193964555501442425)
                      ·
                        rfl

theorem cell23_4864207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 4].length) (baseStart_4864207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864207 prefixEnd_4864207 := by exact prefixLift 4864207
  have htrace : WordTrace (prefixWord ++ tailWord_4864207) baseStart_4864207 baseEnd_4864207 := by
    simpa [prefixWord, tailWord_4864207, baseEnd_4864207] using wordTrace_append hprefix tailTrace_4864207
  have hstable : (prefixWord ++ tailWord_4864207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864207).length < 2 ^ (prefixWord ++ tailWord_4864207).sum := by decide
  have hdescent : baseEnd_4864207 < baseStart_4864207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864221 : List Nat := [1, 4, 3, 2, 1, 1, 1, 4, 2, 4]
def baseStart_4864221 : Nat := 118140960795 + 4864221 * 2 ^ 59
def prefixEnd_4864221 : Nat := 4983230072969 + 3 ^ 40 * 4864221 * 2
def baseEnd_4864221 : Nat := 832561127564572815555787

theorem tailTrace_4864221 : CollatzResearch.WordTrace tailWord_4864221 prefixEnd_4864221 832561127564572815555787 := by
  unfold tailWord_4864221
  simp only [CollatzResearch.WordTrace]
  refine ⟨177412714910765534653096517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118275143273843689768731011 177412714910765534653096517)
  ·
    refine ⟨33264884045768537747455597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177412714910765534653096517 33264884045768537747455597)
    ·
      refine ⟨12474331517163201655295849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33264884045768537747455597 12474331517163201655295849)
      ·
        refine ⟨9355748637872401241471887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12474331517163201655295849 9355748637872401241471887)
        ·
          refine ⟨14033622956808601862207831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9355748637872401241471887 14033622956808601862207831)
          ·
            refine ⟨21050434435212902793311747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14033622956808601862207831 21050434435212902793311747)
            ·
              refine ⟨31575651652819354189967621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21050434435212902793311747 31575651652819354189967621)
              ·
                refine ⟨5920434684903628910618929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31575651652819354189967621 5920434684903628910618929)
                ·
                  refine ⟨4440326013677721682964197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5920434684903628910618929 4440326013677721682964197)
                  ·
                    refine ⟨832561127564572815555787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4440326013677721682964197 832561127564572815555787)
                    ·
                      rfl

theorem cell23_4864221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_4864221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864221 prefixEnd_4864221 := by exact prefixLift 4864221
  have htrace : WordTrace (prefixWord ++ tailWord_4864221) baseStart_4864221 baseEnd_4864221 := by
    simpa [prefixWord, tailWord_4864221, baseEnd_4864221] using wordTrace_append hprefix tailTrace_4864221
  have hstable : (prefixWord ++ tailWord_4864221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864221).length < 2 ^ (prefixWord ++ tailWord_4864221).sum := by decide
  have hdescent : baseEnd_4864221 < baseStart_4864221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864257 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_4864257 : Nat := 118140960795 + 4864257 * 2 ^ 59
def prefixEnd_4864257 : Nat := 4983230072969 + 3 ^ 40 * 4864257 * 2
def baseEnd_4864257 : Nat := 2497701867997280305817195

theorem tailTrace_4864257 : CollatzResearch.WordTrace tailWord_4864257 prefixEnd_4864257 2497701867997280305817195 := by
  unfold tailWord_4864257
  simp only [CollatzResearch.WordTrace]
  refine ⟨177414027938635112801407025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118276018625756741867604683 177414027938635112801407025)
  ·
    refine ⟨133060520953976334601055269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177414027938635112801407025 133060520953976334601055269)
    ·
      refine ⟨24948847678870562737697863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133060520953976334601055269 24948847678870562737697863)
      ·
        refine ⟨37423271518305844106546795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24948847678870562737697863 37423271518305844106546795)
        ·
          refine ⟨56134907277458766159820193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37423271518305844106546795 56134907277458766159820193)
          ·
            refine ⟨42101180458094074619865145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56134907277458766159820193 42101180458094074619865145)
            ·
              refine ⟨31575885343570555964898859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42101180458094074619865145 31575885343570555964898859)
              ·
                refine ⟨47363828015355833947348289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31575885343570555964898859 47363828015355833947348289)
                ·
                  refine ⟨35522871011516875460511217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47363828015355833947348289 35522871011516875460511217)
                  ·
                    refine ⟨26642153258637656595383413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35522871011516875460511217 26642153258637656595383413)
                    ·
                      refine ⟨2497701867997280305817195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26642153258637656595383413 2497701867997280305817195)
                      ·
                        rfl

theorem cell23_4864257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_4864257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864257 prefixEnd_4864257 := by exact prefixLift 4864257
  have htrace : WordTrace (prefixWord ++ tailWord_4864257) baseStart_4864257 baseEnd_4864257 := by
    simpa [prefixWord, tailWord_4864257, baseEnd_4864257] using wordTrace_append hprefix tailTrace_4864257
  have hstable : (prefixWord ++ tailWord_4864257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864257).length < 2 ^ (prefixWord ++ tailWord_4864257).sum := by decide
  have hdescent : baseEnd_4864257 < baseStart_4864257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864277 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 2, 6]
def baseStart_4864277 : Nat := 118140960795 + 4864277 * 2 ^ 59
def prefixEnd_4864277 : Nat := 4983230072969 + 3 ^ 40 * 4864277 * 2
def baseEnd_4864277 : Nat := 832570712536790075855701

theorem tailTrace_4864277 : CollatzResearch.WordTrace tailWord_4864277 prefixEnd_4864277 832570712536790075855701 := by
  unfold tailWord_4864277
  simp only [CollatzResearch.WordTrace]
  refine ⟨177414757398562656217135085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118276504932375104144756723 177414757398562656217135085)
  ·
    refine ⟨66530534024460996081425657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177414757398562656217135085 66530534024460996081425657)
    ·
      refine ⟨49897900518345747061069243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66530534024460996081425657 49897900518345747061069243)
      ·
        refine ⟨74846850777518620591603865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49897900518345747061069243 74846850777518620591603865)
        ·
          refine ⟨56135138083138965443702899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74846850777518620591603865 56135138083138965443702899)
          ·
            refine ⟨84202707124708448165554349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56135138083138965443702899 84202707124708448165554349)
            ·
              refine ⟨31576015171765668062082881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84202707124708448165554349 31576015171765668062082881)
              ·
                refine ⟨23682011378824251046562161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31576015171765668062082881 23682011378824251046562161)
                ·
                  refine ⟨17761508534118188284921621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23682011378824251046562161 17761508534118188284921621)
                  ·
                    refine ⟨832570712536790075855701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17761508534118188284921621 832570712536790075855701)
                    ·
                      rfl

theorem cell23_4864277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_4864277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864277 prefixEnd_4864277 := by exact prefixLift 4864277
  have htrace : WordTrace (prefixWord ++ tailWord_4864277) baseStart_4864277 baseEnd_4864277 := by
    simpa [prefixWord, tailWord_4864277, baseEnd_4864277] using wordTrace_append hprefix tailTrace_4864277
  have hstable : (prefixWord ++ tailWord_4864277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864277).length < 2 ^ (prefixWord ++ tailWord_4864277).sum := by decide
  have hdescent : baseEnd_4864277 < baseStart_4864277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864307 : List Nat := [1, 1, 1, 2, 5, 1, 1, 4, 7]
def baseStart_4864307 : Nat := 118140960795 + 4864307 * 2 ^ 59
def prefixEnd_4864307 : Nat := 4983230072969 + 3 ^ 40 * 4864307 * 2
def baseEnd_4864307 : Nat := 277525282447778345576885

theorem tailTrace_4864307 : CollatzResearch.WordTrace tailWord_4864307 prefixEnd_4864307 277525282447778345576885 := by
  unfold tailWord_4864307
  simp only [CollatzResearch.WordTrace]
  refine ⟨177415851588453971340727175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118277234392302647560484783 177415851588453971340727175)
  ·
    refine ⟨266123777382680957011090763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177415851588453971340727175 266123777382680957011090763)
    ·
      refine ⟨399185666074021435516636145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266123777382680957011090763 399185666074021435516636145)
      ·
        refine ⟨299389249555516076637477109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 399185666074021435516636145 299389249555516076637477109)
        ·
          refine ⟨28067742145829632184763479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 299389249555516076637477109 28067742145829632184763479)
          ·
            refine ⟨42101613218744448277145219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28067742145829632184763479 42101613218744448277145219)
            ·
              refine ⟨63152419828116672415717829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42101613218744448277145219 63152419828116672415717829)
              ·
                refine ⟨11841078717771876077947093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63152419828116672415717829 11841078717771876077947093)
                ·
                  refine ⟨277525282447778345576885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11841078717771876077947093 277525282447778345576885)
                  ·
                    rfl

theorem cell23_4864307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 7].length) (baseStart_4864307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864307 prefixEnd_4864307 := by exact prefixLift 4864307
  have htrace : WordTrace (prefixWord ++ tailWord_4864307) baseStart_4864307 baseEnd_4864307 := by
    simpa [prefixWord, tailWord_4864307, baseEnd_4864307] using wordTrace_append hprefix tailTrace_4864307
  have hstable : (prefixWord ++ tailWord_4864307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864307).length < 2 ^ (prefixWord ++ tailWord_4864307).sum := by decide
  have hdescent : baseEnd_4864307 < baseStart_4864307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864318 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 4, 2, 2]
def baseStart_4864318 : Nat := 118140960795 + 4864318 * 2 ^ 59
def prefixEnd_4864318 : Nat := 4983230072969 + 3 ^ 40 * 4864318 * 2
def baseEnd_4864318 : Nat := 2497733190317204567154415

theorem tailTrace_4864318 : CollatzResearch.WordTrace tailWord_4864318 prefixEnd_4864318 2497733190317204567154415 := by
  unfold tailWord_4864318
  simp only [CollatzResearch.WordTrace]
  refine ⟨22177031598926765027422201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118277501860942746812918405 22177031598926765027422201)
  ·
    refine ⟨16632773699195073770566651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22177031598926765027422201 16632773699195073770566651)
    ·
      refine ⟨24949160548792610655849977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16632773699195073770566651 24949160548792610655849977)
      ·
        refine ⟨18711870411594457991887483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24949160548792610655849977 18711870411594457991887483)
        ·
          refine ⟨28067805617391686987831225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18711870411594457991887483 28067805617391686987831225)
          ·
            refine ⟨21050854213043765240873419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28067805617391686987831225 21050854213043765240873419)
            ·
              refine ⟨31576281319565647861310129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21050854213043765240873419 31576281319565647861310129)
              ·
                refine ⟨23682210989674235895982597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31576281319565647861310129 23682210989674235895982597)
                ·
                  refine ⟨4440414560563919230496737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23682210989674235895982597 4440414560563919230496737)
                  ·
                    refine ⟨3330310920422939422872553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4440414560563919230496737 3330310920422939422872553)
                    ·
                      refine ⟨2497733190317204567154415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3330310920422939422872553 2497733190317204567154415)
                      ·
                        rfl

theorem cell23_4864318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_4864318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864318 prefixEnd_4864318 := by exact prefixLift 4864318
  have htrace : WordTrace (prefixWord ++ tailWord_4864318) baseStart_4864318 baseEnd_4864318 := by
    simpa [prefixWord, tailWord_4864318, baseEnd_4864318] using wordTrace_append hprefix tailTrace_4864318
  have hstable : (prefixWord ++ tailWord_4864318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864318).length < 2 ^ (prefixWord ++ tailWord_4864318).sum := by decide
  have hdescent : baseEnd_4864318 < baseStart_4864318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864321 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_4864321 : Nat := 118140960795 + 4864321 * 2 ^ 59
def prefixEnd_4864321 : Nat := 4983230072969 + 3 ^ 40 * 4864321 * 2
def baseEnd_4864321 : Nat := 2497734730759168055416901

theorem tailTrace_4864321 : CollatzResearch.WordTrace tailWord_4864321 prefixEnd_4864321 2497734730759168055416901 := by
  unfold tailWord_4864321
  simp only [CollatzResearch.WordTrace]
  refine ⟨177416362210403251731736817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118277574806935501154491211 177416362210403251731736817)
  ·
    refine ⟨133062271657802438798802613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177416362210403251731736817 133062271657802438798802613)
    ·
      refine ⟨12474587967918978637387745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133062271657802438798802613 12474587967918978637387745)
      ·
        refine ⟨9355940975939233978040809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12474587967918978637387745 9355940975939233978040809)
        ·
          refine ⟨7016955731954425483530607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9355940975939233978040809 7016955731954425483530607)
          ·
            refine ⟨10525433597931638225295911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7016955731954425483530607 10525433597931638225295911)
            ·
              refine ⟨15788150396897457337943867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10525433597931638225295911 15788150396897457337943867)
              ·
                refine ⟨23682225595346186006915801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15788150396897457337943867 23682225595346186006915801)
                ·
                  refine ⟨17761669196509639505186851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23682225595346186006915801 17761669196509639505186851)
                  ·
                    refine ⟨26642503794764459257780277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17761669196509639505186851 26642503794764459257780277)
                    ·
                      refine ⟨2497734730759168055416901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26642503794764459257780277 2497734730759168055416901)
                      ·
                        rfl

theorem cell23_4864321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_4864321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864321 prefixEnd_4864321 := by exact prefixLift 4864321
  have htrace : WordTrace (prefixWord ++ tailWord_4864321) baseStart_4864321 baseEnd_4864321 := by
    simpa [prefixWord, tailWord_4864321, baseEnd_4864321] using wordTrace_append hprefix tailTrace_4864321
  have hstable : (prefixWord ++ tailWord_4864321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864321).length < 2 ^ (prefixWord ++ tailWord_4864321).sum := by decide
  have hdescent : baseEnd_4864321 < baseStart_4864321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864334 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3]
def baseStart_4864334 : Nat := 118140960795 + 4864334 * 2 ^ 59
def prefixEnd_4864334 : Nat := 4983230072969 + 3 ^ 40 * 4864334 * 2
def baseEnd_4864334 : Nat := 2497741406007676504554341

theorem tailTrace_4864334 : CollatzResearch.WordTrace tailWord_4864334 prefixEnd_4864334 2497741406007676504554341 := by
  unfold tailWord_4864334
  simp only [CollatzResearch.WordTrace]
  refine ⟨22177104544919519368995007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118277890906237436634640037 22177104544919519368995007)
  ·
    refine ⟨33265656817379279053492511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22177104544919519368995007 33265656817379279053492511)
    ·
      refine ⟨49898485226068918580238767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33265656817379279053492511 49898485226068918580238767)
      ·
        refine ⟨74847727839103377870358151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49898485226068918580238767 74847727839103377870358151)
        ·
          refine ⟨112271591758655066805537227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74847727839103377870358151 112271591758655066805537227)
          ·
            refine ⟨168407387637982600208305841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112271591758655066805537227 168407387637982600208305841)
            ·
              refine ⟨126305540728486950156229381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168407387637982600208305841 126305540728486950156229381)
              ·
                refine ⟨23682288886591303154293009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126305540728486950156229381 23682288886591303154293009)
                ·
                  refine ⟨17761716664943477365719757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23682288886591303154293009 17761716664943477365719757)
                  ·
                    refine ⟨6660643749353804012144909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17761716664943477365719757 6660643749353804012144909)
                    ·
                      refine ⟨2497741406007676504554341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6660643749353804012144909 2497741406007676504554341)
                      ·
                        rfl

theorem cell23_4864334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_4864334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864334 prefixEnd_4864334 := by exact prefixLift 4864334
  have htrace : WordTrace (prefixWord ++ tailWord_4864334) baseStart_4864334 baseEnd_4864334 := by
    simpa [prefixWord, tailWord_4864334, baseEnd_4864334] using wordTrace_append hprefix tailTrace_4864334
  have hstable : (prefixWord ++ tailWord_4864334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864334).length < 2 ^ (prefixWord ++ tailWord_4864334).sum := by decide
  have hdescent : baseEnd_4864334 < baseStart_4864334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864341 : List Nat := [1, 3, 2, 2, 4, 2, 1, 1, 7]
def baseStart_4864341 : Nat := 118140960795 + 4864341 * 2 ^ 59
def prefixEnd_4864341 : Nat := 4983230072969 + 3 ^ 40 * 4864341 * 2
def baseEnd_4864341 : Nat := 277527222263584219685201

theorem tailTrace_4864341 : CollatzResearch.WordTrace tailWord_4864341 prefixEnd_4864341 277527222263584219685201 := by
  unfold tailWord_4864341
  simp only [CollatzResearch.WordTrace]
  refine ⟨177417091670330795147464877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118278061113553863431643251 177417091670330795147464877)
  ·
    refine ⟨66531409376374048180299329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177417091670330795147464877 66531409376374048180299329)
    ·
      refine ⟨49898557032280536135224497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66531409376374048180299329 49898557032280536135224497)
      ·
        refine ⟨37423917774210402101418373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49898557032280536135224497 37423917774210402101418373)
        ·
          refine ⟨7016984582664450394015945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37423917774210402101418373 7016984582664450394015945)
          ·
            refine ⟨5262738436998337795511959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7016984582664450394015945 5262738436998337795511959)
            ·
              refine ⟨7894107655497506693267939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5262738436998337795511959 7894107655497506693267939)
              ·
                refine ⟨11841161483246260039901909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7894107655497506693267939 11841161483246260039901909)
                ·
                  refine ⟨277527222263584219685201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11841161483246260039901909 277527222263584219685201)
                  ·
                    rfl

theorem cell23_4864341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 7].length) (baseStart_4864341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864341 prefixEnd_4864341 := by exact prefixLift 4864341
  have htrace : WordTrace (prefixWord ++ tailWord_4864341) baseStart_4864341 baseEnd_4864341 := by
    simpa [prefixWord, tailWord_4864341, baseEnd_4864341] using wordTrace_append hprefix tailTrace_4864341
  have hstable : (prefixWord ++ tailWord_4864341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864341).length < 2 ^ (prefixWord ++ tailWord_4864341).sum := by decide
  have hdescent : baseEnd_4864341 < baseStart_4864341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864352 : List Nat := [2, 1, 1, 3, 5, 2, 2, 1, 2, 2, 2]
def baseStart_4864352 : Nat := 118140960795 + 4864352 * 2 ^ 59
def prefixEnd_4864352 : Nat := 4983230072969 + 3 ^ 40 * 4864352 * 2
def baseEnd_4864352 : Nat := 2497750648659457434129259

theorem tailTrace_4864352 : CollatzResearch.WordTrace tailWord_4864352 prefixEnd_4864352 2497750648659457434129259 := by
  unfold tailWord_4864352
  simp only [CollatzResearch.WordTrace]
  refine ⟨88708746436645472013057655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118278328582193962684076873 88708746436645472013057655)
  ·
    refine ⟨133063119654968208019586483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88708746436645472013057655 133063119654968208019586483)
    ·
      refine ⟨199594679482452312029379725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133063119654968208019586483 199594679482452312029379725)
      ·
        refine ⟨74848004805919617011017397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199594679482452312029379725 74848004805919617011017397)
        ·
          refine ⟨7017000450554964094782881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74848004805919617011017397 7017000450554964094782881)
          ·
            refine ⟨5262750337916223071087161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7017000450554964094782881 5262750337916223071087161)
            ·
              refine ⟨3947062753437167303315371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5262750337916223071087161 3947062753437167303315371)
              ·
                refine ⟨5920594130155750954973057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3947062753437167303315371 5920594130155750954973057)
                ·
                  refine ⟨4440445597616813216229793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5920594130155750954973057 4440445597616813216229793)
                  ·
                    refine ⟨3330334198212609912172345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4440445597616813216229793 3330334198212609912172345)
                    ·
                      refine ⟨2497750648659457434129259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3330334198212609912172345 2497750648659457434129259)
                      ·
                        rfl

theorem cell23_4864352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_4864352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864352 prefixEnd_4864352 := by exact prefixLift 4864352
  have htrace : WordTrace (prefixWord ++ tailWord_4864352) baseStart_4864352 baseEnd_4864352 := by
    simpa [prefixWord, tailWord_4864352, baseEnd_4864352] using wordTrace_append hprefix tailTrace_4864352
  have hstable : (prefixWord ++ tailWord_4864352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864352).length < 2 ^ (prefixWord ++ tailWord_4864352).sum := by decide
  have hdescent : baseEnd_4864352 < baseStart_4864352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864391 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 2, 4, 2]
def baseStart_4864391 : Nat := 118140960795 + 4864391 * 2 ^ 59
def prefixEnd_4864391 : Nat := 4983230072969 + 3 ^ 40 * 4864391 * 2
def baseEnd_4864391 : Nat := 2497770674404982781541579

theorem tailTrace_4864391 : CollatzResearch.WordTrace tailWord_4864391 prefixEnd_4864391 2497770674404982781541579 := by
  unfold tailWord_4864391
  simp only [CollatzResearch.WordTrace]
  refine ⟨177418915320149653686785027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118279276880099769124523351 177418915320149653686785027)
  ·
    refine ⟨266128372980224480530177541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177418915320149653686785027 266128372980224480530177541)
    ·
      refine ⟨49899069933792090099408289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266128372980224480530177541 49899069933792090099408289)
      ·
        refine ⟨37424302450344067574556217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49899069933792090099408289 37424302450344067574556217)
        ·
          refine ⟨28068226837758050680917163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37424302450344067574556217 28068226837758050680917163)
          ·
            refine ⟨42102340256637076021375745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28068226837758050680917163 42102340256637076021375745)
            ·
              refine ⟨31576755192477807016031809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42102340256637076021375745 31576755192477807016031809)
              ·
                refine ⟨23682566394358355262023857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31576755192477807016031809 23682566394358355262023857)
                ·
                  refine ⟨17761924795768766446517893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23682566394358355262023857 17761924795768766446517893)
                  ·
                    refine ⟨3330360899206643708722105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17761924795768766446517893 3330360899206643708722105)
                    ·
                      refine ⟨2497770674404982781541579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3330360899206643708722105 2497770674404982781541579)
                      ·
                        rfl

theorem cell23_4864391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_4864391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864391 prefixEnd_4864391 := by exact prefixLift 4864391
  have htrace : WordTrace (prefixWord ++ tailWord_4864391) baseStart_4864391 baseEnd_4864391 := by
    simpa [prefixWord, tailWord_4864391, baseEnd_4864391] using wordTrace_append hprefix tailTrace_4864391
  have hstable : (prefixWord ++ tailWord_4864391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864391).length < 2 ^ (prefixWord ++ tailWord_4864391).sum := by decide
  have hdescent : baseEnd_4864391 < baseStart_4864391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864408 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 2, 4, 2]
def baseStart_4864408 : Nat := 118140960795 + 4864408 * 2 ^ 59
def prefixEnd_4864408 : Nat := 4983230072969 + 3 ^ 40 * 4864408 * 2
def baseEnd_4864408 : Nat := 2497779403576109215029001

theorem tailTrace_4864408 : CollatzResearch.WordTrace tailWord_4864408 prefixEnd_4864408 2497779403576109215029001 := by
  unfold tailWord_4864408
  simp only [CollatzResearch.WordTrace]
  refine ⟨88709767680544032795076939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118279690240725377060102585 88709767680544032795076939)
  ·
    refine ⟨133064651520816049192615409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88709767680544032795076939 133064651520816049192615409)
    ·
      refine ⟨99798488640612036894461557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133064651520816049192615409 99798488640612036894461557)
      ·
        refine ⟨9356108310057378458855771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99798488640612036894461557 9356108310057378458855771)
        ·
          refine ⟨14034162465086067688283657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9356108310057378458855771 14034162465086067688283657)
          ·
            refine ⟨10525621848814550766212743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14034162465086067688283657 10525621848814550766212743)
            ·
              refine ⟨15788432773221826149319115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10525621848814550766212743 15788432773221826149319115)
              ·
                refine ⟨23682649159832739223978673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15788432773221826149319115 23682649159832739223978673)
                ·
                  refine ⟨17761986869874554417984005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23682649159832739223978673 17761986869874554417984005)
                  ·
                    refine ⟨3330372538101478953372001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17761986869874554417984005 3330372538101478953372001)
                    ·
                      refine ⟨2497779403576109215029001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3330372538101478953372001 2497779403576109215029001)
                      ·
                        rfl

theorem cell23_4864408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_4864408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864408 prefixEnd_4864408 := by exact prefixLift 4864408
  have htrace : WordTrace (prefixWord ++ tailWord_4864408) baseStart_4864408 baseEnd_4864408 := by
    simpa [prefixWord, tailWord_4864408, baseEnd_4864408] using wordTrace_append hprefix tailTrace_4864408
  have hstable : (prefixWord ++ tailWord_4864408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864408).length < 2 ^ (prefixWord ++ tailWord_4864408).sum := by decide
  have hdescent : baseEnd_4864408 < baseStart_4864408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864451 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 4, 3, 2]
def baseStart_4864451 : Nat := 118140960795 + 4864451 * 2 ^ 59
def prefixEnd_4864451 : Nat := 4983230072969 + 3 ^ 40 * 4864451 * 2
def baseEnd_4864451 : Nat := 2497801483244252546791303

theorem tailTrace_4864451 : CollatzResearch.WordTrace tailWord_4864451 prefixEnd_4864451 2497801483244252546791303 := by
  unfold tailWord_4864451
  simp only [CollatzResearch.WordTrace]
  refine ⟨177421103699932283933969207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118280735799954855955979471 177421103699932283933969207)
  ·
    refine ⟨266131655549898425900953811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177421103699932283933969207 266131655549898425900953811)
    ·
      refine ⟨399197483324847638851430717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266131655549898425900953811 399197483324847638851430717)
      ·
        refine ⟨149699056246817864569286519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 399197483324847638851430717 149699056246817864569286519)
        ·
          refine ⟨224548584370226796853929779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149699056246817864569286519 224548584370226796853929779)
          ·
            refine ⟨336822876555340195280894669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224548584370226796853929779 336822876555340195280894669)
            ·
              refine ⟨126308578708252573230335501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 336822876555340195280894669 126308578708252573230335501)
              ·
                refine ⟨47365717015594714961375813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126308578708252573230335501 47365717015594714961375813)
                ·
                  refine ⟨8881071940424009055257965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47365717015594714961375813 8881071940424009055257965)
                  ·
                    refine ⟨3330401977659003395721737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8881071940424009055257965 3330401977659003395721737)
                    ·
                      refine ⟨2497801483244252546791303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3330401977659003395721737 2497801483244252546791303)
                      ·
                        rfl

theorem cell23_4864451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 3, 2].length) (baseStart_4864451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864451 prefixEnd_4864451 := by exact prefixLift 4864451
  have htrace : WordTrace (prefixWord ++ tailWord_4864451) baseStart_4864451 baseEnd_4864451 := by
    simpa [prefixWord, tailWord_4864451, baseEnd_4864451] using wordTrace_append hprefix tailTrace_4864451
  have hstable : (prefixWord ++ tailWord_4864451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864451).length < 2 ^ (prefixWord ++ tailWord_4864451).sum := by decide
  have hdescent : baseEnd_4864451 < baseStart_4864451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864458 : List Nat := [3, 1, 2, 1, 2, 2, 4, 1, 3, 1, 3]
def baseStart_4864458 : Nat := 118140960795 + 4864458 * 2 ^ 59
def prefixEnd_4864458 : Nat := 4983230072969 + 3 ^ 40 * 4864458 * 2
def baseEnd_4864458 : Nat := 2497805077608834019403771

theorem tailTrace_4864458 : CollatzResearch.WordTrace tailWord_4864458 prefixEnd_4864458 2497805077608834019403771 := by
  unfold tailWord_4864458
  simp only [CollatzResearch.WordTrace]
  refine ⟨44355339752726731032368507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118280906007271282752982685 44355339752726731032368507)
  ·
    refine ⟨66533009629090096548552761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44355339752726731032368507 66533009629090096548552761)
    ·
      refine ⟨49899757221817572411414571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66533009629090096548552761 49899757221817572411414571)
      ·
        refine ⟨74849635832726358617121857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49899757221817572411414571 74849635832726358617121857)
        ·
          refine ⟨56137226874544768962841393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74849635832726358617121857 56137226874544768962841393)
          ·
            refine ⟨42102920155908576722131045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56137226874544768962841393 42102920155908576722131045)
            ·
              refine ⟨7894297529232858135399571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42102920155908576722131045 7894297529232858135399571)
              ·
                refine ⟨11841446293849287203099357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7894297529232858135399571 11841446293849287203099357)
                ·
                  refine ⟨4440542360193482701162259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11841446293849287203099357 4440542360193482701162259)
                  ·
                    refine ⟨6660813540290224051743389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4440542360193482701162259 6660813540290224051743389)
                    ·
                      refine ⟨2497805077608834019403771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6660813540290224051743389 2497805077608834019403771)
                      ·
                        rfl

theorem cell23_4864458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_4864458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864458 prefixEnd_4864458 := by exact prefixLift 4864458
  have htrace : WordTrace (prefixWord ++ tailWord_4864458) baseStart_4864458 baseEnd_4864458 := by
    simpa [prefixWord, tailWord_4864458, baseEnd_4864458] using wordTrace_append hprefix tailTrace_4864458
  have hstable : (prefixWord ++ tailWord_4864458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864458).length < 2 ^ (prefixWord ++ tailWord_4864458).sum := by decide
  have hdescent : baseEnd_4864458 < baseStart_4864458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864468 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 1, 5, 2]
def baseStart_4864468 : Nat := 118140960795 + 4864468 * 2 ^ 59
def prefixEnd_4864468 : Nat := 4983230072969 + 3 ^ 40 * 4864468 * 2
def baseEnd_4864468 : Nat := 2497810212415378980278725

theorem tailTrace_4864468 : CollatzResearch.WordTrace tailWord_4864468 prefixEnd_4864468 2497810212415378980278725 := by
  unfold tailWord_4864468
  simp only [CollatzResearch.WordTrace]
  refine ⟨88710861870435347918669029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118281149160580463891558705 88710861870435347918669029)
  ·
    refine ⟨16633286600706627734750443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88710861870435347918669029 16633286600706627734750443)
    ·
      refine ⟨24949929901059941602125665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16633286600706627734750443 24949929901059941602125665)
      ·
        refine ⟨18712447425794956201594249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24949929901059941602125665 18712447425794956201594249)
        ·
          refine ⟨14034335569346217151195687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18712447425794956201594249 14034335569346217151195687)
          ·
            refine ⟨21051503354019325726793531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14034335569346217151195687 21051503354019325726793531)
            ·
              refine ⟨31577255031028988590190297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21051503354019325726793531 31577255031028988590190297)
              ·
                refine ⟨23682941273271741442642723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31577255031028988590190297 23682941273271741442642723)
                ·
                  refine ⟨35524411909907612163964085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23682941273271741442642723 35524411909907612163964085)
                  ·
                    refine ⟨3330413616553838640371633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35524411909907612163964085 3330413616553838640371633)
                    ·
                      refine ⟨2497810212415378980278725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3330413616553838640371633 2497810212415378980278725)
                      ·
                        rfl

theorem cell23_4864468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_4864468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864468 prefixEnd_4864468 := by exact prefixLift 4864468
  have htrace : WordTrace (prefixWord ++ tailWord_4864468) baseStart_4864468 baseEnd_4864468 := by
    simpa [prefixWord, tailWord_4864468, baseEnd_4864468] using wordTrace_append hprefix tailTrace_4864468
  have hstable : (prefixWord ++ tailWord_4864468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864468).length < 2 ^ (prefixWord ++ tailWord_4864468).sum := by decide
  have hdescent : baseEnd_4864468 < baseStart_4864468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864481 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 2, 6, 2]
def baseStart_4864481 : Nat := 118140960795 + 4864481 * 2 ^ 59
def prefixEnd_4864481 : Nat := 4983230072969 + 3 ^ 40 * 4864481 * 2
def baseEnd_4864481 : Nat := 2497816887663887429416165

theorem tailTrace_4864481 : CollatzResearch.WordTrace tailWord_4864481 prefixEnd_4864481 2497816887663887429416165 := by
  unfold tailWord_4864481
  simp only [CollatzResearch.WordTrace]
  refine ⟨177422197889823599057561297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118281465259882399371707531 177422197889823599057561297)
  ·
    refine ⟨133066648417367699293170973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177422197889823599057561297 133066648417367699293170973)
    ·
      refine ⟨49899993156512887234939115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133066648417367699293170973 49899993156512887234939115)
      ·
        refine ⟨74849989734769330852408673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49899993156512887234939115 74849989734769330852408673)
        ·
          refine ⟨56137492301076998139306505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74849989734769330852408673 56137492301076998139306505)
          ·
            refine ⟨42103119225807748604479879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56137492301076998139306505 42103119225807748604479879)
            ·
              refine ⟨63154678838711622906719819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42103119225807748604479879 63154678838711622906719819)
              ·
                refine ⟨94732018258067434360079729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63154678838711622906719819 94732018258067434360079729)
                ·
                  refine ⟨71049013693550575770059797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94732018258067434360079729 71049013693550575770059797)
                  ·
                    refine ⟨3330422516885183239221553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71049013693550575770059797 3330422516885183239221553)
                    ·
                      refine ⟨2497816887663887429416165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3330422516885183239221553 2497816887663887429416165)
                      ·
                        rfl

theorem cell23_4864481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_4864481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864481 prefixEnd_4864481 := by exact prefixLift 4864481
  have htrace : WordTrace (prefixWord ++ tailWord_4864481) baseStart_4864481 baseEnd_4864481 := by
    simpa [prefixWord, tailWord_4864481, baseEnd_4864481] using wordTrace_append hprefix tailTrace_4864481
  have hstable : (prefixWord ++ tailWord_4864481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864481).length < 2 ^ (prefixWord ++ tailWord_4864481).sum := by decide
  have hdescent : baseEnd_4864481 < baseStart_4864481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864531 : List Nat := [1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 3]
def baseStart_4864531 : Nat := 118140960795 + 4864531 * 2 ^ 59
def prefixEnd_4864531 : Nat := 4983230072969 + 3 ^ 40 * 4864531 * 2
def baseEnd_4864531 : Nat := 2497842561696612233790935

theorem tailTrace_4864531 : CollatzResearch.WordTrace tailWord_4864531 prefixEnd_4864531 2497842561696612233790935 := by
  unfold tailWord_4864531
  simp only [CollatzResearch.WordTrace]
  refine ⟨177424021539642457596881447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118282681026428305064587631 177424021539642457596881447)
  ·
    refine ⟨266136032309463686395322171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177424021539642457596881447 266136032309463686395322171)
    ·
      refine ⟨399204048464195529592983257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266136032309463686395322171 399204048464195529592983257)
      ·
        refine ⟨299403036348146647194737443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 399204048464195529592983257 299403036348146647194737443)
        ·
          refine ⟨449104554522219970792106165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299403036348146647194737443 449104554522219970792106165)
          ·
            refine ⟨42103551986458122261759953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 449104554522219970792106165 42103551986458122261759953)
            ·
              refine ⟨31577663989843591696319965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42103551986458122261759953 31577663989843591696319965)
              ·
                refine ⟨11841623996191346886119987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31577663989843591696319965 11841623996191346886119987)
                ·
                  refine ⟨17762435994287020329179981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11841623996191346886119987 17762435994287020329179981)
                  ·
                    refine ⟨6660913497857632623442493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17762435994287020329179981 6660913497857632623442493)
                    ·
                      refine ⟨2497842561696612233790935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6660913497857632623442493 2497842561696612233790935)
                      ·
                        rfl

theorem cell23_4864531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3, 3].length) (baseStart_4864531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864531 prefixEnd_4864531 := by exact prefixLift 4864531
  have htrace : WordTrace (prefixWord ++ tailWord_4864531) baseStart_4864531 baseEnd_4864531 := by
    simpa [prefixWord, tailWord_4864531, baseEnd_4864531] using wordTrace_append hprefix tailTrace_4864531
  have hstable : (prefixWord ++ tailWord_4864531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864531).length < 2 ^ (prefixWord ++ tailWord_4864531).sum := by decide
  have hdescent : baseEnd_4864531 < baseStart_4864531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864532 : List Nat := [2, 4, 3, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_4864532 : Nat := 118140960795 + 4864532 * 2 ^ 59
def prefixEnd_4864532 : Nat := 4983230072969 + 3 ^ 40 * 4864532 * 2
def baseEnd_4864532 : Nat := 2497843075177266729878431

theorem tailTrace_4864532 : CollatzResearch.WordTrace tailWord_4864532 prefixEnd_4864532 2497843075177266729878431 := by
  unfold tailWord_4864532
  simp only [CollatzResearch.WordTrace]
  refine ⟨88712029006319417383833925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118282705341759223178445233 88712029006319417383833925)
  ·
    refine ⟨16633505438684890759468861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88712029006319417383833925 16633505438684890759468861)
    ·
      refine ⟨6237564539506834034800823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16633505438684890759468861 6237564539506834034800823)
      ·
        refine ⟨9356346809260251052201235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6237564539506834034800823 9356346809260251052201235)
        ·
          refine ⟨14034520213890376578301853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9356346809260251052201235 14034520213890376578301853)
          ·
            refine ⟨5262945080208891216863195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14034520213890376578301853 5262945080208891216863195)
            ·
              refine ⟨7894417620313336825294793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5262945080208891216863195 7894417620313336825294793)
              ·
                refine ⟨5920813215235002618971095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7894417620313336825294793 5920813215235002618971095)
                ·
                  refine ⟨8881219822852503928456643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5920813215235002618971095 8881219822852503928456643)
                  ·
                    refine ⟨13321829734278755892684965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8881219822852503928456643 13321829734278755892684965)
                    ·
                      refine ⟨2497843075177266729878431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13321829734278755892684965 2497843075177266729878431)
                      ·
                        rfl

theorem cell23_4864532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_4864532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864532 prefixEnd_4864532 := by exact prefixLift 4864532
  have htrace : WordTrace (prefixWord ++ tailWord_4864532) baseStart_4864532 baseEnd_4864532 := by
    simpa [prefixWord, tailWord_4864532, baseEnd_4864532] using wordTrace_append hprefix tailTrace_4864532
  have hstable : (prefixWord ++ tailWord_4864532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864532).length < 2 ^ (prefixWord ++ tailWord_4864532).sum := by decide
  have hdescent : baseEnd_4864532 < baseStart_4864532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864535 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 3, 2, 3]
def baseStart_4864535 : Nat := 118140960795 + 4864535 * 2 ^ 59
def prefixEnd_4864535 : Nat := 4983230072969 + 3 ^ 40 * 4864535 * 2
def baseEnd_4864535 : Nat := 2497844615619230218140917

theorem tailTrace_4864535 : CollatzResearch.WordTrace tailWord_4864535 prefixEnd_4864535 2497844615619230218140917 := by
  unfold tailWord_4864535
  simp only [CollatzResearch.WordTrace]
  refine ⟨177424167431627966280027059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118282778287751977520018039 177424167431627966280027059)
  ·
    refine ⟨266136251147441949420040589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177424167431627966280027059 266136251147441949420040589)
    ·
      refine ⟨99801094180290731032515221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266136251147441949420040589 99801094180290731032515221)
      ·
        refine ⟨4678176289701128017149151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99801094180290731032515221 4678176289701128017149151)
        ·
          refine ⟨7017264434551692025723727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4678176289701128017149151 7017264434551692025723727)
          ·
            refine ⟨10525896651827538038585591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7017264434551692025723727 10525896651827538038585591)
            ·
              refine ⟨15788844977741307057878387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10525896651827538038585591 15788844977741307057878387)
              ·
                refine ⟨23683267466611960586817581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15788844977741307057878387 23683267466611960586817581)
                ·
                  refine ⟨8881225299979485220056593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23683267466611960586817581 8881225299979485220056593)
                  ·
                    refine ⟨6660918974984613915042445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8881225299979485220056593 6660918974984613915042445)
                    ·
                      refine ⟨2497844615619230218140917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6660918974984613915042445 2497844615619230218140917)
                      ·
                        rfl

theorem cell23_4864535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_4864535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864535 prefixEnd_4864535 := by exact prefixLift 4864535
  have htrace : WordTrace (prefixWord ++ tailWord_4864535) baseStart_4864535 baseEnd_4864535 := by
    simpa [prefixWord, tailWord_4864535, baseEnd_4864535] using wordTrace_append hprefix tailTrace_4864535
  have hstable : (prefixWord ++ tailWord_4864535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864535).length < 2 ^ (prefixWord ++ tailWord_4864535).sum := by decide
  have hdescent : baseEnd_4864535 < baseStart_4864535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864552 : List Nat := [2, 1, 5, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_4864552 : Nat := 118140960795 + 4864552 * 2 ^ 59
def prefixEnd_4864552 : Nat := 4983230072969 + 3 ^ 40 * 4864552 * 2
def baseEnd_4864552 : Nat := 2497853344790356651628339

theorem tailTrace_4864552 : CollatzResearch.WordTrace tailWord_4864552 prefixEnd_4864552 2497853344790356651628339 := by
  unfold tailWord_4864552
  simp only [CollatzResearch.WordTrace]
  refine ⟨88712393736283189091697955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118283191648377585455597273 88712393736283189091697955)
  ·
    refine ⟨133068590604424783637546933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88712393736283189091697955 133068590604424783637546933)
    ·
      refine ⟨12475180369164823466020025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133068590604424783637546933 12475180369164823466020025)
      ·
        refine ⟨9356385276873617599515019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12475180369164823466020025 9356385276873617599515019)
        ·
          refine ⟨14034577915310426399272529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9356385276873617599515019 14034577915310426399272529)
          ·
            refine ⟨10525933436482819799454397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14034577915310426399272529 10525933436482819799454397)
            ·
              refine ⟨3947225038681057424795399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10525933436482819799454397 3947225038681057424795399)
              ·
                refine ⟨5920837558021586137193099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3947225038681057424795399 5920837558021586137193099)
                ·
                  refine ⟨8881256337032379205789649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5920837558021586137193099 8881256337032379205789649)
                  ·
                    refine ⟨6660942252774284404342237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8881256337032379205789649 6660942252774284404342237)
                    ·
                      refine ⟨2497853344790356651628339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6660942252774284404342237 2497853344790356651628339)
                      ·
                        rfl

theorem cell23_4864552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_4864552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864552 prefixEnd_4864552 := by exact prefixLift 4864552
  have htrace : WordTrace (prefixWord ++ tailWord_4864552) baseStart_4864552 baseEnd_4864552 := by
    simpa [prefixWord, tailWord_4864552, baseEnd_4864552] using wordTrace_append hprefix tailTrace_4864552
  have hstable : (prefixWord ++ tailWord_4864552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864552).length < 2 ^ (prefixWord ++ tailWord_4864552).sum := by decide
  have hdescent : baseEnd_4864552 < baseStart_4864552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864565 : List Nat := [1, 3, 3, 1, 1, 2, 4, 2, 2, 1, 3]
def baseStart_4864565 : Nat := 118140960795 + 4864565 * 2 ^ 59
def prefixEnd_4864565 : Nat := 4983230072969 + 3 ^ 40 * 4864565 * 2
def baseEnd_4864565 : Nat := 2497860020038865100765779

theorem tailTrace_4864565 : CollatzResearch.WordTrace tailWord_4864565 prefixEnd_4864565 2497860020038865100765779 := by
  unfold tailWord_4864565
  simp only [CollatzResearch.WordTrace]
  refine ⟨177425261621519281403619149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118283507747679520935746099 177425261621519281403619149)
  ·
    refine ⟨66534473108069730526357181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177425261621519281403619149 66534473108069730526357181)
    ·
      refine ⟨24950427415526148947383943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66534473108069730526357181 24950427415526148947383943)
      ·
        refine ⟨37425641123289223421075915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24950427415526148947383943 37425641123289223421075915)
        ·
          refine ⟨56138461684933835131613873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37425641123289223421075915 56138461684933835131613873)
          ·
            refine ⟨42103846263700376348710405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56138461684933835131613873 42103846263700376348710405)
            ·
              refine ⟨7894471174443820565383201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42103846263700376348710405 7894471174443820565383201)
              ·
                refine ⟨5920853380832865424037401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7894471174443820565383201 5920853380832865424037401)
                ·
                  refine ⟨4440640035624649068028051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5920853380832865424037401 4440640035624649068028051)
                  ·
                    refine ⟨6660960053436973602042077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4440640035624649068028051 6660960053436973602042077)
                    ·
                      refine ⟨2497860020038865100765779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6660960053436973602042077 2497860020038865100765779)
                      ·
                        rfl

theorem cell23_4864565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_4864565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864565 prefixEnd_4864565 := by exact prefixLift 4864565
  have htrace : WordTrace (prefixWord ++ tailWord_4864565) baseStart_4864565 baseEnd_4864565 := by
    simpa [prefixWord, tailWord_4864565, baseEnd_4864565] using wordTrace_append hprefix tailTrace_4864565
  have hstable : (prefixWord ++ tailWord_4864565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864565).length < 2 ^ (prefixWord ++ tailWord_4864565).sum := by decide
  have hdescent : baseEnd_4864565 < baseStart_4864565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864566 : List Nat := [5, 1, 2, 1, 2, 1, 4, 2, 1, 2, 2]
def baseStart_4864566 : Nat := 118140960795 + 4864566 * 2 ^ 59
def prefixEnd_4864566 : Nat := 4983230072969 + 3 ^ 40 * 4864566 * 2
def baseEnd_4864566 : Nat := 2497860533519519596853275

theorem tailTrace_4864566 : CollatzResearch.WordTrace tailWord_4864566 prefixEnd_4864566 2497860533519519596853275 := by
  unfold tailWord_4864566
  simp only [CollatzResearch.WordTrace]
  refine ⟨11089081130907228660900347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118283532063010439049603701 11089081130907228660900347)
  ·
    refine ⟨16633621696360842991350521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11089081130907228660900347 16633621696360842991350521)
    ·
      refine ⟨12475216272270632243512891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16633621696360842991350521 12475216272270632243512891)
      ·
        refine ⟨18712824408405948365269337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12475216272270632243512891 18712824408405948365269337)
        ·
          refine ⟨14034618306304461273952003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18712824408405948365269337 14034618306304461273952003)
          ·
            refine ⟨21051927459456691910928005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14034618306304461273952003 21051927459456691910928005)
            ·
              refine ⟨3947236398648129733299001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21051927459456691910928005 3947236398648129733299001)
              ·
                refine ⟨2960427298986097299974251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3947236398648129733299001 2960427298986097299974251)
                ·
                  refine ⟨4440640948479145949961377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2960427298986097299974251 4440640948479145949961377)
                  ·
                    refine ⟨3330480711359359462471033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4440640948479145949961377 3330480711359359462471033)
                    ·
                      refine ⟨2497860533519519596853275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3330480711359359462471033 2497860533519519596853275)
                      ·
                        rfl

theorem cell23_4864566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_4864566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864566 prefixEnd_4864566 := by exact prefixLift 4864566
  have htrace : WordTrace (prefixWord ++ tailWord_4864566) baseStart_4864566 baseEnd_4864566 := by
    simpa [prefixWord, tailWord_4864566, baseEnd_4864566] using wordTrace_append hprefix tailTrace_4864566
  have hstable : (prefixWord ++ tailWord_4864566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864566).length < 2 ^ (prefixWord ++ tailWord_4864566).sum := by decide
  have hdescent : baseEnd_4864566 < baseStart_4864566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864581 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 2, 6]
def baseStart_4864581 : Nat := 118140960795 + 4864581 * 2 ^ 59
def prefixEnd_4864581 : Nat := 4983230072969 + 3 ^ 40 * 4864581 * 2
def baseEnd_4864581 : Nat := 832622745243112346055235

theorem tailTrace_4864581 : CollatzResearch.WordTrace tailWord_4864581 prefixEnd_4864581 832622745243112346055235 := by
  unfold tailWord_4864581
  simp only [CollatzResearch.WordTrace]
  refine ⟨177425845189461316136201597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118283896792974210757467731 177425845189461316136201597)
  ·
    refine ⟨66534691946047993551075599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177425845189461316136201597 66534691946047993551075599)
    ·
      refine ⟨99802037919071990326613399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66534691946047993551075599 99802037919071990326613399)
      ·
        refine ⟨149703056878607985489920099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99802037919071990326613399 149703056878607985489920099)
        ·
          refine ⟨224554585317911978234880149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149703056878607985489920099 224554585317911978234880149)
          ·
            refine ⟨10525996186777123979760007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 224554585317911978234880149 10525996186777123979760007)
            ·
              refine ⟨15788994280165685969640011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10525996186777123979760007 15788994280165685969640011)
              ·
                refine ⟨23683491420248528954460017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15788994280165685969640011 23683491420248528954460017)
                ·
                  refine ⟨17762618565186396715845013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23683491420248528954460017 17762618565186396715845013)
                  ·
                    refine ⟨832622745243112346055235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17762618565186396715845013 832622745243112346055235)
                    ·
                      rfl

theorem cell23_4864581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_4864581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864581 prefixEnd_4864581 := by exact prefixLift 4864581
  have htrace : WordTrace (prefixWord ++ tailWord_4864581) baseStart_4864581 baseEnd_4864581 := by
    simpa [prefixWord, tailWord_4864581, baseEnd_4864581] using wordTrace_append hprefix tailTrace_4864581
  have hstable : (prefixWord ++ tailWord_4864581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864581).length < 2 ^ (prefixWord ++ tailWord_4864581).sum := by decide
  have hdescent : baseEnd_4864581 < baseStart_4864581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864582 : List Nat := [6, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_4864582 : Nat := 118140960795 + 4864582 * 2 ^ 59
def prefixEnd_4864582 : Nat := 4983230072969 + 3 ^ 40 * 4864582 * 2
def baseEnd_4864582 : Nat := 2497868749209991534253201

theorem tailTrace_4864582 : CollatzResearch.WordTrace tailWord_4864582 prefixEnd_4864582 2497868749209991534253201 := by
  unfold tailWord_4864582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5544558801951802915843375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 118283921108305128871325333 5544558801951802915843375)
  ·
    refine ⟨8316838202927704373765063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5544558801951802915843375 8316838202927704373765063)
    ·
      refine ⟨12475257304391556560647595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8316838202927704373765063 12475257304391556560647595)
      ·
        refine ⟨18712885956587334840971393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12475257304391556560647595 18712885956587334840971393)
        ·
          refine ⟨14034664467440501130728545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18712885956587334840971393 14034664467440501130728545)
          ·
            refine ⟨10525998350580375848046409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14034664467440501130728545 10525998350580375848046409)
            ·
              refine ⟨7894498762935281886034807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10525998350580375848046409 7894498762935281886034807)
              ·
                refine ⟨11841748144402922829052211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7894498762935281886034807 11841748144402922829052211)
                ·
                  refine ⟨17762622216604384243578317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11841748144402922829052211 17762622216604384243578317)
                  ·
                    refine ⟨6660983331226644091341869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17762622216604384243578317 6660983331226644091341869)
                    ·
                      refine ⟨2497868749209991534253201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6660983331226644091341869 2497868749209991534253201)
                      ·
                        rfl

theorem cell23_4864582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_4864582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864582 prefixEnd_4864582 := by exact prefixLift 4864582
  have htrace : WordTrace (prefixWord ++ tailWord_4864582) baseStart_4864582 baseEnd_4864582 := by
    simpa [prefixWord, tailWord_4864582, baseEnd_4864582] using wordTrace_append hprefix tailTrace_4864582
  have hstable : (prefixWord ++ tailWord_4864582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864582).length < 2 ^ (prefixWord ++ tailWord_4864582).sum := by decide
  have hdescent : baseEnd_4864582 < baseStart_4864582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864622 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 4, 2, 2]
def baseStart_4864622 : Nat := 118140960795 + 4864622 * 2 ^ 59
def prefixEnd_4864622 : Nat := 4983230072969 + 3 ^ 40 * 4864622 * 2
def baseEnd_4864622 : Nat := 2497889288436171377753017

theorem tailTrace_4864622 : CollatzResearch.WordTrace tailWord_4864622 prefixEnd_4864622 2497889288436171377753017 := by
  unfold tailWord_4864622
  simp only [CollatzResearch.WordTrace]
  refine ⟨22178417572789097517305515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118284893721541853425629413 22178417572789097517305515)
  ·
    refine ⟨33267626359183646275958273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22178417572789097517305515 33267626359183646275958273)
    ·
      refine ⟨24950719769387734706968705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33267626359183646275958273 24950719769387734706968705)
      ·
        refine ⟨18713039827040801030226529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24950719769387734706968705 18713039827040801030226529)
        ·
          refine ⟨14034779870280600772669897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18713039827040801030226529 14034779870280600772669897)
          ·
            refine ⟨10526084902710450579502423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14034779870280600772669897 10526084902710450579502423)
            ·
              refine ⟨15789127354065675869253635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10526084902710450579502423 15789127354065675869253635)
              ·
                refine ⟨23683691031098513803880453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15789127354065675869253635 23683691031098513803880453)
                ·
                  refine ⟨4440692068330971338227585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23683691031098513803880453 4440692068330971338227585)
                  ·
                    refine ⟨3330519051248228503670689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4440692068330971338227585 3330519051248228503670689)
                    ·
                      refine ⟨2497889288436171377753017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3330519051248228503670689 2497889288436171377753017)
                      ·
                        rfl

theorem cell23_4864622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_4864622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864622 prefixEnd_4864622 := by exact prefixLift 4864622
  have htrace : WordTrace (prefixWord ++ tailWord_4864622) baseStart_4864622 baseEnd_4864622 := by
    simpa [prefixWord, tailWord_4864622, baseEnd_4864622] using wordTrace_append hprefix tailTrace_4864622
  have hstable : (prefixWord ++ tailWord_4864622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864622).length < 2 ^ (prefixWord ++ tailWord_4864622).sum := by decide
  have hdescent : baseEnd_4864622 < baseStart_4864622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864641 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 3, 7]
def baseStart_4864641 : Nat := 118140960795 + 4864641 * 2 ^ 59
def prefixEnd_4864641 : Nat := 4983230072969 + 3 ^ 40 * 4864641 * 2
def baseEnd_4864641 : Nat := 832633014856202267805143

theorem tailTrace_4864641 : CollatzResearch.WordTrace tailWord_4864641 prefixEnd_4864641 832633014856202267805143 := by
  unfold tailWord_4864641
  simp only [CollatzResearch.WordTrace]
  refine ⟨177428033569243946383385777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118285355712829297588923851 177428033569243946383385777)
  ·
    refine ⟨133071025176932959787539333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177428033569243946383385777 133071025176932959787539333)
    ·
      refine ⟨24950817220674929960163625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133071025176932959787539333 24950817220674929960163625)
      ·
        refine ⟨18713112915506197470122719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24950817220674929960163625 18713112915506197470122719)
        ·
          refine ⟨28069669373259296205184079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18713112915506197470122719 28069669373259296205184079)
          ·
            refine ⟨42104504059888944307776119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28069669373259296205184079 42104504059888944307776119)
            ·
              refine ⟨63156756089833416461664179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42104504059888944307776119 63156756089833416461664179)
              ·
                refine ⟨94735134134750124692496269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63156756089833416461664179 94735134134750124692496269)
                ·
                  refine ⟨35525675300531296759686101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94735134134750124692496269 35525675300531296759686101)
                  ·
                    refine ⟨832633014856202267805143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35525675300531296759686101 832633014856202267805143)
                    ·
                      rfl

theorem cell23_4864641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_4864641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864641 prefixEnd_4864641 := by exact prefixLift 4864641
  have htrace : WordTrace (prefixWord ++ tailWord_4864641) baseStart_4864641 baseEnd_4864641 := by
    simpa [prefixWord, tailWord_4864641, baseEnd_4864641] using wordTrace_append hprefix tailTrace_4864641
  have hstable : (prefixWord ++ tailWord_4864641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864641).length < 2 ^ (prefixWord ++ tailWord_4864641).sum := by decide
  have hdescent : baseEnd_4864641 < baseStart_4864641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864658 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 1, 7]
def baseStart_4864658 : Nat := 118140960795 + 4864658 * 2 ^ 59
def prefixEnd_4864658 : Nat := 4983230072969 + 3 ^ 40 * 4864658 * 2
def baseEnd_4864658 : Nat := 832635924579911078967617

theorem tailTrace_4864658 : CollatzResearch.WordTrace tailWord_4864658 prefixEnd_4864658 832635924579911078967617 := by
  unfold tailWord_4864658
  simp only [CollatzResearch.WordTrace]
  refine ⟨44357163402545589571688657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118285769073454905524503085 44357163402545589571688657)
  ·
    refine ⟨33267872551909192178766493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44357163402545589571688657 33267872551909192178766493)
    ·
      refine ⟨12475452206965947067037435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33267872551909192178766493 12475452206965947067037435)
      ·
        refine ⟨18713178310448920600556153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12475452206965947067037435 18713178310448920600556153)
        ·
          refine ⟨14034883732836690450417115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18713178310448920600556153 14034883732836690450417115)
          ·
            refine ⟨21052325599255035675625673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14034883732836690450417115 21052325599255035675625673)
            ·
              refine ⟨15789244199441276756719255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21052325599255035675625673 15789244199441276756719255)
              ·
                refine ⟨23683866299161915135078883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15789244199441276756719255 23683866299161915135078883)
                ·
                  refine ⟨35525799448742872702618325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23683866299161915135078883 35525799448742872702618325)
                  ·
                    refine ⟨832635924579911078967617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35525799448742872702618325 832635924579911078967617)
                    ·
                      rfl

theorem cell23_4864658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_4864658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864658 prefixEnd_4864658 := by exact prefixLift 4864658
  have htrace : WordTrace (prefixWord ++ tailWord_4864658) baseStart_4864658 baseEnd_4864658 := by
    simpa [prefixWord, tailWord_4864658, baseEnd_4864658] using wordTrace_append hprefix tailTrace_4864658
  have hstable : (prefixWord ++ tailWord_4864658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864658).length < 2 ^ (prefixWord ++ tailWord_4864658).sum := by decide
  have hdescent : baseEnd_4864658 < baseStart_4864658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864679 : List Nat := [1, 1, 6, 3, 1, 1, 3, 2, 5]
def baseStart_4864679 : Nat := 118140960795 + 4864679 * 2 ^ 59
def prefixEnd_4864679 : Nat := 4983230072969 + 3 ^ 40 * 4864679 * 2
def baseEnd_4864679 : Nat := 277546506314830850526695

theorem tailTrace_4864679 : CollatzResearch.WordTrace tailWord_4864679 prefixEnd_4864679 277546506314830850526695 := by
  unfold tailWord_4864679
  simp only [CollatzResearch.WordTrace]
  refine ⟨177429419543106278873269091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118286279695404185915512727 177429419543106278873269091)
  ·
    refine ⟨266144129314659418309903637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177429419543106278873269091 266144129314659418309903637)
    ·
      refine ⟨12475506061624660233276733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 266144129314659418309903637 12475506061624660233276733)
      ·
        refine ⟨4678314773109247587478775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12475506061624660233276733 4678314773109247587478775)
        ·
          refine ⟨7017472159663871381218163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4678314773109247587478775 7017472159663871381218163)
          ·
            refine ⟨10526208239495807071827245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7017472159663871381218163 10526208239495807071827245)
            ·
              refine ⟨3947328089810927651935217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10526208239495807071827245 3947328089810927651935217)
              ·
                refine ⟨2960496067358195738951413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3947328089810927651935217 2960496067358195738951413)
                ·
                  refine ⟨277546506314830850526695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2960496067358195738951413 277546506314830850526695)
                  ·
                    rfl

theorem cell23_4864679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 2, 5].length) (baseStart_4864679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864679 prefixEnd_4864679 := by exact prefixLift 4864679
  have htrace : WordTrace (prefixWord ++ tailWord_4864679) baseStart_4864679 baseEnd_4864679 := by
    simpa [prefixWord, tailWord_4864679, baseEnd_4864679] using wordTrace_append hprefix tailTrace_4864679
  have hstable : (prefixWord ++ tailWord_4864679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864679).length < 2 ^ (prefixWord ++ tailWord_4864679).sum := by decide
  have hdescent : baseEnd_4864679 < baseStart_4864679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864698 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3]
def baseStart_4864698 : Nat := 118140960795 + 4864698 * 2 ^ 59
def prefixEnd_4864698 : Nat := 4983230072969 + 3 ^ 40 * 4864698 * 2
def baseEnd_4864698 : Nat := 2497928312965913080402667

theorem tailTrace_4864698 : CollatzResearch.WordTrace tailWord_4864698 prefixEnd_4864698 2497928312965913080402667 := by
  unfold tailWord_4864698
  simp only [CollatzResearch.WordTrace]
  refine ⟨44357528132509361279552687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118286741686691630078807165 44357528132509361279552687)
  ·
    refine ⟨66536292198764041919329031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44357528132509361279552687 66536292198764041919329031)
    ·
      refine ⟨99804438298146062878993547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66536292198764041919329031 99804438298146062878993547)
      ·
        refine ⟨149706657447219094318490321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99804438298146062878993547 149706657447219094318490321)
        ·
          refine ⟨112279993085414320738867741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149706657447219094318490321 112279993085414320738867741)
          ·
            refine ⟨42104997407030370277075403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112279993085414320738867741 42104997407030370277075403)
            ·
              refine ⟨63157496110545555415613105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42104997407030370277075403 63157496110545555415613105)
              ·
                refine ⟨47368122082909166561709829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63157496110545555415613105 47368122082909166561709829)
                ·
                  refine ⟨8881522890545468730320593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47368122082909166561709829 8881522890545468730320593)
                  ·
                    refine ⟨6661142167909101547740445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8881522890545468730320593 6661142167909101547740445)
                    ·
                      refine ⟨2497928312965913080402667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6661142167909101547740445 2497928312965913080402667)
                      ·
                        rfl

theorem cell23_4864698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_4864698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864698 prefixEnd_4864698 := by exact prefixLift 4864698
  have htrace : WordTrace (prefixWord ++ tailWord_4864698) baseStart_4864698 baseEnd_4864698 := by
    simpa [prefixWord, tailWord_4864698, baseEnd_4864698] using wordTrace_append hprefix tailTrace_4864698
  have hstable : (prefixWord ++ tailWord_4864698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864698).length < 2 ^ (prefixWord ++ tailWord_4864698).sum := by decide
  have hdescent : baseEnd_4864698 < baseStart_4864698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864732 : List Nat := [2, 2, 5, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_4864732 : Nat := 118140960795 + 4864732 * 2 ^ 59
def prefixEnd_4864732 : Nat := 4983230072969 + 3 ^ 40 * 4864732 * 2
def baseEnd_4864732 : Nat := 2497945771308165947377511

theorem tailTrace_4864732 : CollatzResearch.WordTrace tailWord_4864732 prefixEnd_4864732 2497945771308165947377511 := by
  unfold tailWord_4864732
  simp only [CollatzResearch.WordTrace]
  refine ⟨88715676305957134462474225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118287568407942845949965633 88715676305957134462474225)
  ·
    refine ⟨66536757229467850846855669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88715676305957134462474225 66536757229467850846855669)
    ·
      refine ⟨6237820990262611016892719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66536757229467850846855669 6237820990262611016892719)
      ·
        refine ⟨9356731485393916525339079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6237820990262611016892719 9356731485393916525339079)
        ·
          refine ⟨14035097228090874788008619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9356731485393916525339079 14035097228090874788008619)
          ·
            refine ⟨21052645842136312182012929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14035097228090874788008619 21052645842136312182012929)
            ·
              refine ⟨15789484381602234136509697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21052645842136312182012929 15789484381602234136509697)
              ·
                refine ⟨11842113286201675602382273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15789484381602234136509697 11842113286201675602382273)
                ·
                  refine ⟨8881584964651256701786705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11842113286201675602382273 8881584964651256701786705)
                  ·
                    refine ⟨6661188723488442526340029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8881584964651256701786705 6661188723488442526340029)
                    ·
                      refine ⟨2497945771308165947377511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6661188723488442526340029 2497945771308165947377511)
                      ·
                        rfl

theorem cell23_4864732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_4864732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864732 prefixEnd_4864732 := by exact prefixLift 4864732
  have htrace : WordTrace (prefixWord ++ tailWord_4864732) baseStart_4864732 baseEnd_4864732 := by
    simpa [prefixWord, tailWord_4864732, baseEnd_4864732] using wordTrace_append hprefix tailTrace_4864732
  have hstable : (prefixWord ++ tailWord_4864732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864732).length < 2 ^ (prefixWord ++ tailWord_4864732).sum := by decide
  have hdescent : baseEnd_4864732 < baseStart_4864732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864739 : List Nat := [1, 1, 1, 7, 1, 1, 4, 2, 1, 4]
def baseStart_4864739 : Nat := 118140960795 + 4864739 * 2 ^ 59
def prefixEnd_4864739 : Nat := 4983230072969 + 3 ^ 40 * 4864739 * 2
def baseEnd_4864739 : Nat := 832649788557582473329993

theorem tailTrace_4864739 : CollatzResearch.WordTrace tailWord_4864739 prefixEnd_4864739 832649788557582473329993 := by
  unfold tailWord_4864739
  simp only [CollatzResearch.WordTrace]
  refine ⟨177431607922888909120453271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118287738615259272746968847 177431607922888909120453271)
  ·
    refine ⟨266147411884333363680679907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177431607922888909120453271 266147411884333363680679907)
    ·
      refine ⟨399221117826500045521019861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266147411884333363680679907 399221117826500045521019861)
      ·
        refine ⟨9356744949058594816898903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 399221117826500045521019861 9356744949058594816898903)
        ·
          refine ⟨14035117423587892225348355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9356744949058594816898903 14035117423587892225348355)
          ·
            refine ⟨21052676135381838338022533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14035117423587892225348355 21052676135381838338022533)
            ·
              refine ⟨3947376775384094688379225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21052676135381838338022533 3947376775384094688379225)
              ·
                refine ⟨2960532581538071016284419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3947376775384094688379225 2960532581538071016284419)
                ·
                  refine ⟨4440798872307106524426629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2960532581538071016284419 4440798872307106524426629)
                  ·
                    refine ⟨832649788557582473329993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4440798872307106524426629 832649788557582473329993)
                    ·
                      rfl

theorem cell23_4864739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 2, 1, 4].length) (baseStart_4864739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864739 prefixEnd_4864739 := by exact prefixLift 4864739
  have htrace : WordTrace (prefixWord ++ tailWord_4864739) baseStart_4864739 baseEnd_4864739 := by
    simpa [prefixWord, tailWord_4864739, baseEnd_4864739] using wordTrace_append hprefix tailTrace_4864739
  have hstable : (prefixWord ++ tailWord_4864739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864739).length < 2 ^ (prefixWord ++ tailWord_4864739).sum := by decide
  have hdescent : baseEnd_4864739 < baseStart_4864739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864758 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_4864758 : Nat := 118140960795 + 4864758 * 2 ^ 59
def prefixEnd_4864758 : Nat := 4983230072969 + 3 ^ 40 * 4864758 * 2
def baseEnd_4864758 : Nat := 2497959121805182845652391

theorem tailTrace_4864758 : CollatzResearch.WordTrace tailWord_4864758 prefixEnd_4864758 2497959121805182845652391 := by
  unfold tailWord_4864758
  simp only [CollatzResearch.WordTrace]
  refine ⟨11089518806863754710337183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118288200606546716910263285 11089518806863754710337183)
  ·
    refine ⟨16634278210295632065505775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11089518806863754710337183 16634278210295632065505775)
    ·
      refine ⟨24951417315443448098258663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16634278210295632065505775 24951417315443448098258663)
      ·
        refine ⟨37427125973165172147387995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24951417315443448098258663 37427125973165172147387995)
        ·
          refine ⟨56140688959747758221081993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37427125973165172147387995 56140688959747758221081993)
          ·
            refine ⟨42105516719810818665811495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56140688959747758221081993 42105516719810818665811495)
            ·
              refine ⟨63158275079716227998717243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42105516719810818665811495 63158275079716227998717243)
              ·
                refine ⟨94737412619574341998075865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63158275079716227998717243 94737412619574341998075865)
                ·
                  refine ⟨71053059464680756498556899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94737412619574341998075865 71053059464680756498556899)
                  ·
                    refine ⟨106579589197021134747835349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71053059464680756498556899 106579589197021134747835349)
                    ·
                      refine ⟨2497959121805182845652391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106579589197021134747835349 2497959121805182845652391)
                      ·
                        rfl

theorem cell23_4864758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_4864758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864758 prefixEnd_4864758 := by exact prefixLift 4864758
  have htrace : WordTrace (prefixWord ++ tailWord_4864758) baseStart_4864758 baseEnd_4864758 := by
    simpa [prefixWord, tailWord_4864758, baseEnd_4864758] using wordTrace_append hprefix tailTrace_4864758
  have hstable : (prefixWord ++ tailWord_4864758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864758).length < 2 ^ (prefixWord ++ tailWord_4864758).sum := by decide
  have hdescent : baseEnd_4864758 < baseStart_4864758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864778 : List Nat := [3, 1, 2, 2, 1, 2, 1, 4, 1, 6]
def baseStart_4864778 : Nat := 118140960795 + 4864778 * 2 ^ 59
def prefixEnd_4864778 : Nat := 4983230072969 + 3 ^ 40 * 4864778 * 2
def baseEnd_4864778 : Nat := 832656463806090922467433

theorem tailTrace_4864778 : CollatzResearch.WordTrace tailWord_4864778 prefixEnd_4864778 832656463806090922467433 := by
  unfold tailWord_4864778
  simp only [CollatzResearch.WordTrace]
  refine ⟨44358257592436904695280747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118288686913165079187415325 44358257592436904695280747)
  ·
    refine ⟨66537386388655357042921121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44358257592436904695280747 66537386388655357042921121)
    ·
      refine ⟨49903039791491517782190841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66537386388655357042921121 49903039791491517782190841)
      ·
        refine ⟨37427279843618638336643131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49903039791491517782190841 37427279843618638336643131)
        ·
          refine ⟨56140919765427957504964697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37427279843618638336643131 56140919765427957504964697)
          ·
            refine ⟨42105689824070968128723523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56140919765427957504964697 42105689824070968128723523)
            ·
              refine ⟨63158534736106452193085285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42105689824070968128723523 63158534736106452193085285)
              ·
                refine ⟨11842225263019959786203491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63158534736106452193085285 11842225263019959786203491)
                ·
                  refine ⟨17763337894529939679305237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11842225263019959786203491 17763337894529939679305237)
                  ·
                    refine ⟨832656463806090922467433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17763337894529939679305237 832656463806090922467433)
                    ·
                      rfl

theorem cell23_4864778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_4864778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864778 prefixEnd_4864778 := by exact prefixLift 4864778
  have htrace : WordTrace (prefixWord ++ tailWord_4864778) baseStart_4864778 baseEnd_4864778 := by
    simpa [prefixWord, tailWord_4864778, baseEnd_4864778] using wordTrace_append hprefix tailTrace_4864778
  have hstable : (prefixWord ++ tailWord_4864778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864778).length < 2 ^ (prefixWord ++ tailWord_4864778).sum := by decide
  have hdescent : baseEnd_4864778 < baseStart_4864778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864808 : List Nat := [2, 1, 5, 1, 1, 1, 2, 10]
def baseStart_4864808 : Nat := 118140960795 + 4864808 * 2 ^ 59
def prefixEnd_4864808 : Nat := 4983230072969 + 3 ^ 40 * 4864808 * 2
def baseEnd_4864808 : Nat := 92517955401403987038043

theorem tailTrace_4864808 : CollatzResearch.WordTrace tailWord_4864808 prefixEnd_4864808 92517955401403987038043 := by
  unfold tailWord_4864808
  simp only [CollatzResearch.WordTrace]
  refine ⟨88717062279819466952357539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118289416373092622603143385 88717062279819466952357539)
  ·
    refine ⟨133075593419729200428536309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88717062279819466952357539 133075593419729200428536309)
    ·
      refine ⟨12475836883099612540175279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133075593419729200428536309 12475836883099612540175279)
      ·
        refine ⟨18713755324649418810262919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12475836883099612540175279 18713755324649418810262919)
        ·
          refine ⟨28070632986974128215394379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18713755324649418810262919 28070632986974128215394379)
          ·
            refine ⟨42105949480461192323091569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28070632986974128215394379 42105949480461192323091569)
            ·
              refine ⟨31579462110345894242318677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42105949480461192323091569 31579462110345894242318677)
              ·
                refine ⟨92517955401403987038043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31579462110345894242318677 92517955401403987038043)
                ·
                  rfl

theorem cell23_4864808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 10].length) (baseStart_4864808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864808 prefixEnd_4864808 := by exact prefixLift 4864808
  have htrace : WordTrace (prefixWord ++ tailWord_4864808) baseStart_4864808 baseEnd_4864808 := by
    simpa [prefixWord, tailWord_4864808, baseEnd_4864808] using wordTrace_append hprefix tailTrace_4864808
  have hstable : (prefixWord ++ tailWord_4864808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864808).length < 2 ^ (prefixWord ++ tailWord_4864808).sum := by decide
  have hdescent : baseEnd_4864808 < baseStart_4864808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864812 : List Nat := [2, 2, 1, 1, 1, 4, 5, 1, 2, 4]
def baseStart_4864812 : Nat := 118140960795 + 4864812 * 2 ^ 59
def prefixEnd_4864812 : Nat := 4983230072969 + 3 ^ 40 * 4864812 * 2
def baseEnd_4864812 : Nat := 832662283253508544792381

theorem tailTrace_4864812 : CollatzResearch.WordTrace tailWord_4864812 prefixEnd_4864812 832662283253508544792381 := by
  unfold tailWord_4864812
  simp only [CollatzResearch.WordTrace]
  refine ⟨88717135225812221293930345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118289513634416295058573793 88717135225812221293930345)
  ·
    refine ⟨66537851419359165970447759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88717135225812221293930345 66537851419359165970447759)
    ·
      refine ⟨99806777129038748955671639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66537851419359165970447759 99806777129038748955671639)
      ·
        refine ⟨149710165693558123433507459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99806777129038748955671639 149710165693558123433507459)
        ·
          refine ⟨224565248540337185150261189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149710165693558123433507459 224565248540337185150261189)
          ·
            refine ⟨42105984101313222215673973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 224565248540337185150261189 42105984101313222215673973)
            ·
              refine ⟨3947436009498114582719435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42105984101313222215673973 3947436009498114582719435)
              ·
                refine ⟨5921154014247171874079153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3947436009498114582719435 5921154014247171874079153)
                ·
                  refine ⟨4440865510685378905559365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5921154014247171874079153 4440865510685378905559365)
                  ·
                    refine ⟨832662283253508544792381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4440865510685378905559365 832662283253508544792381)
                    ·
                      rfl

theorem cell23_4864812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 4].length) (baseStart_4864812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864812 prefixEnd_4864812 := by exact prefixLift 4864812
  have htrace : WordTrace (prefixWord ++ tailWord_4864812) baseStart_4864812 baseEnd_4864812 := by
    simpa [prefixWord, tailWord_4864812, baseEnd_4864812] using wordTrace_append hprefix tailTrace_4864812
  have hstable : (prefixWord ++ tailWord_4864812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864812).length < 2 ^ (prefixWord ++ tailWord_4864812).sum := by decide
  have hdescent : baseEnd_4864812 < baseStart_4864812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864835 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 6, 1, 3]
def baseStart_4864835 : Nat := 118140960795 + 4864835 * 2 ^ 59
def prefixEnd_4864835 : Nat := 4983230072969 + 3 ^ 40 * 4864835 * 2
def baseEnd_4864835 : Nat := 2497998659815579044389537

theorem tailTrace_4864835 : CollatzResearch.WordTrace tailWord_4864835 prefixEnd_4864835 2497998659815579044389537 := by
  unfold tailWord_4864835
  simp only [CollatzResearch.WordTrace]
  refine ⟨177435109330541117515947959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118290072887027411677298639 177435109330541117515947959)
  ·
    refine ⟨266152663995811676273921939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177435109330541117515947959 266152663995811676273921939)
    ·
      refine ⟨399228995993717514410882909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266152663995811676273921939 399228995993717514410882909)
      ·
        refine ⟨149710873497644067904081091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 399228995993717514410882909 149710873497644067904081091)
        ·
          refine ⟨224566310246466101856121637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149710873497644067904081091 224566310246466101856121637)
          ·
            refine ⟨42106183171212394098022807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 224566310246466101856121637 42106183171212394098022807)
            ·
              refine ⟨63159274756818591147034211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42106183171212394098022807 63159274756818591147034211)
              ·
                refine ⟨94738912135227886720551317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63159274756818591147034211 94738912135227886720551317)
                ·
                  refine ⟨4440886506338807190025843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94738912135227886720551317 4440886506338807190025843)
                  ·
                    refine ⟨6661329759508210785038765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4440886506338807190025843 6661329759508210785038765)
                    ·
                      refine ⟨2497998659815579044389537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6661329759508210785038765 2497998659815579044389537)
                      ·
                        rfl

theorem cell23_4864835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 1, 3].length) (baseStart_4864835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864835 prefixEnd_4864835 := by exact prefixLift 4864835
  have htrace : WordTrace (prefixWord ++ tailWord_4864835) baseStart_4864835 baseEnd_4864835 := by
    simpa [prefixWord, tailWord_4864835, baseEnd_4864835] using wordTrace_append hprefix tailTrace_4864835
  have hstable : (prefixWord ++ tailWord_4864835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864835).length < 2 ^ (prefixWord ++ tailWord_4864835).sum := by decide
  have hdescent : baseEnd_4864835 < baseStart_4864835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864869 : List Nat := [1, 3, 1, 3, 1, 1, 6, 1, 2, 1, 3]
def baseStart_4864869 : Nat := 118140960795 + 4864869 * 2 ^ 59
def prefixEnd_4864869 : Nat := 4983230072969 + 3 ^ 40 * 4864869 * 2
def baseEnd_4864869 : Nat := 2498016118157831911364381

theorem tailTrace_4864869 : CollatzResearch.WordTrace tailWord_4864869 prefixEnd_4864869 2498016118157831911364381 := by
  unfold tailWord_4864869
  simp only [CollatzResearch.WordTrace]
  refine ⟨177436349412417941322685661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118290899608278627548457107 177436349412417941322685661)
  ·
    refine ⟨66538631029656727996007123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177436349412417941322685661 66538631029656727996007123)
    ·
      refine ⟨99807946544485091994010685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66538631029656727996007123 99807946544485091994010685)
      ·
        refine ⟨37427979954181909497754007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99807946544485091994010685 37427979954181909497754007)
        ·
          refine ⟨56141969931272864246631011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37427979954181909497754007 56141969931272864246631011)
          ·
            refine ⟨84212954896909296369946517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56141969931272864246631011 84212954896909296369946517)
            ·
              refine ⟨3947482260792623267341243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 84212954896909296369946517 3947482260792623267341243)
              ·
                refine ⟨5921223391188934901011865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3947482260792623267341243 5921223391188934901011865)
                ·
                  refine ⟨4440917543391701175758899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5921223391188934901011865 4440917543391701175758899)
                  ·
                    refine ⟨6661376315087551763638349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4440917543391701175758899 6661376315087551763638349)
                    ·
                      refine ⟨2498016118157831911364381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6661376315087551763638349 2498016118157831911364381)
                      ·
                        rfl

theorem cell23_4864869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_4864869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864869 prefixEnd_4864869 := by exact prefixLift 4864869
  have htrace : WordTrace (prefixWord ++ tailWord_4864869) baseStart_4864869 baseEnd_4864869 := by
    simpa [prefixWord, tailWord_4864869, baseEnd_4864869] using wordTrace_append hprefix tailTrace_4864869
  have hstable : (prefixWord ++ tailWord_4864869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864869).length < 2 ^ (prefixWord ++ tailWord_4864869).sum := by decide
  have hdescent : baseEnd_4864869 < baseStart_4864869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864888 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 3, 4, 4]
def baseStart_4864888 : Nat := 118140960795 + 4864888 * 2 ^ 59
def prefixEnd_4864888 : Nat := 4983230072969 + 3 ^ 40 * 4864888 * 2
def baseEnd_4864888 : Nat := 2498025874290267337026793

theorem tailTrace_4864888 : CollatzResearch.WordTrace tailWord_4864888 prefixEnd_4864888 2498025874290267337026793 := by
  unfold tailWord_4864888
  simp only [CollatzResearch.WordTrace]
  refine ⟨88718521199674553783813659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118291361599566071711751545 88718521199674553783813659)
  ·
    refine ⟨133077781799511830675720489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88718521199674553783813659 133077781799511830675720489)
    ·
      refine ⟨99808336349633873006790367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133077781799511830675720489 99808336349633873006790367)
      ·
        refine ⟨149712504524450809510185551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99808336349633873006790367 149712504524450809510185551)
        ·
          refine ⟨224568756786676214265278327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149712504524450809510185551 224568756786676214265278327)
          ·
            refine ⟨336853135180014321397917491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224568756786676214265278327 336853135180014321397917491)
            ·
              refine ⟨505279702770021482096876237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336853135180014321397917491 505279702770021482096876237)
              ·
                refine ⟨189479888538758055786328589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 505279702770021482096876237 189479888538758055786328589)
                ·
                  refine ⟨71054958202034270919873221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189479888538758055786328589 71054958202034270919873221)
                  ·
                    refine ⟨13322804662881425797476229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71054958202034270919873221 13322804662881425797476229)
                    ·
                      refine ⟨2498025874290267337026793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13322804662881425797476229 2498025874290267337026793)
                      ·
                        rfl

theorem cell23_4864888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 4, 4].length) (baseStart_4864888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864888 prefixEnd_4864888 := by exact prefixLift 4864888
  have htrace : WordTrace (prefixWord ++ tailWord_4864888) baseStart_4864888 baseEnd_4864888 := by
    simpa [prefixWord, tailWord_4864888, baseEnd_4864888] using wordTrace_append hprefix tailTrace_4864888
  have hstable : (prefixWord ++ tailWord_4864888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864888).length < 2 ^ (prefixWord ++ tailWord_4864888).sum := by decide
  have hdescent : baseEnd_4864888 < baseStart_4864888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864892 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 6, 2, 2]
def baseStart_4864892 : Nat := 118140960795 + 4864892 * 2 ^ 59
def prefixEnd_4864892 : Nat := 4983230072969 + 3 ^ 40 * 4864892 * 2
def baseEnd_4864892 : Nat := 2498027928212885321376775

theorem tailTrace_4864892 : CollatzResearch.WordTrace tailWord_4864892 prefixEnd_4864892 2498027928212885321376775 := by
  unfold tailWord_4864892
  simp only [CollatzResearch.WordTrace]
  refine ⟨88718594145667308125386465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118291458860889744167181953 88718594145667308125386465)
  ·
    refine ⟨66538945609250481094039849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88718594145667308125386465 66538945609250481094039849)
    ·
      refine ⟨49904209206937860820529887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66538945609250481094039849 49904209206937860820529887)
      ·
        refine ⟨74856313810406791230794831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49904209206937860820529887 74856313810406791230794831)
        ·
          refine ⟨112284470715610186846192247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74856313810406791230794831 112284470715610186846192247)
          ·
            refine ⟨168426706073415280269288371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112284470715610186846192247 168426706073415280269288371)
            ·
              refine ⟨252640059110122920403932557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168426706073415280269288371 252640059110122920403932557)
              ·
                refine ⟨94740022166296095151474709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 252640059110122920403932557 94740022166296095151474709)
                ·
                  refine ⟨4440938539045129460225377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94740022166296095151474709 4440938539045129460225377)
                  ·
                    refine ⟨3330703904283847095169033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4440938539045129460225377 3330703904283847095169033)
                    ·
                      refine ⟨2498027928212885321376775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3330703904283847095169033 2498027928212885321376775)
                      ·
                        rfl

theorem cell23_4864892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_4864892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864892 prefixEnd_4864892 := by exact prefixLift 4864892
  have htrace : WordTrace (prefixWord ++ tailWord_4864892) baseStart_4864892 baseEnd_4864892 := by
    simpa [prefixWord, tailWord_4864892, baseEnd_4864892] using wordTrace_append hprefix tailTrace_4864892
  have hstable : (prefixWord ++ tailWord_4864892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864892).length < 2 ^ (prefixWord ++ tailWord_4864892).sum := by decide
  have hdescent : baseEnd_4864892 < baseStart_4864892 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864908 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 1, 2, 7]
def baseStart_4864908 : Nat := 118140960795 + 4864908 * 2 ^ 59
def prefixEnd_4864908 : Nat := 4983230072969 + 3 ^ 40 * 4864908 * 2
def baseEnd_4864908 : Nat := 2498036143903357258776701

theorem tailTrace_4864908 : CollatzResearch.WordTrace tailWord_4864908 prefixEnd_4864908 2498036143903357258776701 := by
  unfold tailWord_4864908
  simp only [CollatzResearch.WordTrace]
  refine ⟨88718885929638325491677689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118291847906184433988903585 88718885929638325491677689)
  ·
    refine ⟨66539164447228744118758267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88718885929638325491677689 66539164447228744118758267)
    ·
      refine ⟨99808746670843116178137401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66539164447228744118758267 99808746670843116178137401)
      ·
        refine ⟨74856560003132337133603051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99808746670843116178137401 74856560003132337133603051)
        ·
          refine ⟨112284840004698505700404577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74856560003132337133603051 112284840004698505700404577)
          ·
            refine ⟨84213630003523879275303433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112284840004698505700404577 84213630003523879275303433)
            ·
              refine ⟨63160222502642909456477575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84213630003523879275303433 63160222502642909456477575)
              ·
                refine ⟨94740333753964364184716363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63160222502642909456477575 94740333753964364184716363)
                ·
                  refine ⟨142110500630946546277074545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94740333753964364184716363 142110500630946546277074545)
                  ·
                    refine ⟨106582875473209909707805909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 142110500630946546277074545 106582875473209909707805909)
                    ·
                      refine ⟨2498036143903357258776701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106582875473209909707805909 2498036143903357258776701)
                      ·
                        rfl

theorem cell23_4864908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_4864908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864908 prefixEnd_4864908 := by exact prefixLift 4864908
  have htrace : WordTrace (prefixWord ++ tailWord_4864908) baseStart_4864908 baseEnd_4864908 := by
    simpa [prefixWord, tailWord_4864908, baseEnd_4864908] using wordTrace_append hprefix tailTrace_4864908
  have hstable : (prefixWord ++ tailWord_4864908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864908).length < 2 ^ (prefixWord ++ tailWord_4864908).sum := by decide
  have hdescent : baseEnd_4864908 < baseStart_4864908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864922 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4]
def baseStart_4864922 : Nat := 118140960795 + 4864922 * 2 ^ 59
def prefixEnd_4864922 : Nat := 4983230072969 + 3 ^ 40 * 4864922 * 2
def baseEnd_4864922 : Nat := 2498043332632520204001637

theorem tailTrace_4864922 : CollatzResearch.WordTrace tailWord_4864922 prefixEnd_4864922 2498043332632520204001637 := by
  unfold tailWord_4864922
  simp only [CollatzResearch.WordTrace]
  refine ⟨44359570620306482843591255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118292188320817287582910013 44359570620306482843591255)
  ·
    refine ⟨66539355930459724265386883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44359570620306482843591255 66539355930459724265386883)
    ·
      refine ⟨99809033895689586398080325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66539355930459724265386883 99809033895689586398080325)
      ·
        refine ⟨18714193855441797449640061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99809033895689586398080325 18714193855441797449640061)
        ·
          refine ⟨7017822695790674043615023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18714193855441797449640061 7017822695790674043615023)
          ·
            refine ⟨10526734043686011065422535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7017822695790674043615023 10526734043686011065422535)
            ·
              refine ⟨15790101065529016598133803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10526734043686011065422535 15790101065529016598133803)
              ·
                refine ⟨23685151598293524897200705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15790101065529016598133803 23685151598293524897200705)
                ·
                  refine ⟨17763863698720143672900529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23685151598293524897200705 17763863698720143672900529)
                  ·
                    refine ⟨13322897774040107754675397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17763863698720143672900529 13322897774040107754675397)
                    ·
                      refine ⟨2498043332632520204001637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13322897774040107754675397 2498043332632520204001637)
                      ·
                        rfl

theorem cell23_4864922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_4864922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864922 prefixEnd_4864922 := by exact prefixLift 4864922
  have htrace : WordTrace (prefixWord ++ tailWord_4864922) baseStart_4864922 baseEnd_4864922 := by
    simpa [prefixWord, tailWord_4864922, baseEnd_4864922] using wordTrace_append hprefix tailTrace_4864922
  have hstable : (prefixWord ++ tailWord_4864922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864922).length < 2 ^ (prefixWord ++ tailWord_4864922).sum := by decide
  have hdescent : baseEnd_4864922 < baseStart_4864922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4864995 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 4]
def baseStart_4864995 : Nat := 118140960795 + 4864995 * 2 ^ 59
def prefixEnd_4864995 : Nat := 4983230072969 + 3 ^ 40 * 4864995 * 2
def baseEnd_4864995 : Nat := 2498080816720298418388801

theorem tailTrace_4864995 : CollatzResearch.WordTrace tailWord_4864995 prefixEnd_4864995 2498080816720298418388801 := by
  unfold tailWord_4864995
  simp only [CollatzResearch.WordTrace]
  refine ⟨177440945009961464841772439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118293963339974309894514959 177440945009961464841772439)
  ·
    refine ⟨266161417514942197262658659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177440945009961464841772439 266161417514942197262658659)
    ·
      refine ⟨399242126272413295893987989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266161417514942197262658659 399242126272413295893987989)
      ·
        refine ⟨18714474669019373245030687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 399242126272413295893987989 18714474669019373245030687)
        ·
          refine ⟨28071712003529059867546031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18714474669019373245030687 28071712003529059867546031)
          ·
            refine ⟨42107568005293589801319047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28071712003529059867546031 42107568005293589801319047)
            ·
              refine ⟨63161352007940384701978571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42107568005293589801319047 63161352007940384701978571)
              ·
                refine ⟨94742028011910577052967857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63161352007940384701978571 94742028011910577052967857)
                ·
                  refine ⟨71056521008932932789725893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94742028011910577052967857 71056521008932932789725893)
                  ·
                    refine ⟨13323097689174924898073605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71056521008932932789725893 13323097689174924898073605)
                    ·
                      refine ⟨2498080816720298418388801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13323097689174924898073605 2498080816720298418388801)
                      ·
                        rfl

theorem cell23_4864995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_4864995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4864995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4864995 prefixEnd_4864995 := by exact prefixLift 4864995
  have htrace : WordTrace (prefixWord ++ tailWord_4864995) baseStart_4864995 baseEnd_4864995 := by
    simpa [prefixWord, tailWord_4864995, baseEnd_4864995] using wordTrace_append hprefix tailTrace_4864995
  have hstable : (prefixWord ++ tailWord_4864995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4864995).length < 2 ^ (prefixWord ++ tailWord_4864995).sum := by decide
  have hdescent : baseEnd_4864995 < baseStart_4864995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4864995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865002 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_4865002 : Nat := 118140960795 + 4865002 * 2 ^ 59
def prefixEnd_4865002 : Nat := 4983230072969 + 3 ^ 40 * 4865002 * 2
def baseEnd_4865002 : Nat := 2498084411084879891001269

theorem tailTrace_4865002 : CollatzResearch.WordTrace tailWord_4865002 prefixEnd_4865002 2498084411084879891001269 := by
  unfold tailWord_4865002
  simp only [CollatzResearch.WordTrace]
  refine ⟨44360300080234026259319315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118294133547290736691518173 44360300080234026259319315)
  ·
    refine ⟨66540450120351039388978973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44360300080234026259319315 66540450120351039388978973)
    ·
      refine ⟨24952668795131639770867115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66540450120351039388978973 24952668795131639770867115)
      ·
        refine ⟨37429003192697459656300673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24952668795131639770867115 37429003192697459656300673)
        ·
          refine ⟨28071752394523094742225505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37429003192697459656300673 28071752394523094742225505)
          ·
            refine ⟨21053814295892321056669129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28071752394523094742225505 21053814295892321056669129)
            ·
              refine ⟨15790360721919240792501847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21053814295892321056669129 15790360721919240792501847)
              ·
                refine ⟨23685541082878861188752771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15790360721919240792501847 23685541082878861188752771)
                ·
                  refine ⟨35528311624318291783129157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23685541082878861188752771 35528311624318291783129157)
                  ·
                    refine ⟨6661558429559679709336717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35528311624318291783129157 6661558429559679709336717)
                    ·
                      refine ⟨2498084411084879891001269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6661558429559679709336717 2498084411084879891001269)
                      ·
                        rfl

theorem cell23_4865002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_4865002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865002 prefixEnd_4865002 := by exact prefixLift 4865002
  have htrace : WordTrace (prefixWord ++ tailWord_4865002) baseStart_4865002 baseEnd_4865002 := by
    simpa [prefixWord, tailWord_4865002, baseEnd_4865002] using wordTrace_append hprefix tailTrace_4865002
  have hstable : (prefixWord ++ tailWord_4865002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865002).length < 2 ^ (prefixWord ++ tailWord_4865002).sum := by decide
  have hdescent : baseEnd_4865002 < baseStart_4865002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865059 : List Nat := [1, 1, 1, 4, 3, 2, 1, 3, 2, 3, 2]
def baseStart_4865059 : Nat := 118140960795 + 4865059 * 2 ^ 59
def prefixEnd_4865059 : Nat := 4983230072969 + 3 ^ 40 * 4865059 * 2
def baseEnd_4865059 : Nat := 2498113679482186167988507

theorem tailTrace_4865059 : CollatzResearch.WordTrace tailWord_4865059 prefixEnd_4865059 2498113679482186167988507 := by
  unfold tailWord_4865059
  simp only [CollatzResearch.WordTrace]
  refine ⟨177443279281729603772102231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118295519521153069181401487 177443279281729603772102231)
  ·
    refine ⟨266164918922594405658153347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177443279281729603772102231 266164918922594405658153347)
    ·
      refine ⟨399247378383891608487230021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266164918922594405658153347 399247378383891608487230021)
      ·
        refine ⟨74858883446979676591355629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 399247378383891608487230021 74858883446979676591355629)
        ·
          refine ⟨28072081292617378721758361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74858883446979676591355629 28072081292617378721758361)
          ·
            refine ⟨21054060969463034041318771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28072081292617378721758361 21054060969463034041318771)
            ·
              refine ⟨31581091454194551061978157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21054060969463034041318771 31581091454194551061978157)
              ·
                refine ⟨11842909295322956648241809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31581091454194551061978157 11842909295322956648241809)
                ·
                  refine ⟨8882181971492217486181357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11842909295322956648241809 8882181971492217486181357)
                  ·
                    refine ⟨3330818239309581557318009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8882181971492217486181357 3330818239309581557318009)
                    ·
                      refine ⟨2498113679482186167988507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3330818239309581557318009 2498113679482186167988507)
                      ·
                        rfl

theorem cell23_4865059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_4865059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865059 prefixEnd_4865059 := by exact prefixLift 4865059
  have htrace : WordTrace (prefixWord ++ tailWord_4865059) baseStart_4865059 baseEnd_4865059 := by
    simpa [prefixWord, tailWord_4865059, baseEnd_4865059] using wordTrace_append hprefix tailTrace_4865059
  have hstable : (prefixWord ++ tailWord_4865059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865059).length < 2 ^ (prefixWord ++ tailWord_4865059).sum := by decide
  have hdescent : baseEnd_4865059 < baseStart_4865059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865082 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 4, 4]
def baseStart_4865082 : Nat := 118140960795 + 4865082 * 2 ^ 59
def prefixEnd_4865082 : Nat := 4983230072969 + 3 ^ 40 * 4865082 * 2
def baseEnd_4865082 : Nat := 832708496512413192666967

theorem tailTrace_4865082 : CollatzResearch.WordTrace tailWord_4865082 prefixEnd_4865082 832708496512413192666967 := by
  unfold tailWord_4865082
  simp only [CollatzResearch.WordTrace]
  refine ⟨44361029540161569675047375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118296078773764185800126333 44361029540161569675047375)
  ·
    refine ⟨66541544310242354512571063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44361029540161569675047375 66541544310242354512571063)
    ·
      refine ⟨99812316465363531768856595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66541544310242354512571063 99812316465363531768856595)
      ·
        refine ⟨149718474698045297653284893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99812316465363531768856595 149718474698045297653284893)
        ·
          refine ⟨56144428011766986619981835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149718474698045297653284893 56144428011766986619981835)
          ·
            refine ⟨84216642017650479929972753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56144428011766986619981835 84216642017650479929972753)
            ·
              refine ⟨63162481513237859947479565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84216642017650479929972753 63162481513237859947479565)
              ·
                refine ⟨23685930567464197480304837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63162481513237859947479565 23685930567464197480304837)
                ·
                  refine ⟨4441111981399537027557157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23685930567464197480304837 4441111981399537027557157)
                  ·
                    refine ⟨832708496512413192666967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4441111981399537027557157 832708496512413192666967)
                    ·
                      rfl

theorem cell23_4865082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 4, 4].length) (baseStart_4865082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865082 prefixEnd_4865082 := by exact prefixLift 4865082
  have htrace : WordTrace (prefixWord ++ tailWord_4865082) baseStart_4865082 baseEnd_4865082 := by
    simpa [prefixWord, tailWord_4865082, baseEnd_4865082] using wordTrace_append hprefix tailTrace_4865082
  have hstable : (prefixWord ++ tailWord_4865082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865082).length < 2 ^ (prefixWord ++ tailWord_4865082).sum := by decide
  have hdescent : baseEnd_4865082 < baseStart_4865082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865106 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 5, 2, 2]
def baseStart_4865106 : Nat := 118140960795 + 4865106 * 2 ^ 59
def prefixEnd_4865106 : Nat := 4983230072969 + 3 ^ 40 * 4865106 * 2
def baseEnd_4865106 : Nat := 2498137813072947484100791

theorem tailTrace_4865106 : CollatzResearch.WordTrace tailWord_4865106 prefixEnd_4865106 2498137813072947484100791 := by
  unfold tailWord_4865106
  simp only [CollatzResearch.WordTrace]
  refine ⟨44361248378139832699765793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118296662341706220532708781 44361248378139832699765793)
  ·
    refine ⟨33270936283604874524824345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44361248378139832699765793 33270936283604874524824345)
    ·
      refine ⟨24953202212703655893618259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33270936283604874524824345 24953202212703655893618259)
      ·
        refine ⟨37429803319055483840427389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24953202212703655893618259 37429803319055483840427389)
        ·
          refine ⟨14036176244645806440160271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37429803319055483840427389 14036176244645806440160271)
          ·
            refine ⟨21054264366968709660240407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14036176244645806440160271 21054264366968709660240407)
            ·
              refine ⟨31581396550453064490360611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21054264366968709660240407 31581396550453064490360611)
              ·
                refine ⟨47372094825679596735540917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31581396550453064490360611 47372094825679596735540917)
                ·
                  refine ⟨4441133889907462193956961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47372094825679596735540917 4441133889907462193956961)
                  ·
                    refine ⟨3330850417430596645467721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4441133889907462193956961 3330850417430596645467721)
                    ·
                      refine ⟨2498137813072947484100791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3330850417430596645467721 2498137813072947484100791)
                      ·
                        rfl

theorem cell23_4865106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_4865106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865106 prefixEnd_4865106 := by exact prefixLift 4865106
  have htrace : WordTrace (prefixWord ++ tailWord_4865106) baseStart_4865106 baseEnd_4865106 := by
    simpa [prefixWord, tailWord_4865106, baseEnd_4865106] using wordTrace_append hprefix tailTrace_4865106
  have hstable : (prefixWord ++ tailWord_4865106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865106).length < 2 ^ (prefixWord ++ tailWord_4865106).sum := by decide
  have hdescent : baseEnd_4865106 < baseStart_4865106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865109 : List Nat := [1, 3, 2, 2, 1, 2, 2, 4, 1, 2, 3]
def baseStart_4865109 : Nat := 118140960795 + 4865109 * 2 ^ 59
def prefixEnd_4865109 : Nat := 4983230072969 + 3 ^ 40 * 4865109 * 2
def baseEnd_4865109 : Nat := 2498139353514910972363277

theorem tailTrace_4865109 : CollatzResearch.WordTrace tailWord_4865109 prefixEnd_4865109 2498139353514910972363277 := by
  unfold tailWord_4865109
  simp only [CollatzResearch.WordTrace]
  refine ⟨177445102931548462311422381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118296735287698974874281587 177445102931548462311422381)
  ·
    refine ⟨66541913599330673366783393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177445102931548462311422381 66541913599330673366783393)
    ·
      refine ⟨49906435199498005025087545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66541913599330673366783393 49906435199498005025087545)
      ·
        refine ⟨37429826399623503768815659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49906435199498005025087545 37429826399623503768815659)
        ·
          refine ⟨56144739599435255653223489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37429826399623503768815659 56144739599435255653223489)
          ·
            refine ⟨42108554699576441739917617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56144739599435255653223489 42108554699576441739917617)
            ·
              refine ⟨31581416024682331304938213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42108554699576441739917617 31581416024682331304938213)
              ·
                refine ⟨5921515504627937119675915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31581416024682331304938213 5921515504627937119675915)
                ·
                  refine ⟨8882273256941905679513873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5921515504627937119675915 8882273256941905679513873)
                  ·
                    refine ⟨6661704942706429259635405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8882273256941905679513873 6661704942706429259635405)
                    ·
                      refine ⟨2498139353514910972363277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6661704942706429259635405 2498139353514910972363277)
                      ·
                        rfl

theorem cell23_4865109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_4865109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865109 prefixEnd_4865109 := by exact prefixLift 4865109
  have htrace : WordTrace (prefixWord ++ tailWord_4865109) baseStart_4865109 baseEnd_4865109 := by
    simpa [prefixWord, tailWord_4865109, baseEnd_4865109] using wordTrace_append hprefix tailTrace_4865109
  have hstable : (prefixWord ++ tailWord_4865109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865109).length < 2 ^ (prefixWord ++ tailWord_4865109).sum := by decide
  have hdescent : baseEnd_4865109 < baseStart_4865109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865112 : List Nat := [2, 1, 2, 2, 1, 3, 5, 7]
def baseStart_4865112 : Nat := 118140960795 + 4865112 * 2 ^ 59
def prefixEnd_4865112 : Nat := 4983230072969 + 3 ^ 40 * 4865112 * 2
def baseEnd_4865112 : Nat := 92523736813217572615769

theorem tailTrace_4865112 : CollatzResearch.WordTrace tailWord_4865112 prefixEnd_4865112 92523736813217572615769 := by
  unfold tailWord_4865112
  simp only [CollatzResearch.WordTrace]
  refine ⟨88722606175268796911890795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118296808233691729215854393 88722606175268796911890795)
  ·
    refine ⟨133083909262903195367836193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88722606175268796911890795 133083909262903195367836193)
    ·
      refine ⟨99812931947177396525877145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133083909262903195367836193 99812931947177396525877145)
      ·
        refine ⟨74859698960383047394407859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99812931947177396525877145 74859698960383047394407859)
        ·
          refine ⟨112289548440574571091611789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74859698960383047394407859 112289548440574571091611789)
          ·
            refine ⟨42108580665215464159354421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112289548440574571091611789 42108580665215464159354421)
            ·
              refine ⟨3947679437363949764939477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42108580665215464159354421 3947679437363949764939477)
              ·
                refine ⟨92523736813217572615769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3947679437363949764939477 92523736813217572615769)
                ·
                  rfl

theorem cell23_4865112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 7].length) (baseStart_4865112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865112 prefixEnd_4865112 := by exact prefixLift 4865112
  have htrace : WordTrace (prefixWord ++ tailWord_4865112) baseStart_4865112 baseEnd_4865112 := by
    simpa [prefixWord, tailWord_4865112, baseEnd_4865112] using wordTrace_append hprefix tailTrace_4865112
  have hstable : (prefixWord ++ tailWord_4865112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865112).length < 2 ^ (prefixWord ++ tailWord_4865112).sum := by decide
  have hdescent : baseEnd_4865112 < baseStart_4865112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865150 : List Nat := [4, 2, 4, 1, 1, 2, 1, 1, 1, 6]
def baseStart_4865150 : Nat := 118140960795 + 4865150 * 2 ^ 59
def prefixEnd_4865150 : Nat := 4983230072969 + 3 ^ 40 * 4865150 * 2
def baseEnd_4865150 : Nat := 832720135407248437316863

theorem tailTrace_4865150 : CollatzResearch.WordTrace tailWord_4865150 prefixEnd_4865150 832720135407248437316863 := by
  unfold tailWord_4865150
  simp only [CollatzResearch.WordTrace]
  refine ⟨22180824790549990789208113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118297732216266617542443269 22180824790549990789208113)
  ·
    refine ⟨16635618592912493091906085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22180824790549990789208113 16635618592912493091906085)
    ·
      refine ⟨3119178486171092454732391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16635618592912493091906085 3119178486171092454732391)
      ·
        refine ⟨4678767729256638682098587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3119178486171092454732391 4678767729256638682098587)
        ·
          refine ⟨7018151593884958023147881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4678767729256638682098587 7018151593884958023147881)
          ·
            refine ⟨5263613695413718517360911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7018151593884958023147881 5263613695413718517360911)
            ·
              refine ⟨7895420543120577776041367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5263613695413718517360911 7895420543120577776041367)
              ·
                refine ⟨11843130814680866664062051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7895420543120577776041367 11843130814680866664062051)
                ·
                  refine ⟨17764696222021299996093077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11843130814680866664062051 17764696222021299996093077)
                  ·
                    refine ⟨832720135407248437316863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17764696222021299996093077 832720135407248437316863)
                    ·
                      rfl

theorem cell23_4865150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_4865150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865150 prefixEnd_4865150 := by exact prefixLift 4865150
  have htrace : WordTrace (prefixWord ++ tailWord_4865150) baseStart_4865150 baseEnd_4865150 := by
    simpa [prefixWord, tailWord_4865150, baseEnd_4865150] using wordTrace_append hprefix tailTrace_4865150
  have hstable : (prefixWord ++ tailWord_4865150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865150).length < 2 ^ (prefixWord ++ tailWord_4865150).sum := by decide
  have hdescent : baseEnd_4865150 < baseStart_4865150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865156 : List Nat := [2, 3, 2, 1, 2, 4, 1, 1, 1, 3, 3]
def baseStart_4865156 : Nat := 118140960795 + 4865156 * 2 ^ 59
def prefixEnd_4865156 : Nat := 4983230072969 + 3 ^ 40 * 4865156 * 2
def baseEnd_4865156 : Nat := 2498163487105672288475561

theorem tailTrace_4865156 : CollatzResearch.WordTrace tailWord_4865156 prefixEnd_4865156 2498163487105672288475561 := by
  unfold tailWord_4865156
  simp only [CollatzResearch.WordTrace]
  refine ⟨88723408581189094669191661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118297878108252126225588881 88723408581189094669191661)
  ·
    refine ⟨33271278217945910500946873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88723408581189094669191661 33271278217945910500946873)
    ·
      refine ⟨24953458663459432875710155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33271278217945910500946873 24953458663459432875710155)
      ·
        refine ⟨37430187995189149313565233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24953458663459432875710155 37430187995189149313565233)
        ·
          refine ⟨28072640996391861985173925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37430187995189149313565233 28072640996391861985173925)
          ·
            refine ⟨5263620186823474122220111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28072640996391861985173925 5263620186823474122220111)
            ·
              refine ⟨7895430280235211183330167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5263620186823474122220111 7895430280235211183330167)
              ·
                refine ⟨11843145420352816774995251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7895430280235211183330167 11843145420352816774995251)
                ·
                  refine ⟨17764718130529225162492877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11843145420352816774995251 17764718130529225162492877)
                  ·
                    refine ⟨6661769298948459435934829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17764718130529225162492877 6661769298948459435934829)
                    ·
                      refine ⟨2498163487105672288475561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6661769298948459435934829 2498163487105672288475561)
                      ·
                        rfl

theorem cell23_4865156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_4865156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865156 prefixEnd_4865156 := by exact prefixLift 4865156
  have htrace : WordTrace (prefixWord ++ tailWord_4865156) baseStart_4865156 baseEnd_4865156 := by
    simpa [prefixWord, tailWord_4865156, baseEnd_4865156] using wordTrace_append hprefix tailTrace_4865156
  have hstable : (prefixWord ++ tailWord_4865156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865156).length < 2 ^ (prefixWord ++ tailWord_4865156).sum := by decide
  have hdescent : baseEnd_4865156 < baseStart_4865156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865249 : List Nat := [1, 2, 3, 1, 3, 2, 2, 2, 2, 5]
def baseStart_4865249 : Nat := 118140960795 + 4865249 * 2 ^ 59
def prefixEnd_4865249 : Nat := 4983230072969 + 3 ^ 40 * 4865249 * 2
def baseEnd_4865249 : Nat := 832737080268846808204211

theorem tailTrace_4865249 : CollatzResearch.WordTrace tailWord_4865249 prefixEnd_4865249 832737080268846808204211 := by
  unfold tailWord_4865249
  simp only [CollatzResearch.WordTrace]
  refine ⟨177450209151041266221518801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118300139434027510814345867 177450209151041266221518801)
  ·
    refine ⟨133087656863280949666139101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177450209151041266221518801 133087656863280949666139101)
    ·
      refine ⟨49907871323730356124802163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133087656863280949666139101 49907871323730356124802163)
      ·
        refine ⟨74861806985595534187203245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49907871323730356124802163 74861806985595534187203245)
        ·
          refine ⟨28073177619598325320201217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74861806985595534187203245 28073177619598325320201217)
          ·
            refine ⟨21054883214698743990150913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28073177619598325320201217 21054883214698743990150913)
            ·
              refine ⟨15791162411024057992613185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21054883214698743990150913 15791162411024057992613185)
              ·
                refine ⟨11843371808268043494459889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15791162411024057992613185 11843371808268043494459889)
                ·
                  refine ⟨8882528856201032620844917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11843371808268043494459889 8882528856201032620844917)
                  ·
                    refine ⟨832737080268846808204211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8882528856201032620844917 832737080268846808204211)
                    ·
                      rfl

theorem cell23_4865249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_4865249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865249 prefixEnd_4865249 := by exact prefixLift 4865249
  have htrace : WordTrace (prefixWord ++ tailWord_4865249) baseStart_4865249 baseEnd_4865249 := by
    simpa [prefixWord, tailWord_4865249, baseEnd_4865249] using wordTrace_append hprefix tailTrace_4865249
  have hstable : (prefixWord ++ tailWord_4865249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865249).length < 2 ^ (prefixWord ++ tailWord_4865249).sum := by decide
  have hdescent : baseEnd_4865249 < baseStart_4865249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865279 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 5, 4]
def baseStart_4865279 : Nat := 118140960795 + 4865279 * 2 ^ 59
def prefixEnd_4865279 : Nat := 4983230072969 + 3 ^ 40 * 4865279 * 2
def baseEnd_4865279 : Nat := 832742215075391769079165

theorem tailTrace_4865279 : CollatzResearch.WordTrace tailWord_4865279 prefixEnd_4865279 832742215075391769079165 := by
  unfold tailWord_4865279
  simp only [CollatzResearch.WordTrace]
  refine ⟨177451303340932581345110891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118300868893955054230073927 177451303340932581345110891)
  ·
    refine ⟨266176955011398872017666337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177451303340932581345110891 266176955011398872017666337)
    ·
      refine ⟨199632716258549154013249753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266176955011398872017666337 199632716258549154013249753)
      ·
        refine ⟨149724537193911865509937315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199632716258549154013249753 149724537193911865509937315)
        ·
          refine ⟨224586805790867798264905973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149724537193911865509937315 224586805790867798264905973)
          ·
            refine ⟨21055013042893856087334935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 224586805790867798264905973 21055013042893856087334935)
            ·
              refine ⟨31582519564340784131002403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21055013042893856087334935 31582519564340784131002403)
              ·
                refine ⟨47373779346511176196503605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31582519564340784131002403 47373779346511176196503605)
                ·
                  refine ⟨4441291813735422768422213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47373779346511176196503605 4441291813735422768422213)
                  ·
                    refine ⟨832742215075391769079165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4441291813735422768422213 832742215075391769079165)
                    ·
                      rfl

theorem cell23_4865279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 5, 4].length) (baseStart_4865279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865279 prefixEnd_4865279 := by exact prefixLift 4865279
  have htrace : WordTrace (prefixWord ++ tailWord_4865279) baseStart_4865279 baseEnd_4865279 := by
    simpa [prefixWord, tailWord_4865279, baseEnd_4865279] using wordTrace_append hprefix tailTrace_4865279
  have hstable : (prefixWord ++ tailWord_4865279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865279).length < 2 ^ (prefixWord ++ tailWord_4865279).sum := by decide
  have hdescent : baseEnd_4865279 < baseStart_4865279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865289 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 1, 4, 3]
def baseStart_4865289 : Nat := 118140960795 + 4865289 * 2 ^ 59
def prefixEnd_4865289 : Nat := 4983230072969 + 3 ^ 40 * 4865289 * 2
def baseEnd_4865289 : Nat := 2498231780032720268112449

theorem tailTrace_4865289 : CollatzResearch.WordTrace tailWord_4865289 prefixEnd_4865289 2498231780032720268112449 := by
  unfold tailWord_4865289
  simp only [CollatzResearch.WordTrace]
  refine ⟨177451668070896353052974921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118301112047264235368649947 177451668070896353052974921)
  ·
    refine ⟨133088751053172264789731191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177451668070896353052974921 133088751053172264789731191)
    ·
      refine ⟨199633126579758397184596787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133088751053172264789731191 199633126579758397184596787)
      ·
        refine ⟨299449689869637595776895181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199633126579758397184596787 299449689869637595776895181)
        ·
          refine ⟨112293633701114098416335693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 299449689869637595776895181 112293633701114098416335693)
          ·
            refine ⟨42110112637917786906125885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112293633701114098416335693 42110112637917786906125885)
            ·
              refine ⟨15791292239219170089797207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42110112637917786906125885 15791292239219170089797207)
              ·
                refine ⟨23686938358828755134695811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15791292239219170089797207 23686938358828755134695811)
                ·
                  refine ⟨35530407538243132702043717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23686938358828755134695811 35530407538243132702043717)
                  ·
                    refine ⟨6661951413420587381633197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35530407538243132702043717 6661951413420587381633197)
                    ·
                      refine ⟨2498231780032720268112449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6661951413420587381633197 2498231780032720268112449)
                      ·
                        rfl

theorem cell23_4865289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 4, 3].length) (baseStart_4865289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865289 prefixEnd_4865289 := by exact prefixLift 4865289
  have htrace : WordTrace (prefixWord ++ tailWord_4865289) baseStart_4865289 baseEnd_4865289 := by
    simpa [prefixWord, tailWord_4865289, baseEnd_4865289] using wordTrace_append hprefix tailTrace_4865289
  have hstable : (prefixWord ++ tailWord_4865289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865289).length < 2 ^ (prefixWord ++ tailWord_4865289).sum := by decide
  have hdescent : baseEnd_4865289 < baseStart_4865289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865356 : List Nat := [2, 2, 1, 3, 2, 2, 2, 3, 1, 5]
def baseStart_4865356 : Nat := 118140960795 + 4865356 * 2 ^ 59
def prefixEnd_4865356 : Nat := 4983230072969 + 3 ^ 40 * 4865356 * 2
def baseEnd_4865356 : Nat := 832755394412190501991547

theorem tailTrace_4865356 : CollatzResearch.WordTrace tailWord_4865356 prefixEnd_4865356 832755394412190501991547 := by
  unfold tailWord_4865356
  simp only [CollatzResearch.WordTrace]
  refine ⟨88727055880826811747831961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118302741174435748997109281 88727055880826811747831961)
  ·
    refine ⟨66545291910620108810873971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88727055880826811747831961 66545291910620108810873971)
    ·
      refine ⟨99817937865930163216310957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66545291910620108810873971 99817937865930163216310957)
      ·
        refine ⟨37431726699723811206116609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99817937865930163216310957 37431726699723811206116609)
        ·
          refine ⟨28073795024792858404587457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37431726699723811206116609 28073795024792858404587457)
          ·
            refine ⟨21055346268594643803440593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28073795024792858404587457 21055346268594643803440593)
            ·
              refine ⟨15791509701445982852580445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21055346268594643803440593 15791509701445982852580445)
              ·
                refine ⟨5921816138042243569717667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15791509701445982852580445 5921816138042243569717667)
                ·
                  refine ⟨8882724207063365354576501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5921816138042243569717667 8882724207063365354576501)
                  ·
                    refine ⟨832755394412190501991547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8882724207063365354576501 832755394412190501991547)
                    ·
                      rfl

theorem cell23_4865356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 1, 5].length) (baseStart_4865356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865356 prefixEnd_4865356 := by exact prefixLift 4865356
  have htrace : WordTrace (prefixWord ++ tailWord_4865356) baseStart_4865356 baseEnd_4865356 := by
    simpa [prefixWord, tailWord_4865356, baseEnd_4865356] using wordTrace_append hprefix tailTrace_4865356
  have hstable : (prefixWord ++ tailWord_4865356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865356).length < 2 ^ (prefixWord ++ tailWord_4865356).sum := by decide
  have hdescent : baseEnd_4865356 < baseStart_4865356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865393 : List Nat := [1, 2, 2, 2, 1, 2, 2, 4, 3, 2, 2]
def baseStart_4865393 : Nat := 118140960795 + 4865393 * 2 ^ 59
def prefixEnd_4865393 : Nat := 4983230072969 + 3 ^ 40 * 4865393 * 2
def baseEnd_4865393 : Nat := 2498285182020787861211971

theorem tailTrace_4865393 : CollatzResearch.WordTrace tailWord_4865393 prefixEnd_4865393 2498285182020787861211971 := by
  unfold tailWord_4865393
  simp only [CollatzResearch.WordTrace]
  refine ⟨177455461262519578814760833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118303640841679719209840555 177455461262519578814760833)
  ·
    refine ⟨133091595946889684111070625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177455461262519578814760833 133091595946889684111070625)
    ·
      refine ⟨99818696960167263083302969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133091595946889684111070625 99818696960167263083302969)
      ·
        refine ⟨74864022720125447312477227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99818696960167263083302969 74864022720125447312477227)
        ·
          refine ⟨112296034080188170968715841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74864022720125447312477227 112296034080188170968715841)
          ·
            refine ⟨84222025560141128226536881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112296034080188170968715841 84222025560141128226536881)
            ·
              refine ⟨63166519170105846169902661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84222025560141128226536881 63166519170105846169902661)
              ·
                refine ⟨11843722344394846156856749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63166519170105846169902661 11843722344394846156856749)
                ·
                  refine ⟨4441395879148067308821281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11843722344394846156856749 4441395879148067308821281)
                  ·
                    refine ⟨3331046909361050481615961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4441395879148067308821281 3331046909361050481615961)
                    ·
                      refine ⟨2498285182020787861211971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3331046909361050481615961 2498285182020787861211971)
                      ·
                        rfl

theorem cell23_4865393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_4865393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865393 prefixEnd_4865393 := by exact prefixLift 4865393
  have htrace : WordTrace (prefixWord ++ tailWord_4865393) baseStart_4865393 baseEnd_4865393 := by
    simpa [prefixWord, tailWord_4865393, baseEnd_4865393] using wordTrace_append hprefix tailTrace_4865393
  have hstable : (prefixWord ++ tailWord_4865393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865393).length < 2 ^ (prefixWord ++ tailWord_4865393).sum := by decide
  have hdescent : baseEnd_4865393 < baseStart_4865393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865429 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 2, 7]
def baseStart_4865429 : Nat := 118140960795 + 4865429 * 2 ^ 59
def prefixEnd_4865429 : Nat := 4983230072969 + 3 ^ 40 * 4865429 * 2
def baseEnd_4865429 : Nat := 832767889108116573453935

theorem tailTrace_4865429 : CollatzResearch.WordTrace tailWord_4865429 prefixEnd_4865429 832767889108116573453935 := by
  unfold tailWord_4865429
  simp only [CollatzResearch.WordTrace]
  refine ⟨177456774290389156963071341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118304516193592771308714227 177456774290389156963071341)
  ·
    refine ⟨66546290358895933861151753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177456774290389156963071341 66546290358895933861151753)
    ·
      refine ⟨49909717769171950395863815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66546290358895933861151753 49909717769171950395863815)
      ·
        refine ⟨74864576653757925593795723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49909717769171950395863815 74864576653757925593795723)
        ·
          refine ⟨112296864980636888390693585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74864576653757925593795723 112296864980636888390693585)
          ·
            refine ⟨84222648735477666293020189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112296864980636888390693585 84222648735477666293020189)
            ·
              refine ⟨31583493275804124859882571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84222648735477666293020189 31583493275804124859882571)
              ·
                refine ⟨47375239913706187289823857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31583493275804124859882571 47375239913706187289823857)
                ·
                  refine ⟨35531429935279640467367893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47375239913706187289823857 35531429935279640467367893)
                  ·
                    refine ⟨832767889108116573453935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35531429935279640467367893 832767889108116573453935)
                    ·
                      rfl

theorem cell23_4865429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_4865429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865429 prefixEnd_4865429 := by exact prefixLift 4865429
  have htrace : WordTrace (prefixWord ++ tailWord_4865429) baseStart_4865429 baseEnd_4865429 := by
    simpa [prefixWord, tailWord_4865429, baseEnd_4865429] using wordTrace_append hprefix tailTrace_4865429
  have hstable : (prefixWord ++ tailWord_4865429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865429).length < 2 ^ (prefixWord ++ tailWord_4865429).sum := by decide
  have hdescent : baseEnd_4865429 < baseStart_4865429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865443 : List Nat := [1, 1, 1, 4, 1, 3, 1, 5, 2, 1, 3]
def baseStart_4865443 : Nat := 118140960795 + 4865443 * 2 ^ 59
def prefixEnd_4865443 : Nat := 4983230072969 + 3 ^ 40 * 4865443 * 2
def baseEnd_4865443 : Nat := 2498310856053512665586741

theorem tailTrace_4865443 : CollatzResearch.WordTrace tailWord_4865443 prefixEnd_4865443 2498310856053512665586741 := by
  unfold tailWord_4865443
  simp only [CollatzResearch.WordTrace]
  refine ⟨177457284912338437354080983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118304856608225624902720655 177457284912338437354080983)
  ·
    refine ⟨266185927368507656031121475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177457284912338437354080983 266185927368507656031121475)
    ·
      refine ⟨399278891052761484046682213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266185927368507656031121475 399278891052761484046682213)
      ·
        refine ⟨74864792072392778258752915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 399278891052761484046682213 74864792072392778258752915)
        ·
          refine ⟨112297188108589167388129373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74864792072392778258752915 112297188108589167388129373)
          ·
            refine ⟨42111445540720937770548515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112297188108589167388129373 42111445540720937770548515)
            ·
              refine ⟨63167168311081406655822773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42111445540720937770548515 63167168311081406655822773)
              ·
                refine ⟨5921922029163881873983385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63167168311081406655822773 5921922029163881873983385)
                ·
                  refine ⟨4441441521872911405487539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5921922029163881873983385 4441441521872911405487539)
                  ·
                    refine ⟨6662162282809367108231309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4441441521872911405487539 6662162282809367108231309)
                    ·
                      refine ⟨2498310856053512665586741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6662162282809367108231309 2498310856053512665586741)
                      ·
                        rfl

theorem cell23_4865443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_4865443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865443 prefixEnd_4865443 := by exact prefixLift 4865443
  have htrace : WordTrace (prefixWord ++ tailWord_4865443) baseStart_4865443 baseEnd_4865443 := by
    simpa [prefixWord, tailWord_4865443, baseEnd_4865443] using wordTrace_append hprefix tailTrace_4865443
  have hstable : (prefixWord ++ tailWord_4865443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865443).length < 2 ^ (prefixWord ++ tailWord_4865443).sum := by decide
  have hdescent : baseEnd_4865443 < baseStart_4865443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865486 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3]
def baseStart_4865486 : Nat := 118140960795 + 4865486 * 2 ^ 59
def prefixEnd_4865486 : Nat := 4983230072969 + 3 ^ 40 * 4865486 * 2
def baseEnd_4865486 : Nat := 2498332935721655997349043

theorem tailTrace_4865486 : CollatzResearch.WordTrace tailWord_4865486 prefixEnd_4865486 2498332935721655997349043 := by
  unfold tailWord_4865486
  simp only [CollatzResearch.WordTrace]
  refine ⟨22182356656397831962237039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118305902167455103798597541 22182356656397831962237039)
  ·
    refine ⟨33273534984596747943355559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22182356656397831962237039 33273534984596747943355559)
    ·
      refine ⟨49910302476895121915033339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33273534984596747943355559 49910302476895121915033339)
      ·
        refine ⟨74865453715342682872550009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49910302476895121915033339 74865453715342682872550009)
        ·
          refine ⟨56149090286507012154412507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74865453715342682872550009 56149090286507012154412507)
          ·
            refine ⟨84223635429760518231618761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56149090286507012154412507 84223635429760518231618761)
            ·
              refine ⟨63167726572320388673714071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84223635429760518231618761 63167726572320388673714071)
              ·
                refine ⟨94751589858480583010571107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63167726572320388673714071 94751589858480583010571107)
                ·
                  refine ⟨142127384787720874515856661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94751589858480583010571107 142127384787720874515856661)
                  ·
                    refine ⟨6662221161924415992930781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 142127384787720874515856661 6662221161924415992930781)
                    ·
                      refine ⟨2498332935721655997349043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6662221161924415992930781 2498332935721655997349043)
                      ·
                        rfl

theorem cell23_4865486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_4865486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865486 prefixEnd_4865486 := by exact prefixLift 4865486
  have htrace : WordTrace (prefixWord ++ tailWord_4865486) baseStart_4865486 baseEnd_4865486 := by
    simpa [prefixWord, tailWord_4865486, baseEnd_4865486] using wordTrace_append hprefix tailTrace_4865486
  have hstable : (prefixWord ++ tailWord_4865486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865486).length < 2 ^ (prefixWord ++ tailWord_4865486).sum := by decide
  have hdescent : baseEnd_4865486 < baseStart_4865486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865494 : List Nat := [5, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_4865494 : Nat := 118140960795 + 4865494 * 2 ^ 59
def prefixEnd_4865494 : Nat := 4983230072969 + 3 ^ 40 * 4865494 * 2
def baseEnd_4865494 : Nat := 2498337043566891966049007

theorem tailTrace_4865494 : CollatzResearch.WordTrace tailWord_4865494 prefixEnd_4865494 2498337043566891966049007 := by
  unfold tailWord_4865494
  simp only [CollatzResearch.WordTrace]
  refine ⟨11091196564697104566511721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118306096690102448709458357 11091196564697104566511721)
  ·
    refine ⟨8318397423522828424883791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11091196564697104566511721 8318397423522828424883791)
    ·
      refine ⟨12477596135284242637325687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8318397423522828424883791 12477596135284242637325687)
      ·
        refine ⟨18716394202926363955988531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12477596135284242637325687 18716394202926363955988531)
        ·
          refine ⟨28074591304389545933982797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18716394202926363955988531 28074591304389545933982797)
          ·
            refine ⟨10527971739146079725243549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28074591304389545933982797 10527971739146079725243549)
            ·
              refine ⟨3947989402179779896966331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10527971739146079725243549 3947989402179779896966331)
              ·
                refine ⟨5921984103269669845449497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3947989402179779896966331 5921984103269669845449497)
                ·
                  refine ⟨4441488077452252384087123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5921984103269669845449497 4441488077452252384087123)
                  ·
                    refine ⟨6662232116178378576130685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4441488077452252384087123 6662232116178378576130685)
                    ·
                      refine ⟨2498337043566891966049007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6662232116178378576130685 2498337043566891966049007)
                      ·
                        rfl

theorem cell23_4865494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_4865494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865494 prefixEnd_4865494 := by exact prefixLift 4865494
  have htrace : WordTrace (prefixWord ++ tailWord_4865494) baseStart_4865494 baseEnd_4865494 := by
    simpa [prefixWord, tailWord_4865494, baseEnd_4865494] using wordTrace_append hprefix tailTrace_4865494
  have hstable : (prefixWord ++ tailWord_4865494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865494).length < 2 ^ (prefixWord ++ tailWord_4865494).sum := by decide
  have hdescent : baseEnd_4865494 < baseStart_4865494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865496 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 2, 2, 4]
def baseStart_4865496 : Nat := 118140960795 + 4865496 * 2 ^ 59
def prefixEnd_4865496 : Nat := 4983230072969 + 3 ^ 40 * 4865496 * 2
def baseEnd_4865496 : Nat := 2498338070528200958223997

theorem tailTrace_4865496 : CollatzResearch.WordTrace tailWord_4865496 prefixEnd_4865496 2498338070528200958223997 := by
  unfold tailWord_4865496
  simp only [CollatzResearch.WordTrace]
  refine ⟨88729608990573213702880171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118306145320764284937173561 88729608990573213702880171)
  ·
    refine ⟨133094413485859820554320257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88729608990573213702880171 133094413485859820554320257)
    ·
      refine ⟨99820810114394865415740193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133094413485859820554320257 99820810114394865415740193)
      ·
        refine ⟨74865607585796149061805145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99820810114394865415740193 74865607585796149061805145)
        ·
          refine ⟨56149205689347111796353859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74865607585796149061805145 56149205689347111796353859)
          ·
            refine ⟨84223808534020667694530789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56149205689347111796353859 84223808534020667694530789)
            ·
              refine ⟨15791964100128875192724523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84223808534020667694530789 15791964100128875192724523)
              ·
                refine ⟨23687946150193312789086785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15791964100128875192724523 23687946150193312789086785)
                ·
                  refine ⟨17765959612644984591815089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23687946150193312789086785 17765959612644984591815089)
                  ·
                    refine ⟨13324469709483738443861317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17765959612644984591815089 13324469709483738443861317)
                    ·
                      refine ⟨2498338070528200958223997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13324469709483738443861317 2498338070528200958223997)
                      ·
                        rfl

theorem cell23_4865496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_4865496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865496 prefixEnd_4865496 := by exact prefixLift 4865496
  have htrace : WordTrace (prefixWord ++ tailWord_4865496) baseStart_4865496 baseEnd_4865496 := by
    simpa [prefixWord, tailWord_4865496, baseEnd_4865496] using wordTrace_append hprefix tailTrace_4865496
  have hstable : (prefixWord ++ tailWord_4865496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865496).length < 2 ^ (prefixWord ++ tailWord_4865496).sum := by decide
  have hdescent : baseEnd_4865496 < baseStart_4865496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865516 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 3]
def baseStart_4865516 : Nat := 118140960795 + 4865516 * 2 ^ 59
def prefixEnd_4865516 : Nat := 4983230072969 + 3 ^ 40 * 4865516 * 2
def baseEnd_4865516 : Nat := 2498348340141290879973905

theorem tailTrace_4865516 : CollatzResearch.WordTrace tailWord_4865516 prefixEnd_4865516 2498348340141290879973905 := by
  unfold tailWord_4865516
  simp only [CollatzResearch.WordTrace]
  refine ⟨88729973720536985410744201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118306631627382647214325601 88729973720536985410744201)
  ·
    refine ⟨66547480290402739058058151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88729973720536985410744201 66547480290402739058058151)
    ·
      refine ⟨99821220435604108587087227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66547480290402739058058151 99821220435604108587087227)
      ·
        refine ⟨149731830653406162880630841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99821220435604108587087227 149731830653406162880630841)
        ·
          refine ⟨112298872990054622160473131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149731830653406162880630841 112298872990054622160473131)
          ·
            refine ⟨168448309485081933240709697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112298872990054622160473131 168448309485081933240709697)
            ·
              refine ⟨126336232113811449930532273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168448309485081933240709697 126336232113811449930532273)
              ·
                refine ⟨94752174085358587447899205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126336232113811449930532273 94752174085358587447899205)
                ·
                  refine ⟨17766032641004735146481101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94752174085358587447899205 17766032641004735146481101)
                  ·
                    refine ⟨6662262240376775679930413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17766032641004735146481101 6662262240376775679930413)
                    ·
                      refine ⟨2498348340141290879973905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6662262240376775679930413 2498348340141290879973905)
                      ·
                        rfl

theorem cell23_4865516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_4865516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865516 prefixEnd_4865516 := by exact prefixLift 4865516
  have htrace : WordTrace (prefixWord ++ tailWord_4865516) baseStart_4865516 baseEnd_4865516 := by
    simpa [prefixWord, tailWord_4865516, baseEnd_4865516] using wordTrace_append hprefix tailTrace_4865516
  have hstable : (prefixWord ++ tailWord_4865516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865516).length < 2 ^ (prefixWord ++ tailWord_4865516).sum := by decide
  have hdescent : baseEnd_4865516 < baseStart_4865516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865540 : List Nat := [2, 3, 2, 3, 2, 2, 1, 1, 7]
def baseStart_4865540 : Nat := 118140960795 + 4865540 * 2 ^ 59
def prefixEnd_4865540 : Nat := 4983230072969 + 3 ^ 40 * 4865540 * 2
def baseEnd_4865540 : Nat := 277595629297444309563755

theorem tailTrace_4865540 : CollatzResearch.WordTrace tailWord_4865540 prefixEnd_4865540 277595629297444309563755 := by
  unfold tailWord_4865540
  simp only [CollatzResearch.WordTrace]
  refine ⟨88730411396493511460181037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118307215195324681946908049 88730411396493511460181037)
  ·
    refine ⟨33273904273685066797567889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88730411396493511460181037 33273904273685066797567889)
    ·
      refine ⟨24955428205263800098175917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33273904273685066797567889 24955428205263800098175917)
      ·
        refine ⟨9358285576973925036815969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24955428205263800098175917 9358285576973925036815969)
        ·
          refine ⟨7018714182730443777611977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9358285576973925036815969 7018714182730443777611977)
          ·
            refine ⟨5264035637047832833208983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7018714182730443777611977 5264035637047832833208983)
            ·
              refine ⟨7896053455571749249813475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5264035637047832833208983 7896053455571749249813475)
              ·
                refine ⟨11844080183357623874720213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7896053455571749249813475 11844080183357623874720213)
                ·
                  refine ⟨277595629297444309563755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11844080183357623874720213 277595629297444309563755)
                  ·
                    rfl

theorem cell23_4865540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 7].length) (baseStart_4865540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865540 prefixEnd_4865540 := by exact prefixLift 4865540
  have htrace : WordTrace (prefixWord ++ tailWord_4865540) baseStart_4865540 baseEnd_4865540 := by
    simpa [prefixWord, tailWord_4865540, baseEnd_4865540] using wordTrace_append hprefix tailTrace_4865540
  have hstable : (prefixWord ++ tailWord_4865540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865540).length < 2 ^ (prefixWord ++ tailWord_4865540).sum := by decide
  have hdescent : baseEnd_4865540 < baseStart_4865540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865546 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_4865546 : Nat := 118140960795 + 4865546 * 2 ^ 59
def prefixEnd_4865546 : Nat := 4983230072969 + 3 ^ 40 * 4865546 * 2
def baseEnd_4865546 : Nat := 2498363744560925762598767

theorem tailTrace_4865546 : CollatzResearch.WordTrace tailWord_4865546 prefixEnd_4865546 2498363744560925762598767 := by
  unfold tailWord_4865546
  simp only [CollatzResearch.WordTrace]
  refine ⟨44365260407741321486270123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118307361087310190630053661 44365260407741321486270123)
  ·
    refine ⟨66547890611611982229405185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44365260407741321486270123 66547890611611982229405185)
    ·
      refine ⟨49910917958708986672053889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66547890611611982229405185 49910917958708986672053889)
      ·
        refine ⟨37433188469031740004040417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49910917958708986672053889 37433188469031740004040417)
        ·
          refine ⟨28074891351773805003030313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37433188469031740004040417 28074891351773805003030313)
          ·
            refine ⟨21056168513830353752272735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28074891351773805003030313 21056168513830353752272735)
            ·
              refine ⟨31584252770745530628409103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21056168513830353752272735 31584252770745530628409103)
              ·
                refine ⟨47376379156118295942613655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31584252770745530628409103 47376379156118295942613655)
                ·
                  refine ⟨71064568734177443913920483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47376379156118295942613655 71064568734177443913920483)
                  ·
                    refine ⟨106596853101266165870880725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71064568734177443913920483 106596853101266165870880725)
                    ·
                      refine ⟨2498363744560925762598767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106596853101266165870880725 2498363744560925762598767)
                      ·
                        rfl

theorem cell23_4865546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_4865546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865546 prefixEnd_4865546 := by exact prefixLift 4865546
  have htrace : WordTrace (prefixWord ++ tailWord_4865546) baseStart_4865546 baseEnd_4865546 := by
    simpa [prefixWord, tailWord_4865546, baseEnd_4865546] using wordTrace_append hprefix tailTrace_4865546
  have hstable : (prefixWord ++ tailWord_4865546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865546).length < 2 ^ (prefixWord ++ tailWord_4865546).sum := by decide
  have hdescent : baseEnd_4865546 < baseStart_4865546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865573 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 4, 4, 2]
def baseStart_4865573 : Nat := 118140960795 + 4865573 * 2 ^ 59
def prefixEnd_4865573 : Nat := 4983230072969 + 3 ^ 40 * 4865573 * 2
def baseEnd_4865573 : Nat := 2498377608538597156961143

theorem tailTrace_4865573 : CollatzResearch.WordTrace tailWord_4865573 prefixEnd_4865573 2498377608538597156961143 := by
  unfold tailWord_4865573
  simp only [CollatzResearch.WordTrace]
  refine ⟨177462026401867469556313373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118308017601244979704208915 177462026401867469556313373)
  ·
    refine ⟨66548259900700301083617515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177462026401867469556313373 66548259900700301083617515)
    ·
      refine ⟨99822389851050451625426273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66548259900700301083617515 99822389851050451625426273)
      ·
        refine ⟨74866792388287838719069705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99822389851050451625426273 74866792388287838719069705)
        ·
          refine ⟨56150094291215879039302279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74866792388287838719069705 56150094291215879039302279)
          ·
            refine ⟨84225141436823818558953419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56150094291215879039302279 84225141436823818558953419)
            ·
              refine ⟨126337712155235727838430129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84225141436823818558953419 126337712155235727838430129)
              ·
                refine ⟨94753284116426795878822597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126337712155235727838430129 94753284116426795878822597)
                ·
                  refine ⟨17766240771830024227279237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94753284116426795878822597 17766240771830024227279237)
                  ·
                    refine ⟨3331170144718129542614857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17766240771830024227279237 3331170144718129542614857)
                    ·
                      refine ⟨2498377608538597156961143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3331170144718129542614857 2498377608538597156961143)
                      ·
                        rfl

theorem cell23_4865573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_4865573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865573 prefixEnd_4865573 := by exact prefixLift 4865573
  have htrace : WordTrace (prefixWord ++ tailWord_4865573) baseStart_4865573 baseEnd_4865573 := by
    simpa [prefixWord, tailWord_4865573, baseEnd_4865573] using wordTrace_append hprefix tailTrace_4865573
  have hstable : (prefixWord ++ tailWord_4865573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865573).length < 2 ^ (prefixWord ++ tailWord_4865573).sum := by decide
  have hdescent : baseEnd_4865573 < baseStart_4865573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865586 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_4865586 : Nat := 118140960795 + 4865586 * 2 ^ 59
def prefixEnd_4865586 : Nat := 4983230072969 + 3 ^ 40 * 4865586 * 2
def baseEnd_4865586 : Nat := 2498384283787105606098583

theorem tailTrace_4865586 : CollatzResearch.WordTrace tailWord_4865586 prefixEnd_4865586 2498384283787105606098583 := by
  unfold tailWord_4865586
  simp only [CollatzResearch.WordTrace]
  refine ⟨44365625137705093194134153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118308333700546915184357741 44365625137705093194134153)
  ·
    refine ⟨33274218853278819895600615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44365625137705093194134153 33274218853278819895600615)
    ·
      refine ⟨49911328279918229843400923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33274218853278819895600615 49911328279918229843400923)
      ·
        refine ⟨74866992419877344765101385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49911328279918229843400923 74866992419877344765101385)
        ·
          refine ⟨56150244314908008573826039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74866992419877344765101385 56150244314908008573826039)
          ·
            refine ⟨84225366472362012860739059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56150244314908008573826039 84225366472362012860739059)
            ·
              refine ⟨126338049708543019291108589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84225366472362012860739059 126338049708543019291108589)
              ·
                refine ⟨47376768640703632234165721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126338049708543019291108589 47376768640703632234165721)
                ·
                  refine ⟨35532576480527724175624291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47376768640703632234165721 35532576480527724175624291)
                  ·
                    refine ⟨53298864720791586263436437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35532576480527724175624291 53298864720791586263436437)
                    ·
                      refine ⟨2498384283787105606098583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53298864720791586263436437 2498384283787105606098583)
                      ·
                        rfl

theorem cell23_4865586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_4865586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865586 prefixEnd_4865586 := by exact prefixLift 4865586
  have htrace : WordTrace (prefixWord ++ tailWord_4865586) baseStart_4865586 baseEnd_4865586 := by
    simpa [prefixWord, tailWord_4865586, baseEnd_4865586] using wordTrace_append hprefix tailTrace_4865586
  have hstable : (prefixWord ++ tailWord_4865586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865586).length < 2 ^ (prefixWord ++ tailWord_4865586).sum := by decide
  have hdescent : baseEnd_4865586 < baseStart_4865586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865657 : List Nat := [1, 2, 1, 3, 3, 1, 1, 6, 1, 1, 3]
def baseStart_4865657 : Nat := 118140960795 + 4865657 * 2 ^ 59
def prefixEnd_4865657 : Nat := 4983230072969 + 3 ^ 40 * 4865657 * 2
def baseEnd_4865657 : Nat := 2498420740913574828310757

theorem tailTrace_4865657 : CollatzResearch.WordTrace tailWord_4865657 prefixEnd_4865657 2498420740913574828310757 := by
  unfold tailWord_4865657
  simp only [CollatzResearch.WordTrace]
  refine ⟨177465090133563151902371225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118310060089042101268247483 177465090133563151902371225)
  ·
    refine ⟨133098817600172363926778419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177465090133563151902371225 133098817600172363926778419)
    ·
      refine ⟨199648226400258545890167629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133098817600172363926778419 199648226400258545890167629)
      ·
        refine ⟨74868084900096954708812861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199648226400258545890167629 74868084900096954708812861)
        ·
          refine ⟨28075531837536358015804823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74868084900096954708812861 28075531837536358015804823)
          ·
            refine ⟨42113297756304537023707235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28075531837536358015804823 42113297756304537023707235)
            ·
              refine ⟨63169946634456805535560853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42113297756304537023707235 63169946634456805535560853)
              ·
                refine ⟨2961091248490162759479415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63169946634456805535560853 2961091248490162759479415)
                ·
                  refine ⟨4441636872735244139219123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2961091248490162759479415 4441636872735244139219123)
                  ·
                    refine ⟨6662455309102866208828685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4441636872735244139219123 6662455309102866208828685)
                    ·
                      refine ⟨2498420740913574828310757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6662455309102866208828685 2498420740913574828310757)
                      ·
                        rfl

theorem cell23_4865657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 1, 1, 3].length) (baseStart_4865657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865657 prefixEnd_4865657 := by exact prefixLift 4865657
  have htrace : WordTrace (prefixWord ++ tailWord_4865657) baseStart_4865657 baseEnd_4865657 := by
    simpa [prefixWord, tailWord_4865657, baseEnd_4865657] using wordTrace_append hprefix tailTrace_4865657
  have hstable : (prefixWord ++ tailWord_4865657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865657).length < 2 ^ (prefixWord ++ tailWord_4865657).sum := by decide
  have hdescent : baseEnd_4865657 < baseStart_4865657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865673 : List Nat := [1, 2, 1, 1, 4, 1, 5, 1, 1, 6]
def baseStart_4865673 : Nat := 118140960795 + 4865673 * 2 ^ 59
def prefixEnd_4865673 : Nat := 4983230072969 + 3 ^ 40 * 4865673 * 2
def baseEnd_4865673 : Nat := 832809652201348921903561

theorem tailTrace_4865673 : CollatzResearch.WordTrace tailWord_4865673 prefixEnd_4865673 832809652201348921903561 := by
  unfold tailWord_4865673
  simp only [CollatzResearch.WordTrace]
  refine ⟨177465673701505186634953673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118310449134336791089969115 177465673701505186634953673)
  ·
    refine ⟨133099255276128889976215255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177465673701505186634953673 133099255276128889976215255)
    ·
      refine ⟨199648882914193334964322883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133099255276128889976215255 199648882914193334964322883)
      ·
        refine ⟨299473324371290002446484325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199648882914193334964322883 299473324371290002446484325)
        ·
          refine ⟨56151248319616875458715811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 299473324371290002446484325 56151248319616875458715811)
          ·
            refine ⟨84226872479425313188073717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56151248319616875458715811 84226872479425313188073717)
            ·
              refine ⟨7896269294946123111381911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84226872479425313188073717 7896269294946123111381911)
              ·
                refine ⟨11844403942419184667072867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7896269294946123111381911 11844403942419184667072867)
                ·
                  refine ⟨17766605913628777000609301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11844403942419184667072867 17766605913628777000609301)
                  ·
                    refine ⟨832809652201348921903561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17766605913628777000609301 832809652201348921903561)
                    ·
                      rfl

theorem cell23_4865673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 1, 6].length) (baseStart_4865673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865673 prefixEnd_4865673 := by exact prefixLift 4865673
  have htrace : WordTrace (prefixWord ++ tailWord_4865673) baseStart_4865673 baseEnd_4865673 := by
    simpa [prefixWord, tailWord_4865673, baseEnd_4865673] using wordTrace_append hprefix tailTrace_4865673
  have hstable : (prefixWord ++ tailWord_4865673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865673).length < 2 ^ (prefixWord ++ tailWord_4865673).sum := by decide
  have hdescent : baseEnd_4865673 < baseStart_4865673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865693 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_4865693 : Nat := 118140960795 + 4865693 * 2 ^ 59
def prefixEnd_4865693 : Nat := 4983230072969 + 3 ^ 40 * 4865693 * 2
def baseEnd_4865693 : Nat := 2498439226217136687460591

theorem tailTrace_4865693 : CollatzResearch.WordTrace tailWord_4865693 prefixEnd_4865693 2498439226217136687460591 := by
  unfold tailWord_4865693
  simp only [CollatzResearch.WordTrace]
  refine ⟨177466403161432730050681733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118310935440955153367121155 177466403161432730050681733)
  ·
    refine ⟨33274950592768636884502825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177466403161432730050681733 33274950592768636884502825)
    ·
      refine ⟨24956212944576477663377119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33274950592768636884502825 24956212944576477663377119)
      ·
        refine ⟨37434319416864716495065679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24956212944576477663377119 37434319416864716495065679)
        ·
          refine ⟨56151479125297074742598519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37434319416864716495065679 56151479125297074742598519)
          ·
            refine ⟨84227218687945612113897779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56151479125297074742598519 84227218687945612113897779)
            ·
              refine ⟨126340828031918418170846669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84227218687945612113897779 126340828031918418170846669)
              ·
                refine ⟨47377810511969406814067501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126340828031918418170846669 47377810511969406814067501)
                ·
                  refine ⟨17766678941988527555275313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47377810511969406814067501 17766678941988527555275313)
                  ·
                    refine ⟨13325009206491395666456485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17766678941988527555275313 13325009206491395666456485)
                    ·
                      refine ⟨2498439226217136687460591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13325009206491395666456485 2498439226217136687460591)
                      ·
                        rfl

theorem cell23_4865693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_4865693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865693 prefixEnd_4865693 := by exact prefixLift 4865693
  have htrace : WordTrace (prefixWord ++ tailWord_4865693) baseStart_4865693 baseEnd_4865693 := by
    simpa [prefixWord, tailWord_4865693, baseEnd_4865693] using wordTrace_append hprefix tailTrace_4865693
  have hstable : (prefixWord ++ tailWord_4865693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865693).length < 2 ^ (prefixWord ++ tailWord_4865693).sum := by decide
  have hdescent : baseEnd_4865693 < baseStart_4865693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865700 : List Nat := [2, 3, 1, 2, 2, 3, 2, 1, 1, 1, 5]
def baseStart_4865700 : Nat := 118140960795 + 4865700 * 2 ^ 59
def prefixEnd_4865700 : Nat := 4983230072969 + 3 ^ 40 * 4865700 * 2
def baseEnd_4865700 : Nat := 2498442820581718160073059

theorem tailTrace_4865700 : CollatzResearch.WordTrace tailWord_4865700 prefixEnd_4865700 2498442820581718160073059 := by
  unfold tailWord_4865700
  simp only [CollatzResearch.WordTrace]
  refine ⟨88733329236203685123093277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118311105648271580164124369 88733329236203685123093277)
  ·
    refine ⟨33274998463576381921159979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88733329236203685123093277 33274998463576381921159979)
    ·
      refine ⟨49912497695364572881739969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33274998463576381921159979 49912497695364572881739969)
      ·
        refine ⟨37434373271523429661304977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49912497695364572881739969 37434373271523429661304977)
        ·
          refine ⟨28075779953642572245978733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37434373271523429661304977 28075779953642572245978733)
          ·
            refine ⟨10528417482615964592242025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28075779953642572245978733 10528417482615964592242025)
            ·
              refine ⟨7896313111961973444181519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10528417482615964592242025 7896313111961973444181519)
              ·
                refine ⟨11844469667942960166272279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7896313111961973444181519 11844469667942960166272279)
                ·
                  refine ⟨17766704501914440249408419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11844469667942960166272279 17766704501914440249408419)
                  ·
                    refine ⟨26650056752871660374112629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17766704501914440249408419 26650056752871660374112629)
                    ·
                      refine ⟨2498442820581718160073059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26650056752871660374112629 2498442820581718160073059)
                      ·
                        rfl

theorem cell23_4865700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_4865700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865700 prefixEnd_4865700 := by exact prefixLift 4865700
  have htrace : WordTrace (prefixWord ++ tailWord_4865700) baseStart_4865700 baseEnd_4865700 := by
    simpa [prefixWord, tailWord_4865700, baseEnd_4865700] using wordTrace_append hprefix tailTrace_4865700
  have hstable : (prefixWord ++ tailWord_4865700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865700).length < 2 ^ (prefixWord ++ tailWord_4865700).sum := by decide
  have hdescent : baseEnd_4865700 < baseStart_4865700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865714 : List Nat := [3, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2]
def baseStart_4865714 : Nat := 118140960795 + 4865714 * 2 ^ 59
def prefixEnd_4865714 : Nat := 4983230072969 + 3 ^ 40 * 4865714 * 2
def baseEnd_4865714 : Nat := 2498450009310881105297995

theorem tailTrace_4865714 : CollatzResearch.WordTrace tailWord_4865714 prefixEnd_4865714 2498450009310881105297995 := by
  unfold tailWord_4865714
  simp only [CollatzResearch.WordTrace]
  refine ⟨44366792273589162659299049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118311446062904433758130797 44366792273589162659299049)
  ·
    refine ⟨33275094205191871994474287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44366792273589162659299049 33275094205191871994474287)
    ·
      refine ⟨49912641307787807991711431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33275094205191871994474287 49912641307787807991711431)
      ·
        refine ⟨74868961961681711987567147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49912641307787807991711431 74868961961681711987567147)
        ·
          refine ⟨112303442942522567981350721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74868961961681711987567147 112303442942522567981350721)
          ·
            refine ⟨84227582206891925986013041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112303442942522567981350721 84227582206891925986013041)
            ·
              refine ⟨63170686655168944489509781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84227582206891925986013041 63170686655168944489509781)
              ·
                refine ⟨2961125936961044272945771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63170686655168944489509781 2961125936961044272945771)
                ·
                  refine ⟨4441688905441566409418657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2961125936961044272945771 4441688905441566409418657)
                  ·
                    refine ⟨3331266679081174807063993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4441688905441566409418657 3331266679081174807063993)
                    ·
                      refine ⟨2498450009310881105297995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3331266679081174807063993 2498450009310881105297995)
                      ·
                        rfl

theorem cell23_4865714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2].length) (baseStart_4865714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865714 prefixEnd_4865714 := by exact prefixLift 4865714
  have htrace : WordTrace (prefixWord ++ tailWord_4865714) baseStart_4865714 baseEnd_4865714 := by
    simpa [prefixWord, tailWord_4865714, baseEnd_4865714] using wordTrace_append hprefix tailTrace_4865714
  have hstable : (prefixWord ++ tailWord_4865714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865714).length < 2 ^ (prefixWord ++ tailWord_4865714).sum := by decide
  have hdescent : baseEnd_4865714 < baseStart_4865714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865724 : List Nat := [2, 2, 2, 3, 1, 4, 2, 1, 2, 4]
def baseStart_4865724 : Nat := 118140960795 + 4865724 * 2 ^ 59
def prefixEnd_4865724 : Nat := 4983230072969 + 3 ^ 40 * 4865724 * 2
def baseEnd_4865724 : Nat := 832818381372475355390983

theorem tailTrace_4865724 : CollatzResearch.WordTrace tailWord_4865724 prefixEnd_4865724 832818381372475355390983 := by
  unfold tailWord_4865724
  simp only [CollatzResearch.WordTrace]
  refine ⟨88733766912160211172530113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118311689216213614896706817 88733766912160211172530113)
  ·
    refine ⟨66550325184120158379397585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88733766912160211172530113 66550325184120158379397585)
    ·
      refine ⟨49912743888090118784548189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66550325184120158379397585 49912743888090118784548189)
      ·
        refine ⟨18717278958033794544205571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49912743888090118784548189 18717278958033794544205571)
        ·
          refine ⟨28075918437050691816308357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18717278958033794544205571 28075918437050691816308357)
          ·
            refine ⟨5264234706947004715557817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28075918437050691816308357 5264234706947004715557817)
            ·
              refine ⟨3948176030210253536668363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5264234706947004715557817 3948176030210253536668363)
              ·
                refine ⟨5922264045315380305002545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3948176030210253536668363 5922264045315380305002545)
                ·
                  refine ⟨4441698033986535228751909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5922264045315380305002545 4441698033986535228751909)
                  ·
                    refine ⟨832818381372475355390983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4441698033986535228751909 832818381372475355390983)
                    ·
                      rfl

theorem cell23_4865724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_4865724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865724 prefixEnd_4865724 := by exact prefixLift 4865724
  have htrace : WordTrace (prefixWord ++ tailWord_4865724) baseStart_4865724 baseEnd_4865724 := by
    simpa [prefixWord, tailWord_4865724, baseEnd_4865724] using wordTrace_append hprefix tailTrace_4865724
  have hstable : (prefixWord ++ tailWord_4865724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865724).length < 2 ^ (prefixWord ++ tailWord_4865724).sum := by decide
  have hdescent : baseEnd_4865724 < baseStart_4865724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865783 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 4]
def baseStart_4865783 : Nat := 118140960795 + 4865783 * 2 ^ 59
def prefixEnd_4865783 : Nat := 4983230072969 + 3 ^ 40 * 4865783 * 2
def baseEnd_4865783 : Nat := 2498485439476041335335177

theorem tailTrace_4865783 : CollatzResearch.WordTrace tailWord_4865783 prefixEnd_4865783 2498485439476041335335177 := by
  unfold tailWord_4865783
  simp only [CollatzResearch.WordTrace]
  refine ⟨177469685731106675421458003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118313123820737783614305335 177469685731106675421458003)
  ·
    refine ⟨266204528596660013132187005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177469685731106675421458003 266204528596660013132187005)
    ·
      refine ⟨99826698223747504924570127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266204528596660013132187005 99826698223747504924570127)
      ·
        refine ⟨149740047335621257386855191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99826698223747504924570127 149740047335621257386855191)
        ·
          refine ⟨224610071003431886080282787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149740047335621257386855191 224610071003431886080282787)
          ·
            refine ⟨336915106505147829120424181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224610071003431886080282787 336915106505147829120424181)
            ·
              refine ⟨31585791234857608980039767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 336915106505147829120424181 31585791234857608980039767)
              ·
                refine ⟨47378686852286413470059651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31585791234857608980039767 47378686852286413470059651)
                ·
                  refine ⟨71068030278429620205089477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47378686852286413470059651 71068030278429620205089477)
                  ·
                    refine ⟨13325255677205553788454277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71068030278429620205089477 13325255677205553788454277)
                    ·
                      refine ⟨2498485439476041335335177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13325255677205553788454277 2498485439476041335335177)
                      ·
                        rfl

theorem cell23_4865783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_4865783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865783 prefixEnd_4865783 := by exact prefixLift 4865783
  have htrace : WordTrace (prefixWord ++ tailWord_4865783) baseStart_4865783 baseEnd_4865783 := by
    simpa [prefixWord, tailWord_4865783, baseEnd_4865783] using wordTrace_append hprefix tailTrace_4865783
  have hstable : (prefixWord ++ tailWord_4865783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865783).length < 2 ^ (prefixWord ++ tailWord_4865783).sum := by decide
  have hdescent : baseEnd_4865783 < baseStart_4865783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865793 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 9]
def baseStart_4865793 : Nat := 118140960795 + 4865793 * 2 ^ 59
def prefixEnd_4865793 : Nat := 4983230072969 + 3 ^ 40 * 4865793 * 2
def baseEnd_4865793 : Nat := 277610063809176255134459

theorem tailTrace_4865793 : CollatzResearch.WordTrace tailWord_4865793 prefixEnd_4865793 277610063809176255134459 := by
  unfold tailWord_4865793
  simp only [CollatzResearch.WordTrace]
  refine ⟨177470050461070447129322033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118313366974046964752881355 177470050461070447129322033)
  ·
    refine ⟨133102537845802835346991525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177470050461070447129322033 133102537845802835346991525)
    ·
      refine ⟨24956725846088031627560911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133102537845802835346991525 24956725846088031627560911)
      ·
        refine ⟨37435088769132047441341367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24956725846088031627560911 37435088769132047441341367)
        ·
          refine ⟨56152633153698071162012051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37435088769132047441341367 56152633153698071162012051)
          ·
            refine ⟨84228949730547106743018077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56152633153698071162012051 84228949730547106743018077)
            ·
              refine ⟨31585856148955165028631779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84228949730547106743018077 31585856148955165028631779)
              ·
                refine ⟨47378784223432747542947669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31585856148955165028631779 47378784223432747542947669)
                ·
                  refine ⟨277610063809176255134459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47378784223432747542947669 277610063809176255134459)
                  ·
                    rfl

theorem cell23_4865793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 9].length) (baseStart_4865793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865793 prefixEnd_4865793 := by exact prefixLift 4865793
  have htrace : WordTrace (prefixWord ++ tailWord_4865793) baseStart_4865793 baseEnd_4865793 := by
    simpa [prefixWord, tailWord_4865793, baseEnd_4865793] using wordTrace_append hprefix tailTrace_4865793
  have hstable : (prefixWord ++ tailWord_4865793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865793).length < 2 ^ (prefixWord ++ tailWord_4865793).sum := by decide
  have hdescent : baseEnd_4865793 < baseStart_4865793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865820 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_4865820 : Nat := 118140960795 + 4865820 * 2 ^ 59
def prefixEnd_4865820 : Nat := 4983230072969 + 3 ^ 40 * 4865820 * 2
def baseEnd_4865820 : Nat := 2498504438260257690572507

theorem tailTrace_4865820 : CollatzResearch.WordTrace tailWord_4865820 prefixEnd_4865820 2498504438260257690572507 := by
  unfold tailWord_4865820
  simp only [CollatzResearch.WordTrace]
  refine ⟨88735517615986315370277457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118314023487981753827036609 88735517615986315370277457)
  ·
    refine ⟨66551638211989736527708093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88735517615986315370277457 66551638211989736527708093)
    ·
      refine ⟨24956864329496151197890535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66551638211989736527708093 24956864329496151197890535)
      ·
        refine ⟨37435296494244226796835803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24956864329496151197890535 37435296494244226796835803)
        ·
          refine ⟨56152944741366340195253705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37435296494244226796835803 56152944741366340195253705)
          ·
            refine ⟨42114708556024755146440279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56152944741366340195253705 42114708556024755146440279)
            ·
              refine ⟨63172062834037132719660419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42114708556024755146440279 63172062834037132719660419)
              ·
                refine ⟨94758094251055699079490629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63172062834037132719660419 94758094251055699079490629)
                ·
                  refine ⟨17767142672072943577404493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94758094251055699079490629 17767142672072943577404493)
                  ·
                    refine ⟨6662678502027353841526685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17767142672072943577404493 6662678502027353841526685)
                    ·
                      refine ⟨2498504438260257690572507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6662678502027353841526685 2498504438260257690572507)
                      ·
                        rfl

theorem cell23_4865820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_4865820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865820 prefixEnd_4865820 := by exact prefixLift 4865820
  have htrace : WordTrace (prefixWord ++ tailWord_4865820) baseStart_4865820 baseEnd_4865820 := by
    simpa [prefixWord, tailWord_4865820, baseEnd_4865820] using wordTrace_append hprefix tailTrace_4865820
  have hstable : (prefixWord ++ tailWord_4865820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865820).length < 2 ^ (prefixWord ++ tailWord_4865820).sum := by decide
  have hdescent : baseEnd_4865820 < baseStart_4865820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865838 : List Nat := [4, 1, 3, 2, 3, 1, 1, 1, 1, 4, 2]
def baseStart_4865838 : Nat := 118140960795 + 4865838 * 2 ^ 59
def prefixEnd_4865838 : Nat := 4983230072969 + 3 ^ 40 * 4865838 * 2
def baseEnd_4865838 : Nat := 2498513680912038620147425

theorem tailTrace_4865838 : CollatzResearch.WordTrace tailWord_4865838 prefixEnd_4865838 2498513680912038620147425 := by
  unfold tailWord_4865838
  simp only [CollatzResearch.WordTrace]
  refine ⟨22183961468238427476838771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118314461163938279876473445 22183961468238427476838771)
  ·
    refine ⟨33275942202357641215258157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22183961468238427476838771 33275942202357641215258157)
    ·
      refine ⟨12478478325884115455721809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33275942202357641215258157 12478478325884115455721809)
      ·
        refine ⟨9358858744413086591791357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12478478325884115455721809 9358858744413086591791357)
        ·
          refine ⟨3509572029154907471921759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9358858744413086591791357 3509572029154907471921759)
          ·
            refine ⟨5264358043732361207882639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3509572029154907471921759 5264358043732361207882639)
            ·
              refine ⟨7896537065598541811823959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5264358043732361207882639 7896537065598541811823959)
              ·
                refine ⟨11844805598397812717735939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7896537065598541811823959 11844805598397812717735939)
                ·
                  refine ⟨17767208397596719076603909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11844805598397812717735939 17767208397596719076603909)
                  ·
                    refine ⟨3331351574549384826863233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17767208397596719076603909 3331351574549384826863233)
                    ·
                      refine ⟨2498513680912038620147425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3331351574549384826863233 2498513680912038620147425)
                      ·
                        rfl

theorem cell23_4865838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_4865838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865838 prefixEnd_4865838 := by exact prefixLift 4865838
  have htrace : WordTrace (prefixWord ++ tailWord_4865838) baseStart_4865838 baseEnd_4865838 := by
    simpa [prefixWord, tailWord_4865838, baseEnd_4865838] using wordTrace_append hprefix tailTrace_4865838
  have hstable : (prefixWord ++ tailWord_4865838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865838).length < 2 ^ (prefixWord ++ tailWord_4865838).sum := by decide
  have hdescent : baseEnd_4865838 < baseStart_4865838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865877 : List Nat := [1, 3, 2, 2, 2, 3, 1, 2, 2, 1, 4]
def baseStart_4865877 : Nat := 118140960795 + 4865877 * 2 ^ 59
def prefixEnd_4865877 : Nat := 4983230072969 + 3 ^ 40 * 4865877 * 2
def baseEnd_4865877 : Nat := 2498533706657563967559745

theorem tailTrace_4865877 : CollatzResearch.WordTrace tailWord_4865877 prefixEnd_4865877 2498533706657563967559745 := by
  unfold tailWord_4865877
  simp only [CollatzResearch.WordTrace]
  refine ⟨177473114192766129475379885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118315409461844086316919923 177473114192766129475379885)
  ·
    refine ⟨66552417822287298553267457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177473114192766129475379885 66552417822287298553267457)
    ·
      refine ⟨49914313366715473914950593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66552417822287298553267457 49914313366715473914950593)
      ·
        refine ⟨37435735025036605436212945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49914313366715473914950593 37435735025036605436212945)
        ·
          refine ⟨28076801268777454077159709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37435735025036605436212945 28076801268777454077159709)
          ·
            refine ⟨10528800475791545278934891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28076801268777454077159709 10528800475791545278934891)
            ·
              refine ⟨15793200713687317918402337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10528800475791545278934891 15793200713687317918402337)
              ·
                refine ⟨11844900535265488438801753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15793200713687317918402337 11844900535265488438801753)
                ·
                  refine ⟨8883675401449116329101315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11844900535265488438801753 8883675401449116329101315)
                  ·
                    refine ⟨13325513102173674493651973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8883675401449116329101315 13325513102173674493651973)
                    ·
                      refine ⟨2498533706657563967559745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13325513102173674493651973 2498533706657563967559745)
                      ·
                        rfl

theorem cell23_4865877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_4865877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865877 prefixEnd_4865877 := by exact prefixLift 4865877
  have htrace : WordTrace (prefixWord ++ tailWord_4865877) baseStart_4865877 baseEnd_4865877 := by
    simpa [prefixWord, tailWord_4865877, baseEnd_4865877] using wordTrace_append hprefix tailTrace_4865877
  have hstable : (prefixWord ++ tailWord_4865877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865877).length < 2 ^ (prefixWord ++ tailWord_4865877).sum := by decide
  have hdescent : baseEnd_4865877 < baseStart_4865877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865887 : List Nat := [1, 1, 2, 3, 1, 4, 3, 1, 3, 4]
def baseStart_4865887 : Nat := 118140960795 + 4865887 * 2 ^ 59
def prefixEnd_4865887 : Nat := 4983230072969 + 3 ^ 40 * 4865887 * 2
def baseEnd_4865887 : Nat := 832846280488036309478233

theorem tailTrace_4865887 : CollatzResearch.WordTrace tailWord_4865887 prefixEnd_4865887 832846280488036309478233 := by
  unfold tailWord_4865887
  simp only [CollatzResearch.WordTrace]
  refine ⟨177473478922729901183243915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118315652615153267455495943 177473478922729901183243915)
  ·
    refine ⟨266210218384094851774865873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177473478922729901183243915 266210218384094851774865873)
    ·
      refine ⟨199657663788071138831149405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266210218384094851774865873 199657663788071138831149405)
      ·
        refine ⟨74871623920526677061681027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199657663788071138831149405 74871623920526677061681027)
        ·
          refine ⟨112307435880790015592521541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74871623920526677061681027 112307435880790015592521541)
          ·
            refine ⟨21057644227648127923597789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112307435880790015592521541 21057644227648127923597789)
            ·
              refine ⟨7896616585368047971349171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21057644227648127923597789 7896616585368047971349171)
              ·
                refine ⟨11844924878052071957023757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7896616585368047971349171 11844924878052071957023757)
                ·
                  refine ⟨4441846829269526983883909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11844924878052071957023757 4441846829269526983883909)
                  ·
                    refine ⟨832846280488036309478233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4441846829269526983883909 832846280488036309478233)
                    ·
                      rfl

theorem cell23_4865887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 3, 4].length) (baseStart_4865887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865887 prefixEnd_4865887 := by exact prefixLift 4865887
  have htrace : WordTrace (prefixWord ++ tailWord_4865887) baseStart_4865887 baseEnd_4865887 := by
    simpa [prefixWord, tailWord_4865887, baseEnd_4865887] using wordTrace_append hprefix tailTrace_4865887
  have hstable : (prefixWord ++ tailWord_4865887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865887).length < 2 ^ (prefixWord ++ tailWord_4865887).sum := by decide
  have hdescent : baseEnd_4865887 < baseStart_4865887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865938 : List Nat := [3, 2, 3, 2, 1, 1, 4, 2, 1, 4]
def baseStart_4865938 : Nat := 118140960795 + 4865938 * 2 ^ 59
def prefixEnd_4865938 : Nat := 4983230072969 + 3 ^ 40 * 4865938 * 2
def baseEnd_4865938 : Nat := 832855009659162742965655

theorem tailTrace_4865938 : CollatzResearch.WordTrace tailWord_4865938 prefixEnd_4865938 832855009659162742965655 := by
  unfold tailWord_4865938
  simp only [CollatzResearch.WordTrace]
  refine ⟨44368834761386284223337617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118316892697030091262233645 44368834761386284223337617)
  ·
    refine ⟨33276626071039713167503213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44368834761386284223337617 33276626071039713167503213)
    ·
      refine ⟨12478734776639892437813705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33276626071039713167503213 12478734776639892437813705)
      ·
        refine ⟨9359051082479919328360279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12478734776639892437813705 9359051082479919328360279)
        ·
          refine ⟨14038576623719878992540419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9359051082479919328360279 14038576623719878992540419)
          ·
            refine ⟨21057864935579818488810629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14038576623719878992540419 21057864935579818488810629)
            ·
              refine ⟨3948349675421215966651993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21057864935579818488810629 3948349675421215966651993)
              ·
                refine ⟨2961262256565911974988995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3948349675421215966651993 2961262256565911974988995)
                ·
                  refine ⟨4441893384848867962483493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2961262256565911974988995 4441893384848867962483493)
                  ·
                    refine ⟨832855009659162742965655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4441893384848867962483493 832855009659162742965655)
                    ·
                      rfl

theorem cell23_4865938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_4865938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865938 prefixEnd_4865938 := by exact prefixLift 4865938
  have htrace : WordTrace (prefixWord ++ tailWord_4865938) baseStart_4865938 baseEnd_4865938 := by
    simpa [prefixWord, tailWord_4865938, baseEnd_4865938] using wordTrace_append hprefix tailTrace_4865938
  have hstable : (prefixWord ++ tailWord_4865938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865938).length < 2 ^ (prefixWord ++ tailWord_4865938).sum := by decide
  have hdescent : baseEnd_4865938 < baseStart_4865938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865967 : List Nat := [1, 1, 2, 1, 2, 2, 4, 4, 1, 1, 4]
def baseStart_4865967 : Nat := 118140960795 + 4865967 * 2 ^ 59
def prefixEnd_4865967 : Nat := 4983230072969 + 3 ^ 40 * 4865967 * 2
def baseEnd_4865967 : Nat := 2498579919916468615434331

theorem tailTrace_4865967 : CollatzResearch.WordTrace tailWord_4865967 prefixEnd_4865967 2498579919916468615434331 := by
  unfold tailWord_4865967
  simp only [CollatzResearch.WordTrace]
  refine ⟨177476396762440074846156155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118317597841626716564104103 177476396762440074846156155)
  ·
    refine ⟨266214595143660112269234233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177476396762440074846156155 266214595143660112269234233)
    ·
      refine ⟨199660946357745084201925675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266214595143660112269234233 199660946357745084201925675)
      ·
        refine ⟨299491419536617626302888513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199660946357745084201925675 299491419536617626302888513)
        ·
          refine ⟨224618564652463219727166385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299491419536617626302888513 224618564652463219727166385)
          ·
            refine ⟨168463923489347414795374789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224618564652463219727166385 168463923489347414795374789)
            ·
              refine ⟨31586985654252640274132773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168463923489347414795374789 31586985654252640274132773)
              ·
                refine ⟨5922559810172370051399895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31586985654252640274132773 5922559810172370051399895)
                ·
                  refine ⟨8883839715258555077099843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5922559810172370051399895 8883839715258555077099843)
                  ·
                    refine ⟨13325759572887832615649765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8883839715258555077099843 13325759572887832615649765)
                    ·
                      refine ⟨2498579919916468615434331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13325759572887832615649765 2498579919916468615434331)
                      ·
                        rfl

theorem cell23_4865967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 1, 4].length) (baseStart_4865967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865967 prefixEnd_4865967 := by exact prefixLift 4865967
  have htrace : WordTrace (prefixWord ++ tailWord_4865967) baseStart_4865967 baseEnd_4865967 := by
    simpa [prefixWord, tailWord_4865967, baseEnd_4865967] using wordTrace_append hprefix tailTrace_4865967
  have hstable : (prefixWord ++ tailWord_4865967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865967).length < 2 ^ (prefixWord ++ tailWord_4865967).sum := by decide
  have hdescent : baseEnd_4865967 < baseStart_4865967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865977 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 4, 4]
def baseStart_4865977 : Nat := 118140960795 + 4865977 * 2 ^ 59
def prefixEnd_4865977 : Nat := 4983230072969 + 3 ^ 40 * 4865977 * 2
def baseEnd_4865977 : Nat := 832861684907671192103095

theorem tailTrace_4865977 : CollatzResearch.WordTrace tailWord_4865977 prefixEnd_4865977 832861684907671192103095 := by
  unfold tailWord_4865977
  simp only [CollatzResearch.WordTrace]
  refine ⟨177476761492403846554020185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118317840994935897702680123 177476761492403846554020185)
  ·
    refine ⟨133107571119302884915515139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177476761492403846554020185 133107571119302884915515139)
    ·
      refine ⟨199661356678954327373272709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133107571119302884915515139 199661356678954327373272709)
      ·
        refine ⟨37436504377303936382488633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199661356678954327373272709 37436504377303936382488633)
        ·
          refine ⟨28077378282977952286866475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37436504377303936382488633 28077378282977952286866475)
          ·
            refine ⟨42116067424466928430299713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28077378282977952286866475 42116067424466928430299713)
            ·
              refine ⟨31587050568350196322724785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42116067424466928430299713 31587050568350196322724785)
              ·
                refine ⟨23690287926262647242043589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31587050568350196322724785 23690287926262647242043589)
                ·
                  refine ⟨4441928986174246357883173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23690287926262647242043589 4441928986174246357883173)
                  ·
                    refine ⟨832861684907671192103095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4441928986174246357883173 832861684907671192103095)
                    ·
                      rfl

theorem cell23_4865977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 4, 4].length) (baseStart_4865977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865977 prefixEnd_4865977 := by exact prefixLift 4865977
  have htrace : WordTrace (prefixWord ++ tailWord_4865977) baseStart_4865977 baseEnd_4865977 := by
    simpa [prefixWord, tailWord_4865977, baseEnd_4865977] using wordTrace_append hprefix tailTrace_4865977
  have hstable : (prefixWord ++ tailWord_4865977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865977).length < 2 ^ (prefixWord ++ tailWord_4865977).sum := by decide
  have hdescent : baseEnd_4865977 < baseStart_4865977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865981 : List Nat := [1, 4, 1, 2, 3, 3, 2, 1, 1, 5]
def baseStart_4865981 : Nat := 118140960795 + 4865981 * 2 ^ 59
def prefixEnd_4865981 : Nat := 4983230072969 + 3 ^ 40 * 4865981 * 2
def baseEnd_4865981 : Nat := 832862369548543853553089

theorem tailTrace_4865981 : CollatzResearch.WordTrace tailWord_4865981 prefixEnd_4865981 832862369548543853553089 := by
  unfold tailWord_4865981
  simp only [CollatzResearch.WordTrace]
  refine ⟨177476907384389355237165797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118317938256259570158110531 177476907384389355237165797)
  ·
    refine ⟨33276920134573004106968587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177476907384389355237165797 33276920134573004106968587)
    ·
      refine ⟨49915380201859506160452881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33276920134573004106968587 49915380201859506160452881)
      ·
        refine ⟨37436535151394629620339661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49915380201859506160452881 37436535151394629620339661)
        ·
          refine ⟨14038700681772986107627373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37436535151394629620339661 14038700681772986107627373)
          ·
            refine ⟨5264512755664869790360265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14038700681772986107627373 5264512755664869790360265)
            ·
              refine ⟨3948384566748652342770199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5264512755664869790360265 3948384566748652342770199)
              ·
                refine ⟨5922576850122978514155299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3948384566748652342770199 5922576850122978514155299)
                ·
                  refine ⟨8883865275184467771232949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5922576850122978514155299 8883865275184467771232949)
                  ·
                    refine ⟨832862369548543853553089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8883865275184467771232949 832862369548543853553089)
                    ·
                      rfl

theorem cell23_4865981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_4865981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865981 prefixEnd_4865981 := by exact prefixLift 4865981
  have htrace : WordTrace (prefixWord ++ tailWord_4865981) baseStart_4865981 baseEnd_4865981 := by
    simpa [prefixWord, tailWord_4865981, baseEnd_4865981] using wordTrace_append hprefix tailTrace_4865981
  have hstable : (prefixWord ++ tailWord_4865981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865981).length < 2 ^ (prefixWord ++ tailWord_4865981).sum := by decide
  have hdescent : baseEnd_4865981 < baseStart_4865981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865984 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 5, 2, 2]
def baseStart_4865984 : Nat := 118140960795 + 4865984 * 2 ^ 59
def prefixEnd_4865984 : Nat := 4983230072969 + 3 ^ 40 * 4865984 * 2
def baseEnd_4865984 : Nat := 2498588649087595048921753

theorem tailTrace_4865984 : CollatzResearch.WordTrace tailWord_4865984 prefixEnd_4865984 2498588649087595048921753 := by
  unfold tailWord_4865984
  simp only [CollatzResearch.WordTrace]
  refine ⟨88738508401689243374762503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118318011202252324499683337 88738508401689243374762503)
  ·
    refine ⟨133107762602533865062143755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88738508401689243374762503 133107762602533865062143755)
    ·
      refine ⟨199661643903800797593215633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133107762602533865062143755 199661643903800797593215633)
      ·
        refine ⟨149746232927850598194911725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199661643903800797593215633 149746232927850598194911725)
        ·
          refine ⟨56154837347943974323091897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149746232927850598194911725 56154837347943974323091897)
          ·
            refine ⟨42116128010957980742318923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56154837347943974323091897 42116128010957980742318923)
            ·
              refine ⟨63174192016436971113478385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42116128010957980742318923 63174192016436971113478385)
              ·
                refine ⟨47380644012327728335108789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63174192016436971113478385 47380644012327728335108789)
                ·
                  refine ⟨4441935376155724531416449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47380644012327728335108789 4441935376155724531416449)
                  ·
                    refine ⟨3331451532116793398562337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4441935376155724531416449 3331451532116793398562337)
                    ·
                      refine ⟨2498588649087595048921753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3331451532116793398562337 2498588649087595048921753)
                      ·
                        rfl

theorem cell23_4865984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 5, 2, 2].length) (baseStart_4865984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865984 prefixEnd_4865984 := by exact prefixLift 4865984
  have htrace : WordTrace (prefixWord ++ tailWord_4865984) baseStart_4865984 baseEnd_4865984 := by
    simpa [prefixWord, tailWord_4865984, baseEnd_4865984] using wordTrace_append hprefix tailTrace_4865984
  have hstable : (prefixWord ++ tailWord_4865984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865984).length < 2 ^ (prefixWord ++ tailWord_4865984).sum := by decide
  have hdescent : baseEnd_4865984 < baseStart_4865984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4865994 : List Nat := [3, 1, 2, 1, 2, 1, 5, 2, 2, 4]
def baseStart_4865994 : Nat := 118140960795 + 4865994 * 2 ^ 59
def prefixEnd_4865994 : Nat := 4983230072969 + 3 ^ 40 * 4865994 * 2
def baseEnd_4865994 : Nat := 832864594631380003265569

theorem tailTrace_4865994 : CollatzResearch.WordTrace tailWord_4865994 prefixEnd_4865994 832864594631380003265569 := by
  unfold tailWord_4865994
  simp only [CollatzResearch.WordTrace]
  refine ⟨44369345383335564614347259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118318254355561505638259357 44369345383335564614347259)
  ·
    refine ⟨66554018075003346921520889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44369345383335564614347259 66554018075003346921520889)
    ·
      refine ⟨49915513556252510191140667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66554018075003346921520889 49915513556252510191140667)
      ·
        refine ⟨74873270334378765286711001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49915513556252510191140667 74873270334378765286711001)
        ·
          refine ⟨56154952750784073965033251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74873270334378765286711001 56154952750784073965033251)
          ·
            refine ⟨84232429126176110947549877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56154952750784073965033251 84232429126176110947549877)
            ·
              refine ⟨7896790230579010401332801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84232429126176110947549877 7896790230579010401332801)
              ·
                refine ⟨5922592672934257800999601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7896790230579010401332801 5922592672934257800999601)
                ·
                  refine ⟨4441944504700693350749701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5922592672934257800999601 4441944504700693350749701)
                  ·
                    refine ⟨832864594631380003265569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4441944504700693350749701 832864594631380003265569)
                    ·
                      rfl

theorem cell23_4865994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_4865994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4865994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4865994 prefixEnd_4865994 := by exact prefixLift 4865994
  have htrace : WordTrace (prefixWord ++ tailWord_4865994) baseStart_4865994 baseEnd_4865994 := by
    simpa [prefixWord, tailWord_4865994, baseEnd_4865994] using wordTrace_append hprefix tailTrace_4865994
  have hstable : (prefixWord ++ tailWord_4865994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4865994).length < 2 ^ (prefixWord ++ tailWord_4865994).sum := by decide
  have hdescent : baseEnd_4865994 < baseStart_4865994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4865994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866018 : List Nat := [3, 3, 3, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_4866018 : Nat := 118140960795 + 4866018 * 2 ^ 59
def prefixEnd_4866018 : Nat := 4983230072969 + 3 ^ 40 * 4866018 * 2
def baseEnd_4866018 : Nat := 2498606107429847915896597

theorem tailTrace_4866018 : CollatzResearch.WordTrace tailWord_4866018 prefixEnd_4866018 2498606107429847915896597 := by
  unfold tailWord_4866018
  simp only [CollatzResearch.WordTrace]
  refine ⟨44369564221313827639065677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118318837923503540370841805 44369564221313827639065677)
  ·
    refine ⟨16638586582992685364649629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44369564221313827639065677 16638586582992685364649629)
    ·
      refine ⟨6239469968622257011743611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16638586582992685364649629 6239469968622257011743611)
      ·
        refine ⟨9359204952933385517615417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6239469968622257011743611 9359204952933385517615417)
        ·
          refine ⟨7019403714700039138211563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9359204952933385517615417 7019403714700039138211563)
          ·
            refine ⟨10529105572050058707317345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7019403714700039138211563 10529105572050058707317345)
            ·
              refine ⟨7896829179037544030488009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10529105572050058707317345 7896829179037544030488009)
              ·
                refine ⟨5922621884278158022866007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7896829179037544030488009 5922621884278158022866007)
                ·
                  refine ⟨8883932826417237034299011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5922621884278158022866007 8883932826417237034299011)
                  ·
                    refine ⟨13325899239625855551448517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8883932826417237034299011 13325899239625855551448517)
                    ·
                      refine ⟨2498606107429847915896597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13325899239625855551448517 2498606107429847915896597)
                      ·
                        rfl

theorem cell23_4866018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_4866018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866018 prefixEnd_4866018 := by exact prefixLift 4866018
  have htrace : WordTrace (prefixWord ++ tailWord_4866018) baseStart_4866018 baseEnd_4866018 := by
    simpa [prefixWord, tailWord_4866018, baseEnd_4866018] using wordTrace_append hprefix tailTrace_4866018
  have hstable : (prefixWord ++ tailWord_4866018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866018).length < 2 ^ (prefixWord ++ tailWord_4866018).sum := by decide
  have hdescent : baseEnd_4866018 < baseStart_4866018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866027 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 2, 7, 2]
def baseStart_4866027 : Nat := 118140960795 + 4866027 * 2 ^ 59
def prefixEnd_4866027 : Nat := 4983230072969 + 3 ^ 40 * 4866027 * 2
def baseEnd_4866027 : Nat := 2498610728755738380684055

theorem tailTrace_4866027 : CollatzResearch.WordTrace tailWord_4866027 prefixEnd_4866027 2498610728755738380684055 := by
  unfold tailWord_4866027
  simp only [CollatzResearch.WordTrace]
  refine ⟨177478585142222705093340335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118319056761481803395560223 177478585142222705093340335)
  ·
    refine ⟨266217877713334057640010503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177478585142222705093340335 266217877713334057640010503)
    ·
      refine ⟨399326816570001086460015755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266217877713334057640010503 399326816570001086460015755)
      ·
        refine ⟨598990224855001629690023633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399326816570001086460015755 598990224855001629690023633)
        ·
          refine ⟨449242668641251222267517725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 598990224855001629690023633 449242668641251222267517725)
          ·
            refine ⟨168466000740469208350319147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 449242668641251222267517725 168466000740469208350319147)
            ·
              refine ⟨252699001110703812525478721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168466000740469208350319147 252699001110703812525478721)
              ·
                refine ⟨189524250833027859394109041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252699001110703812525478721 189524250833027859394109041)
                ·
                  refine ⟨142143188124770894545581781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189524250833027859394109041 142143188124770894545581781)
                  ·
                    refine ⟨3331480971674317840912073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 142143188124770894545581781 3331480971674317840912073)
                    ·
                      refine ⟨2498610728755738380684055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3331480971674317840912073 2498610728755738380684055)
                      ·
                        rfl

theorem cell23_4866027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 7, 2].length) (baseStart_4866027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866027 prefixEnd_4866027 := by exact prefixLift 4866027
  have htrace : WordTrace (prefixWord ++ tailWord_4866027) baseStart_4866027 baseEnd_4866027 := by
    simpa [prefixWord, tailWord_4866027, baseEnd_4866027] using wordTrace_append hprefix tailTrace_4866027
  have hstable : (prefixWord ++ tailWord_4866027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866027).length < 2 ^ (prefixWord ++ tailWord_4866027).sum := by decide
  have hdescent : baseEnd_4866027 < baseStart_4866027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866052 : List Nat := [2, 3, 2, 4, 2, 1, 1, 1, 3, 2, 2]
def baseStart_4866052 : Nat := 118140960795 + 4866052 * 2 ^ 59
def prefixEnd_4866052 : Nat := 4983230072969 + 3 ^ 40 * 4866052 * 2
def baseEnd_4866052 : Nat := 2498623565772100782871441

theorem tailTrace_4866052 : CollatzResearch.WordTrace tailWord_4866052 prefixEnd_4866052 2498623565772100782871441 := by
  unfold tailWord_4866052
  simp only [CollatzResearch.WordTrace]
  refine ⟨88739748483566067181500205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118319664644754756242000273 88739748483566067181500205)
  ·
    refine ⟨33277405681337275193062577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88739748483566067181500205 33277405681337275193062577)
    ·
      refine ⟨24958054261002956394796933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33277405681337275193062577 24958054261002956394796933)
      ·
        refine ⟨4679635173938054324024425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24958054261002956394796933 4679635173938054324024425)
        ·
          refine ⟨3509726380453540743018319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4679635173938054324024425 3509726380453540743018319)
          ·
            refine ⟨5264589570680311114527479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3509726380453540743018319 5264589570680311114527479)
            ·
              refine ⟨7896884356020466671791219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5264589570680311114527479 7896884356020466671791219)
              ·
                refine ⟨11845326534030700007686829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7896884356020466671791219 11845326534030700007686829)
                ·
                  refine ⟨4441997450261512502882561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11845326534030700007686829 4441997450261512502882561)
                  ·
                    refine ⟨3331498087696134377161921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4441997450261512502882561 3331498087696134377161921)
                    ·
                      refine ⟨2498623565772100782871441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3331498087696134377161921 2498623565772100782871441)
                      ·
                        rfl

theorem cell23_4866052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_4866052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866052 prefixEnd_4866052 := by exact prefixLift 4866052
  have htrace : WordTrace (prefixWord ++ tailWord_4866052) baseStart_4866052 baseEnd_4866052 := by
    simpa [prefixWord, tailWord_4866052, baseEnd_4866052] using wordTrace_append hprefix tailTrace_4866052
  have hstable : (prefixWord ++ tailWord_4866052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866052).length < 2 ^ (prefixWord ++ tailWord_4866052).sum := by decide
  have hdescent : baseEnd_4866052 < baseStart_4866052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866094 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 2, 1, 5]
def baseStart_4866094 : Nat := 118140960795 + 4866094 * 2 ^ 59
def prefixEnd_4866094 : Nat := 4983230072969 + 3 ^ 40 * 4866094 * 2
def baseEnd_4866094 : Nat := 2498645131959589618546247

theorem tailTrace_4866094 : CollatzResearch.WordTrace tailWord_4866094 prefixEnd_4866094 2498645131959589618546247 := by
  unfold tailWord_4866094
  simp only [CollatzResearch.WordTrace]
  refine ⟨22185128604122496942003667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118320685888653317024019557 22185128604122496942003667)
  ·
    refine ⟨33277692906183745413005501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22185128604122496942003667 33277692906183745413005501)
    ·
      refine ⟨12479134839818904529877063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33277692906183745413005501 12479134839818904529877063)
      ·
        refine ⟨18718702259728356794815595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12479134839818904529877063 18718702259728356794815595)
        ·
          refine ⟨28078053389592535192223393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18718702259728356794815595 28078053389592535192223393)
          ·
            refine ⟨21058540042194401394167545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28078053389592535192223393 21058540042194401394167545)
            ·
              refine ⟨15793905031645801045625659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21058540042194401394167545 15793905031645801045625659)
              ·
                refine ⟨23690857547468701568438489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15793905031645801045625659 23690857547468701568438489)
                ·
                  refine ⟨17768143160601526176328867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23690857547468701568438489 17768143160601526176328867)
                  ·
                    refine ⟨26652214740902289264493301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17768143160601526176328867 26652214740902289264493301)
                    ·
                      refine ⟨2498645131959589618546247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26652214740902289264493301 2498645131959589618546247)
                      ·
                        rfl

theorem cell23_4866094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_4866094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866094 prefixEnd_4866094 := by exact prefixLift 4866094
  have htrace : WordTrace (prefixWord ++ tailWord_4866094) baseStart_4866094 baseEnd_4866094 := by
    simpa [prefixWord, tailWord_4866094, baseEnd_4866094] using wordTrace_append hprefix tailTrace_4866094
  have hstable : (prefixWord ++ tailWord_4866094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866094).length < 2 ^ (prefixWord ++ tailWord_4866094).sum := by decide
  have hdescent : baseEnd_4866094 < baseStart_4866094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866107 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 3]
def baseStart_4866107 : Nat := 118140960795 + 4866107 * 2 ^ 59
def prefixEnd_4866107 : Nat := 4983230072969 + 3 ^ 40 * 4866107 * 2
def baseEnd_4866107 : Nat := 2498651807208098067683687

theorem tailTrace_4866107 : CollatzResearch.WordTrace tailWord_4866107 prefixEnd_4866107 2498651807208098067683687 := by
  unfold tailWord_4866107
  simp only [CollatzResearch.WordTrace]
  refine ⟨177481502981932878756252575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118321001987955252504168383 177481502981932878756252575)
  ·
    refine ⟨266222254472899318134378863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177481502981932878756252575 266222254472899318134378863)
    ·
      refine ⟨399333381709348977201568295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266222254472899318134378863 399333381709348977201568295)
      ·
        refine ⟨599000072564023465802352443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399333381709348977201568295 599000072564023465802352443)
        ·
          refine ⟨898500108846035198703528665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599000072564023465802352443 898500108846035198703528665)
          ·
            refine ⟨673875081634526399027646499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 898500108846035198703528665 673875081634526399027646499)
            ·
              refine ⟨1010812622451789598541469749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673875081634526399027646499 1010812622451789598541469749)
              ·
                refine ⟨94763683354855274863262789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1010812622451789598541469749 94763683354855274863262789)
                ·
                  refine ⟨17768190629035364036861773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94763683354855274863262789 17768190629035364036861773)
                  ·
                    refine ⟨6663071485888261513823165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17768190629035364036861773 6663071485888261513823165)
                    ·
                      refine ⟨2498651807208098067683687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6663071485888261513823165 2498651807208098067683687)
                      ·
                        rfl

theorem cell23_4866107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 3, 3].length) (baseStart_4866107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866107 prefixEnd_4866107 := by exact prefixLift 4866107
  have htrace : WordTrace (prefixWord ++ tailWord_4866107) baseStart_4866107 baseEnd_4866107 := by
    simpa [prefixWord, tailWord_4866107, baseEnd_4866107] using wordTrace_append hprefix tailTrace_4866107
  have hstable : (prefixWord ++ tailWord_4866107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866107).length < 2 ^ (prefixWord ++ tailWord_4866107).sum := by decide
  have hdescent : baseEnd_4866107 < baseStart_4866107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866108 : List Nat := [2, 2, 2, 2, 2, 1, 4, 2, 2, 2, 2]
def baseStart_4866108 : Nat := 118140960795 + 4866108 * 2 ^ 59
def prefixEnd_4866108 : Nat := 4983230072969 + 3 ^ 40 * 4866108 * 2
def baseEnd_4866108 : Nat := 2498652320688752563771183

theorem tailTrace_4866108 : CollatzResearch.WordTrace tailWord_4866108 prefixEnd_4866108 2498652320688752563771183 := by
  unfold tailWord_4866108
  simp only [CollatzResearch.WordTrace]
  refine ⟨88740769727464627963519489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118321026303286170618025985 88740769727464627963519489)
  ·
    refine ⟨66555577295598470972639617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88740769727464627963519489 66555577295598470972639617)
    ·
      refine ⟨49916682971698853229479713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66555577295598470972639617 49916682971698853229479713)
      ·
        refine ⟨37437512228774139922109785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49916682971698853229479713 37437512228774139922109785)
        ·
          refine ⟨28078134171580604941582339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37437512228774139922109785 28078134171580604941582339)
          ·
            refine ⟨42117201257370907412373509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28078134171580604941582339 42117201257370907412373509)
            ·
              refine ⟨7896975235757045139820033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42117201257370907412373509 7896975235757045139820033)
              ·
                refine ⟨5922731426817783854865025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7896975235757045139820033 5922731426817783854865025)
                ·
                  refine ⟨4442048570113337891148769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5922731426817783854865025 4442048570113337891148769)
                  ·
                    refine ⟨3331536427585003418361577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4442048570113337891148769 3331536427585003418361577)
                    ·
                      refine ⟨2498652320688752563771183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3331536427585003418361577 2498652320688752563771183)
                      ·
                        rfl

theorem cell23_4866108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_4866108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866108 prefixEnd_4866108 := by exact prefixLift 4866108
  have htrace : WordTrace (prefixWord ++ tailWord_4866108) baseStart_4866108 baseEnd_4866108 := by
    simpa [prefixWord, tailWord_4866108, baseEnd_4866108] using wordTrace_append hprefix tailTrace_4866108
  have hstable : (prefixWord ++ tailWord_4866108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866108).length < 2 ^ (prefixWord ++ tailWord_4866108).sum := by decide
  have hdescent : baseEnd_4866108 < baseStart_4866108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866144 : List Nat := [2, 1, 1, 3, 2, 3, 3, 1, 2, 5]
def baseStart_4866144 : Nat := 118140960795 + 4866144 * 2 ^ 59
def prefixEnd_4866144 : Nat := 4983230072969 + 3 ^ 40 * 4866144 * 2
def baseEnd_4866144 : Nat := 832890268664104807640339

theorem tailTrace_4866144 : CollatzResearch.WordTrace tailWord_4866144 prefixEnd_4866144 832890268664104807640339 := by
  unfold tailWord_4866144
  simp only [CollatzResearch.WordTrace]
  refine ⟨88741426241399417037674743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118321901655199222716899657 88741426241399417037674743)
  ·
    refine ⟨133112139362099125556512115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88741426241399417037674743 133112139362099125556512115)
    ·
      refine ⟨199668209043148688334768173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133112139362099125556512115 199668209043148688334768173)
      ·
        refine ⟨74875578391180758125538065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199668209043148688334768173 74875578391180758125538065)
        ·
          refine ⟨56156683793385568594153549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74875578391180758125538065 56156683793385568594153549)
          ·
            refine ⟨21058756422519588222807581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56156683793385568594153549 21058756422519588222807581)
            ·
              refine ⟨7897033658444845583552843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21058756422519588222807581 7897033658444845583552843)
              ·
                refine ⟨11845550487667268375329265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7897033658444845583552843 11845550487667268375329265)
                ·
                  refine ⟨8884162865750451281496949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11845550487667268375329265 8884162865750451281496949)
                  ·
                    refine ⟨832890268664104807640339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8884162865750451281496949 832890268664104807640339)
                    ·
                      rfl

theorem cell23_4866144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 2, 5].length) (baseStart_4866144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866144 prefixEnd_4866144 := by exact prefixLift 4866144
  have htrace : WordTrace (prefixWord ++ tailWord_4866144) baseStart_4866144 baseEnd_4866144 := by
    simpa [prefixWord, tailWord_4866144, baseEnd_4866144] using wordTrace_append hprefix tailTrace_4866144
  have hstable : (prefixWord ++ tailWord_4866144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866144).length < 2 ^ (prefixWord ++ tailWord_4866144).sum := by decide
  have hdescent : baseEnd_4866144 < baseStart_4866144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866181 : List Nat := [1, 3, 1, 1, 5, 1, 2, 1, 2, 4, 2]
def baseStart_4866181 : Nat := 118140960795 + 4866181 * 2 ^ 59
def prefixEnd_4866181 : Nat := 4983230072969 + 3 ^ 40 * 4866181 * 2
def baseEnd_4866181 : Nat := 2498689804776530778158347

theorem tailTrace_4866181 : CollatzResearch.WordTrace tailWord_4866181 prefixEnd_4866181 2498689804776530778158347 := by
  unfold tailWord_4866181
  simp only [CollatzResearch.WordTrace]
  refine ⟨177484201983664789394446397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118322801322443192929630931 177484201983664789394446397)
  ·
    refine ⟨66556575743874296022917399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177484201983664789394446397 66556575743874296022917399)
    ·
      refine ⟨99834863615811444034376099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66556575743874296022917399 99834863615811444034376099)
      ·
        refine ⟨149752295423717166051564149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99834863615811444034376099 149752295423717166051564149)
        ·
          refine ⟨14039277695973484317334139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 149752295423717166051564149 14039277695973484317334139)
          ·
            refine ⟨21058916543960226476001209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14039277695973484317334139 21058916543960226476001209)
            ·
              refine ⟨15794187407970169857000907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21058916543960226476001209 15794187407970169857000907)
              ·
                refine ⟨23691281111955254785501361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15794187407970169857000907 23691281111955254785501361)
                ·
                  refine ⟨17768460833966441089126021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23691281111955254785501361 17768460833966441089126021)
                  ·
                    refine ⟨3331586406368707704211129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17768460833966441089126021 3331586406368707704211129)
                    ·
                      refine ⟨2498689804776530778158347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3331586406368707704211129 2498689804776530778158347)
                      ·
                        rfl

theorem cell23_4866181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 4, 2].length) (baseStart_4866181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866181 prefixEnd_4866181 := by exact prefixLift 4866181
  have htrace : WordTrace (prefixWord ++ tailWord_4866181) baseStart_4866181 baseEnd_4866181 := by
    simpa [prefixWord, tailWord_4866181, baseEnd_4866181] using wordTrace_append hprefix tailTrace_4866181
  have hstable : (prefixWord ++ tailWord_4866181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866181).length < 2 ^ (prefixWord ++ tailWord_4866181).sum := by decide
  have hdescent : baseEnd_4866181 < baseStart_4866181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866194 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_4866194 : Nat := 118140960795 + 4866194 * 2 ^ 59
def prefixEnd_4866194 : Nat := 4983230072969 + 3 ^ 40 * 4866194 * 2
def baseEnd_4866194 : Nat := 2498696480025039227295787

theorem tailTrace_4866194 : CollatzResearch.WordTrace tailWord_4866194 prefixEnd_4866194 2498696480025039227295787 := by
  unfold tailWord_4866194
  simp only [CollatzResearch.WordTrace]
  refine ⟨44371169033154423153667409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118323117421745128409779757 44371169033154423153667409)
  ·
    refine ⟨33278376774865817365250557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44371169033154423153667409 33278376774865817365250557)
    ·
      refine ⟨12479391290574681511968959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33278376774865817365250557 12479391290574681511968959)
      ·
        refine ⟨18719086935862022267953439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12479391290574681511968959 18719086935862022267953439)
        ·
          refine ⟨28078630403793033401930159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18719086935862022267953439 28078630403793033401930159)
          ·
            refine ⟨42117945605689550102895239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28078630403793033401930159 42117945605689550102895239)
            ·
              refine ⟨63176918408534325154342859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42117945605689550102895239 63176918408534325154342859)
              ·
                refine ⟨94765377612801487731514289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63176918408534325154342859 94765377612801487731514289)
                ·
                  refine ⟨71074033209601115798635717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94765377612801487731514289 71074033209601115798635717)
                  ·
                    refine ⟨13326381226800209212244197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71074033209601115798635717 13326381226800209212244197)
                    ·
                      refine ⟨2498696480025039227295787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13326381226800209212244197 2498696480025039227295787)
                      ·
                        rfl

theorem cell23_4866194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_4866194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866194 prefixEnd_4866194 := by exact prefixLift 4866194
  have htrace : WordTrace (prefixWord ++ tailWord_4866194) baseStart_4866194 baseEnd_4866194 := by
    simpa [prefixWord, tailWord_4866194, baseEnd_4866194] using wordTrace_append hprefix tailTrace_4866194
  have hstable : (prefixWord ++ tailWord_4866194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866194).length < 2 ^ (prefixWord ++ tailWord_4866194).sum := by decide
  have hdescent : baseEnd_4866194 < baseStart_4866194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866208 : List Nat := [2, 1, 1, 4, 2, 2, 3, 3, 1, 4]
def baseStart_4866208 : Nat := 118140960795 + 4866208 * 2 ^ 59
def prefixEnd_4866208 : Nat := 4983230072969 + 3 ^ 40 * 4866208 * 2
def baseEnd_4866208 : Nat := 832901222918067390840241

theorem tailTrace_4866208 : CollatzResearch.WordTrace tailWord_4866208 prefixEnd_4866208 832901222918067390840241 := by
  unfold tailWord_4866208
  simp only [CollatzResearch.WordTrace]
  refine ⟨88742593377283486502839639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118323457836377982003786185 88742593377283486502839639)
  ·
    refine ⟨133113890065925229754259459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88742593377283486502839639 133113890065925229754259459)
    ·
      refine ⟨199670835098887844631389189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133113890065925229754259459 199670835098887844631389189)
      ·
        refine ⟨37438281581041470868385473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199670835098887844631389189 37438281581041470868385473)
        ·
          refine ⟨28078711185781103151289105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37438281581041470868385473 28078711185781103151289105)
          ·
            refine ⟨21059033389335827363466829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28078711185781103151289105 21059033389335827363466829)
            ·
              refine ⟨7897137521000935261300061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21059033389335827363466829 7897137521000935261300061)
              ·
                refine ⟨2961426570375350722987523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7897137521000935261300061 2961426570375350722987523)
                ·
                  refine ⟨4442139855563026084481285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2961426570375350722987523 4442139855563026084481285)
                  ·
                    refine ⟨832901222918067390840241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4442139855563026084481285 832901222918067390840241)
                    ·
                      rfl

theorem cell23_4866208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 3, 1, 4].length) (baseStart_4866208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866208 prefixEnd_4866208 := by exact prefixLift 4866208
  have htrace : WordTrace (prefixWord ++ tailWord_4866208) baseStart_4866208 baseEnd_4866208 := by
    simpa [prefixWord, tailWord_4866208, baseEnd_4866208] using wordTrace_append hprefix tailTrace_4866208
  have hstable : (prefixWord ++ tailWord_4866208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866208).length < 2 ^ (prefixWord ++ tailWord_4866208).sum := by decide
  have hdescent : baseEnd_4866208 < baseStart_4866208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866225 : List Nat := [1, 2, 2, 5, 3, 1, 1, 1, 3, 4]
def baseStart_4866225 : Nat := 118140960795 + 4866225 * 2 ^ 59
def prefixEnd_4866225 : Nat := 4983230072969 + 3 ^ 40 * 4866225 * 2
def baseEnd_4866225 : Nat := 832904132641776202002715

theorem tailTrace_4866225 : CollatzResearch.WordTrace tailWord_4866225 prefixEnd_4866225 832904132641776202002715 := by
  unfold tailWord_4866225
  simp only [CollatzResearch.WordTrace]
  refine ⟨177485806795505384909048129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118323871197003589939365419 177485806795505384909048129)
  ·
    refine ⟨133114355096629038681786097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177485806795505384909048129 133114355096629038681786097)
    ·
      refine ⟨99835766322471779011339573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133114355096629038681786097 99835766322471779011339573)
      ·
        refine ⟨9359603092731729282313085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99835766322471779011339573 9359603092731729282313085)
        ·
          refine ⟨3509851159774398480867407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9359603092731729282313085 3509851159774398480867407)
          ·
            refine ⟨5264776739661597721301111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3509851159774398480867407 5264776739661597721301111)
            ·
              refine ⟨7897165109492396581951667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5264776739661597721301111 7897165109492396581951667)
              ·
                refine ⟨11845747664238594872927501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7897165109492396581951667 11845747664238594872927501)
                ·
                  refine ⟨4442155374089473077347813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11845747664238594872927501 4442155374089473077347813)
                  ·
                    refine ⟨832904132641776202002715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4442155374089473077347813 832904132641776202002715)
                    ·
                      rfl

theorem cell23_4866225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 3, 4].length) (baseStart_4866225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866225 prefixEnd_4866225 := by exact prefixLift 4866225
  have htrace : WordTrace (prefixWord ++ tailWord_4866225) baseStart_4866225 baseEnd_4866225 := by
    simpa [prefixWord, tailWord_4866225, baseEnd_4866225] using wordTrace_append hprefix tailTrace_4866225
  have hstable : (prefixWord ++ tailWord_4866225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866225).length < 2 ^ (prefixWord ++ tailWord_4866225).sum := by decide
  have hdescent : baseEnd_4866225 < baseStart_4866225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866227 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 7]
def baseStart_4866227 : Nat := 118140960795 + 4866227 * 2 ^ 59
def prefixEnd_4866227 : Nat := 4983230072969 + 3 ^ 40 * 4866227 * 2
def baseEnd_4866227 : Nat := 2498713424886637598183135

theorem tailTrace_4866227 : CollatzResearch.WordTrace tailWord_4866227 prefixEnd_4866227 2498713424886637598183135 := by
  unfold tailWord_4866227
  simp only [CollatzResearch.WordTrace]
  refine ⟨177485879741498139250620935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118323919827665426167080623 177485879741498139250620935)
  ·
    refine ⟨266228819612247208875931403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177485879741498139250620935 266228819612247208875931403)
    ·
      refine ⟨399343229418370813313897105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266228819612247208875931403 399343229418370813313897105)
      ·
        refine ⟨299507422063778109985422829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 399343229418370813313897105 299507422063778109985422829)
        ·
          refine ⟨112315283273916791244533561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 299507422063778109985422829 112315283273916791244533561)
          ·
            refine ⟨84236462455437593433400171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112315283273916791244533561 84236462455437593433400171)
            ·
              refine ⟨126354693683156390150100257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84236462455437593433400171 126354693683156390150100257)
              ·
                refine ⟨94766020262367292612575193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126354693683156390150100257 94766020262367292612575193)
                ·
                  refine ⟨71074515196775469459431395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94766020262367292612575193 71074515196775469459431395)
                  ·
                    refine ⟨106611772795163204189147093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71074515196775469459431395 106611772795163204189147093)
                    ·
                      refine ⟨2498713424886637598183135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106611772795163204189147093 2498713424886637598183135)
                      ·
                        rfl

theorem cell23_4866227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_4866227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866227 prefixEnd_4866227 := by exact prefixLift 4866227
  have htrace : WordTrace (prefixWord ++ tailWord_4866227) baseStart_4866227 baseEnd_4866227 := by
    simpa [prefixWord, tailWord_4866227, baseEnd_4866227] using wordTrace_append hprefix tailTrace_4866227
  have hstable : (prefixWord ++ tailWord_4866227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866227).length < 2 ^ (prefixWord ++ tailWord_4866227).sum := by decide
  have hdescent : baseEnd_4866227 < baseStart_4866227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866258 : List Nat := [3, 2, 2, 2, 1, 2, 1, 3, 2, 3, 2]
def baseStart_4866258 : Nat := 118140960795 + 4866258 * 2 ^ 59
def prefixEnd_4866258 : Nat := 4983230072969 + 3 ^ 40 * 4866258 * 2
def baseEnd_4866258 : Nat := 2498729342786926976895493

theorem tailTrace_4866258 : CollatzResearch.WordTrace tailWord_4866258 prefixEnd_4866258 2498729342786926976895493 := by
  unfold tailWord_4866258
  simp only [CollatzResearch.WordTrace]
  refine ⟨44371752601096457886249857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118324673602923887696666285 44371752601096457886249857)
  ·
    refine ⟨33278814450822343414687393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44371752601096457886249857 33278814450822343414687393)
    ·
      refine ⟨24959110838116757561015545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33278814450822343414687393 24959110838116757561015545)
      ·
        refine ⟨18719333128587568170761659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24959110838116757561015545 18719333128587568170761659)
        ·
          refine ⟨28078999692881352256142489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18719333128587568170761659 28078999692881352256142489)
          ·
            refine ⟨21059249769661014192106867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28078999692881352256142489 21059249769661014192106867)
            ·
              refine ⟨31588874654491521288160301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21059249769661014192106867 31588874654491521288160301)
              ·
                refine ⟨11845827995434320483060113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31588874654491521288160301 11845827995434320483060113)
                ·
                  refine ⟨8884370996575740362295085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11845827995434320483060113 8884370996575740362295085)
                  ·
                    refine ⟨3331639123715902635860657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8884370996575740362295085 3331639123715902635860657)
                    ·
                      refine ⟨2498729342786926976895493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3331639123715902635860657 2498729342786926976895493)
                      ·
                        rfl

theorem cell23_4866258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_4866258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866258 prefixEnd_4866258 := by exact prefixLift 4866258
  have htrace : WordTrace (prefixWord ++ tailWord_4866258) baseStart_4866258 baseEnd_4866258 := by
    simpa [prefixWord, tailWord_4866258, baseEnd_4866258] using wordTrace_append hprefix tailTrace_4866258
  have hstable : (prefixWord ++ tailWord_4866258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866258).length < 2 ^ (prefixWord ++ tailWord_4866258).sum := by decide
  have hdescent : baseEnd_4866258 < baseStart_4866258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866264 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 3, 6]
def baseStart_4866264 : Nat := 118140960795 + 4866264 * 2 ^ 59
def prefixEnd_4866264 : Nat := 4983230072969 + 3 ^ 40 * 4866264 * 2
def baseEnd_4866264 : Nat := 832910807890284651140155

theorem tailTrace_4866264 : CollatzResearch.WordTrace tailWord_4866264 prefixEnd_4866264 832910807890284651140155 := by
  unfold tailWord_4866264
  simp only [CollatzResearch.WordTrace]
  refine ⟨88743614621182047284858923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118324819494909396379811897 88743614621182047284858923)
  ·
    refine ⟨133115421931773070927288385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88743614621182047284858923 133115421931773070927288385)
    ·
      refine ⟨99836566448829803195466289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133115421931773070927288385 99836566448829803195466289)
      ·
        refine ⟨74877424836622352396599717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99836566448829803195466289 74877424836622352396599717)
        ·
          refine ⟨14039517156866691074362447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74877424836622352396599717 14039517156866691074362447)
          ·
            refine ⟨21059275735300036611543671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14039517156866691074362447 21059275735300036611543671)
            ·
              refine ⟨31588913602950054917315507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21059275735300036611543671 31588913602950054917315507)
              ·
                refine ⟨47383370404425082375973261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31588913602950054917315507 47383370404425082375973261)
                ·
                  refine ⟨17768763901659405890989973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47383370404425082375973261 17768763901659405890989973)
                  ·
                    refine ⟨832910807890284651140155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17768763901659405890989973 832910807890284651140155)
                    ·
                      rfl

theorem cell23_4866264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 3, 6].length) (baseStart_4866264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866264 prefixEnd_4866264 := by exact prefixLift 4866264
  have htrace : WordTrace (prefixWord ++ tailWord_4866264) baseStart_4866264 baseEnd_4866264 := by
    simpa [prefixWord, tailWord_4866264, baseEnd_4866264] using wordTrace_append hprefix tailTrace_4866264
  have hstable : (prefixWord ++ tailWord_4866264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866264).length < 2 ^ (prefixWord ++ tailWord_4866264).sum := by decide
  have hdescent : baseEnd_4866264 < baseStart_4866264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866284 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 4]
def baseStart_4866284 : Nat := 118140960795 + 4866284 * 2 ^ 59
def prefixEnd_4866284 : Nat := 4983230072969 + 3 ^ 40 * 4866284 * 2
def baseEnd_4866284 : Nat := 2498742693283943875170373

theorem tailTrace_4866284 : CollatzResearch.WordTrace tailWord_4866284 prefixEnd_4866284 2498742693283943875170373 := by
  unfold tailWord_4866284
  simp only [CollatzResearch.WordTrace]
  refine ⟨88743979351145818992722953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118325305801527758656963937 88743979351145818992722953)
  ·
    refine ⟨66557984513359364244542215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88743979351145818992722953 66557984513359364244542215)
    ·
      refine ⟨99836976770039046366813323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66557984513359364244542215 99836976770039046366813323)
      ·
        refine ⟨149755465155058569550219985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99836976770039046366813323 149755465155058569550219985)
        ·
          refine ⟨112316598866293927162664989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149755465155058569550219985 112316598866293927162664989)
          ·
            refine ⟨42118724574860222685999371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112316598866293927162664989 42118724574860222685999371)
            ·
              refine ⟨63178086862290334028999057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42118724574860222685999371 63178086862290334028999057)
              ·
                refine ⟨47383565146717750521749293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63178086862290334028999057 47383565146717750521749293)
                ·
                  refine ⟨17768836930019156445655985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47383565146717750521749293 17768836930019156445655985)
                  ·
                    refine ⟨13326627697514367334241989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17768836930019156445655985 13326627697514367334241989)
                    ·
                      refine ⟨2498742693283943875170373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13326627697514367334241989 2498742693283943875170373)
                      ·
                        rfl

theorem cell23_4866284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 4].length) (baseStart_4866284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866284 prefixEnd_4866284 := by exact prefixLift 4866284
  have htrace : WordTrace (prefixWord ++ tailWord_4866284) baseStart_4866284 baseEnd_4866284 := by
    simpa [prefixWord, tailWord_4866284, baseEnd_4866284] using wordTrace_append hprefix tailTrace_4866284
  have hstable : (prefixWord ++ tailWord_4866284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866284).length < 2 ^ (prefixWord ++ tailWord_4866284).sum := by decide
  have hdescent : baseEnd_4866284 < baseStart_4866284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866321 : List Nat := [1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 3]
def baseStart_4866321 : Nat := 118140960795 + 4866321 * 2 ^ 59
def prefixEnd_4866321 : Nat := 4983230072969 + 3 ^ 40 * 4866321 * 2
def baseEnd_4866321 : Nat := 2498761692068160230407703

theorem tailTrace_4866321 : CollatzResearch.WordTrace tailWord_4866321 prefixEnd_4866321 2498761692068160230407703 := by
  unfold tailWord_4866321
  simp only [CollatzResearch.WordTrace]
  refine ⟨177489308203157593304542817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118326205468771728869695211 177489308203157593304542817)
  ·
    refine ⟨133116981152368194978407113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177489308203157593304542817 133116981152368194978407113)
    ·
      refine ⟨99837735864276146233805335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133116981152368194978407113 99837735864276146233805335)
      ·
        refine ⟨149756603796414219350708003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99837735864276146233805335 149756603796414219350708003)
        ·
          refine ⟨224634905694621329026062005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149756603796414219350708003 224634905694621329026062005)
          ·
            refine ⟨21059522408870749596193313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 224634905694621329026062005 21059522408870749596193313)
            ·
              refine ⟨15794641806653062197144985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21059522408870749596193313 15794641806653062197144985)
              ·
                refine ⟨11845981354989796647858739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15794641806653062197144985 11845981354989796647858739)
                ·
                  refine ⟨17768972032484694971788109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11845981354989796647858739 17768972032484694971788109)
                  ·
                    refine ⟨6663364512181760614420541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17768972032484694971788109 6663364512181760614420541)
                    ·
                      refine ⟨2498761692068160230407703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6663364512181760614420541 2498761692068160230407703)
                      ·
                        rfl

theorem cell23_4866321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_4866321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866321 prefixEnd_4866321 := by exact prefixLift 4866321
  have htrace : WordTrace (prefixWord ++ tailWord_4866321) baseStart_4866321 baseEnd_4866321 := by
    simpa [prefixWord, tailWord_4866321, baseEnd_4866321] using wordTrace_append hprefix tailTrace_4866321
  have hstable : (prefixWord ++ tailWord_4866321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866321).length < 2 ^ (prefixWord ++ tailWord_4866321).sum := by decide
  have hdescent : baseEnd_4866321 < baseStart_4866321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866355 : List Nat := [1, 1, 1, 2, 5, 1, 5, 1, 2, 1, 3]
def baseStart_4866355 : Nat := 118140960795 + 4866355 * 2 ^ 59
def prefixEnd_4866355 : Nat := 4983230072969 + 3 ^ 40 * 4866355 * 2
def baseEnd_4866355 : Nat := 2498779150410413097382547

theorem tailTrace_4866355 : CollatzResearch.WordTrace tailWord_4866355 prefixEnd_4866355 2498779150410413097382547 := by
  unfold tailWord_4866355
  simp only [CollatzResearch.WordTrace]
  refine ⟨177490548285034417111280519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118327032190022944740853679 177490548285034417111280519)
  ·
    refine ⟨266235822427551625666920779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177490548285034417111280519 266235822427551625666920779)
    ·
      refine ⟨399353733641327438500381169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266235822427551625666920779 399353733641327438500381169)
      ·
        refine ⟨299515300230995578875285877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 399353733641327438500381169 299515300230995578875285877)
        ·
          refine ⟨28079559396655835519558051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 299515300230995578875285877 28079559396655835519558051)
          ·
            refine ⟨42119339094983753279337077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28079559396655835519558051 42119339094983753279337077)
            ·
              refine ⟨3948688040154726869937851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42119339094983753279337077 3948688040154726869937851)
              ·
                refine ⟨5923032060232090304906777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3948688040154726869937851 5923032060232090304906777)
                ·
                  refine ⟨4442274045174067728680083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5923032060232090304906777 4442274045174067728680083)
                  ·
                    refine ⟨6663411067761101593020125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4442274045174067728680083 6663411067761101593020125)
                    ·
                      refine ⟨2498779150410413097382547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6663411067761101593020125 2498779150410413097382547)
                      ·
                        rfl

theorem cell23_4866355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 2, 1, 3].length) (baseStart_4866355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866355 prefixEnd_4866355 := by exact prefixLift 4866355
  have htrace : WordTrace (prefixWord ++ tailWord_4866355) baseStart_4866355 baseEnd_4866355 := by
    simpa [prefixWord, tailWord_4866355, baseEnd_4866355] using wordTrace_append hprefix tailTrace_4866355
  have hstable : (prefixWord ++ tailWord_4866355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866355).length < 2 ^ (prefixWord ++ tailWord_4866355).sum := by decide
  have hdescent : baseEnd_4866355 < baseStart_4866355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866394 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9]
def baseStart_4866394 : Nat := 118140960795 + 4866394 * 2 ^ 59
def prefixEnd_4866394 : Nat := 4983230072969 + 3 ^ 40 * 4866394 * 2
def baseEnd_4866394 : Nat := 2498799176155938444794867

theorem tailTrace_4866394 : CollatzResearch.WordTrace tailWord_4866394 prefixEnd_4866394 2498799176155938444794867 := by
  unfold tailWord_4866394
  simp only [CollatzResearch.WordTrace]
  refine ⟨44372992682973281692987559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118327980487928751181300157 44372992682973281692987559)
  ·
    refine ⟨66559489024459922539481339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44372992682973281692987559 66559489024459922539481339)
    ·
      refine ⟨99839233536689883809222009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66559489024459922539481339 99839233536689883809222009)
      ·
        refine ⟨74879425152517412856916507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99839233536689883809222009 74879425152517412856916507)
        ·
          refine ⟨112319137728776119285374761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74879425152517412856916507 112319137728776119285374761)
          ·
            refine ⟨84239353296582089464031071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112319137728776119285374761 84239353296582089464031071)
            ·
              refine ⟨126359029944873134196046607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84239353296582089464031071 126359029944873134196046607)
              ·
                refine ⟨189538544917309701294069911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126359029944873134196046607 189538544917309701294069911)
                ·
                  refine ⟨284307817375964551941104867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189538544917309701294069911 284307817375964551941104867)
                  ·
                    refine ⟨426461726063946827911657301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 284307817375964551941104867 426461726063946827911657301)
                    ·
                      refine ⟨2498799176155938444794867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 426461726063946827911657301 2498799176155938444794867)
                      ·
                        rfl

theorem cell23_4866394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_4866394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866394 prefixEnd_4866394 := by exact prefixLift 4866394
  have htrace : WordTrace (prefixWord ++ tailWord_4866394) baseStart_4866394 baseEnd_4866394 := by
    simpa [prefixWord, tailWord_4866394, baseEnd_4866394] using wordTrace_append hprefix tailTrace_4866394
  have hstable : (prefixWord ++ tailWord_4866394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866394).length < 2 ^ (prefixWord ++ tailWord_4866394).sum := by decide
  have hdescent : baseEnd_4866394 < baseStart_4866394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866412 : List Nat := [2, 2, 1, 1, 6, 1, 1, 3, 2, 2, 2]
def baseStart_4866412 : Nat := 118140960795 + 4866412 * 2 ^ 59
def prefixEnd_4866412 : Nat := 4983230072969 + 3 ^ 40 * 4866412 * 2
def baseEnd_4866412 : Nat := 2498808418807719374369785

theorem tailTrace_4866412 : CollatzResearch.WordTrace tailWord_4866412 prefixEnd_4866412 2498808418807719374369785 := by
  unfold tailWord_4866412
  simp only [CollatzResearch.WordTrace]
  refine ⟨88746313622913957923052745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118328418163885277230736993 88746313622913957923052745)
  ·
    refine ⟨66559735217185468442289559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88746313622913957923052745 66559735217185468442289559)
    ·
      refine ⟨99839602825778202663434339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66559735217185468442289559 99839602825778202663434339)
      ·
        refine ⟨149759404238667303995151509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99839602825778202663434339 149759404238667303995151509)
        ·
          refine ⟨7019972073687529874772727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 149759404238667303995151509 7019972073687529874772727)
          ·
            refine ⟨10529958110531294812159091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7019972073687529874772727 10529958110531294812159091)
            ·
              refine ⟨15794937165796942218238637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10529958110531294812159091 15794937165796942218238637)
              ·
                refine ⟨5923101437173853331839489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15794937165796942218238637 5923101437173853331839489)
                ·
                  refine ⟨4442326077880389998879617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5923101437173853331839489 4442326077880389998879617)
                  ·
                    refine ⟨3331744558410292499159713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4442326077880389998879617 3331744558410292499159713)
                    ·
                      refine ⟨2498808418807719374369785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3331744558410292499159713 2498808418807719374369785)
                      ·
                        rfl

theorem cell23_4866412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 2, 2].length) (baseStart_4866412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866412 prefixEnd_4866412 := by exact prefixLift 4866412
  have htrace : WordTrace (prefixWord ++ tailWord_4866412) baseStart_4866412 baseEnd_4866412 := by
    simpa [prefixWord, tailWord_4866412, baseEnd_4866412] using wordTrace_append hprefix tailTrace_4866412
  have hstable : (prefixWord ++ tailWord_4866412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866412).length < 2 ^ (prefixWord ++ tailWord_4866412).sum := by decide
  have hdescent : baseEnd_4866412 < baseStart_4866412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866441 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 1, 2, 5]
def baseStart_4866441 : Nat := 118140960795 + 4866441 * 2 ^ 59
def prefixEnd_4866441 : Nat := 4983230072969 + 3 ^ 40 * 4866441 * 2
def baseEnd_4866441 : Nat := 2498823309746699760907151

theorem tailTrace_4866441 : CollatzResearch.WordTrace tailWord_4866441 prefixEnd_4866441 2498823309746699760907151 := by
  unfold tailWord_4866441
  simp only [CollatzResearch.WordTrace]
  refine ⟨177493684962722853798911177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118329123308481902532607451 177493684962722853798911177)
  ·
    refine ⟨133120263722042140349183383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177493684962722853798911177 133120263722042140349183383)
    ·
      refine ⟨199680395583063210523775075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133120263722042140349183383 199680395583063210523775075)
      ·
        refine ⟨299520593374594815785662613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199680395583063210523775075 299520593374594815785662613)
        ·
          refine ⟨14040027814434131989952935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 299520593374594815785662613 14040027814434131989952935)
          ·
            refine ⟨21060041721651197984929403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14040027814434131989952935 21060041721651197984929403)
            ·
              refine ⟨31590062582476796977394105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21060041721651197984929403 31590062582476796977394105)
              ·
                refine ⟨23692546936857597733045579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31590062582476796977394105 23692546936857597733045579)
                ·
                  refine ⟨35538820405286396599568369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23692546936857597733045579 35538820405286396599568369)
                  ·
                    refine ⟨26654115303964797449676277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35538820405286396599568369 26654115303964797449676277)
                    ·
                      refine ⟨2498823309746699760907151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26654115303964797449676277 2498823309746699760907151)
                      ·
                        rfl

theorem cell23_4866441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 2, 5].length) (baseStart_4866441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866441 prefixEnd_4866441 := by exact prefixLift 4866441
  have htrace : WordTrace (prefixWord ++ tailWord_4866441) baseStart_4866441 baseEnd_4866441 := by
    simpa [prefixWord, tailWord_4866441, baseEnd_4866441] using wordTrace_append hprefix tailTrace_4866441
  have hstable : (prefixWord ++ tailWord_4866441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866441).length < 2 ^ (prefixWord ++ tailWord_4866441).sum := by decide
  have hdescent : baseEnd_4866441 < baseStart_4866441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866468 : List Nat := [2, 3, 1, 2, 1, 1, 3, 1, 1, 6, 2]
def baseStart_4866468 : Nat := 118140960795 + 4866468 * 2 ^ 59
def prefixEnd_4866468 : Nat := 4983230072969 + 3 ^ 40 * 4866468 * 2
def baseEnd_4866468 : Nat := 2498837173724371155269527

theorem tailTrace_4866468 : CollatzResearch.WordTrace tailWord_4866468 prefixEnd_4866468 2498837173724371155269527 := by
  unfold tailWord_4866468
  simp only [CollatzResearch.WordTrace]
  refine ⟨88747334866812518705072029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118329779822416691606762705 88747334866812518705072029)
  ·
    refine ⟨33280250575054694514402011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88747334866812518705072029 33280250575054694514402011)
    ·
      refine ⟨49920375862582041771603017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33280250575054694514402011 49920375862582041771603017)
      ·
        refine ⟨37440281896936531328702263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49920375862582041771603017 37440281896936531328702263)
        ·
          refine ⟨56160422845404796993053395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37440281896936531328702263 56160422845404796993053395)
          ·
            refine ⟨84240634268107195489580093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56160422845404796993053395 84240634268107195489580093)
            ·
              refine ⟨31590237850540198308592535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84240634268107195489580093 31590237850540198308592535)
              ·
                refine ⟨47385356775810297462888803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31590237850540198308592535 47385356775810297462888803)
                ·
                  refine ⟨71078035163715446194333205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47385356775810297462888803 71078035163715446194333205)
                  ·
                    refine ⟨3331782898299161540359369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71078035163715446194333205 3331782898299161540359369)
                    ·
                      refine ⟨2498837173724371155269527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3331782898299161540359369 2498837173724371155269527)
                      ·
                        rfl

theorem cell23_4866468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_4866468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866468 prefixEnd_4866468 := by exact prefixLift 4866468
  have htrace : WordTrace (prefixWord ++ tailWord_4866468) baseStart_4866468 baseEnd_4866468 := by
    simpa [prefixWord, tailWord_4866468, baseEnd_4866468] using wordTrace_append hprefix tailTrace_4866468
  have hstable : (prefixWord ++ tailWord_4866468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866468).length < 2 ^ (prefixWord ++ tailWord_4866468).sum := by decide
  have hdescent : baseEnd_4866468 < baseStart_4866468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866501 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 3, 7, 3]
def baseStart_4866501 : Nat := 118140960795 + 4866501 * 2 ^ 59
def prefixEnd_4866501 : Nat := 4983230072969 + 3 ^ 40 * 4866501 * 2
def baseEnd_4866501 : Nat := 2498854118585969526156875

theorem tailTrace_4866501 : CollatzResearch.WordTrace tailWord_4866501 prefixEnd_4866501 2498854118585969526156875 := by
  unfold tailWord_4866501
  simp only [CollatzResearch.WordTrace]
  refine ⟨177495873342505484046095357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118330582228336989364063571 177495873342505484046095357)
  ·
    refine ⟨66560952503439556517285759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177495873342505484046095357 66560952503439556517285759)
    ·
      refine ⟨99841428755159334775928639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66560952503439556517285759 99841428755159334775928639)
      ·
        refine ⟨149762143132739002163892959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99841428755159334775928639 149762143132739002163892959)
        ·
          refine ⟨224643214699108503245839439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149762143132739002163892959 224643214699108503245839439)
          ·
            refine ⟨336964822048662754868759159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224643214699108503245839439 336964822048662754868759159)
            ·
              refine ⟨505447233072994132303138739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336964822048662754868759159 505447233072994132303138739)
              ·
                refine ⟨758170849609491198454708109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505447233072994132303138739 758170849609491198454708109)
                ·
                  refine ⟨284314068603559199420515541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 758170849609491198454708109 284314068603559199420515541)
                  ·
                    refine ⟨6663610982895918736418333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 284314068603559199420515541 6663610982895918736418333)
                    ·
                      refine ⟨2498854118585969526156875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6663610982895918736418333 2498854118585969526156875)
                      ·
                        rfl

theorem cell23_4866501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_4866501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866501 prefixEnd_4866501 := by exact prefixLift 4866501
  have htrace : WordTrace (prefixWord ++ tailWord_4866501) baseStart_4866501 baseEnd_4866501 := by
    simpa [prefixWord, tailWord_4866501, baseEnd_4866501] using wordTrace_append hprefix tailTrace_4866501
  have hstable : (prefixWord ++ tailWord_4866501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866501).length < 2 ^ (prefixWord ++ tailWord_4866501).sum := by decide
  have hdescent : baseEnd_4866501 < baseStart_4866501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866508 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 8]
def baseStart_4866508 : Nat := 118140960795 + 4866508 * 2 ^ 59
def prefixEnd_4866508 : Nat := 4983230072969 + 3 ^ 40 * 4866508 * 2
def baseEnd_4866508 : Nat := 277650856994505666529927

theorem tailTrace_4866508 : CollatzResearch.WordTrace tailWord_4866508 prefixEnd_4866508 277650856994505666529927 := by
  unfold tailWord_4866508
  simp only [CollatzResearch.WordTrace]
  refine ⟨88748064326740062120800089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118330752435653416161066785 88748064326740062120800089)
  ·
    refine ⟨66561048245055046590600067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88748064326740062120800089 66561048245055046590600067)
    ·
      refine ⟨99841572367582569885900101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66561048245055046590600067 99841572367582569885900101)
      ·
        refine ⟨18720294818921731853606269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99841572367582569885900101 18720294818921731853606269)
        ·
          refine ⟨7020110557095649445102351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18720294818921731853606269 7020110557095649445102351)
          ·
            refine ⟨10530165835643474167653527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7020110557095649445102351 10530165835643474167653527)
            ·
              refine ⟨15795248753465211251480291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10530165835643474167653527 15795248753465211251480291)
              ·
                refine ⟨23692873130197816877220437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15795248753465211251480291 23692873130197816877220437)
                ·
                  refine ⟨277650856994505666529927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23692873130197816877220437 277650856994505666529927)
                  ·
                    rfl

theorem cell23_4866508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 8].length) (baseStart_4866508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866508 prefixEnd_4866508 := by exact prefixLift 4866508
  have htrace : WordTrace (prefixWord ++ tailWord_4866508) baseStart_4866508 baseEnd_4866508 := by
    simpa [prefixWord, tailWord_4866508, baseEnd_4866508] using wordTrace_append hprefix tailTrace_4866508
  have hstable : (prefixWord ++ tailWord_4866508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866508).length < 2 ^ (prefixWord ++ tailWord_4866508).sum := by decide
  have hdescent : baseEnd_4866508 < baseStart_4866508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866525 : List Nat := [1, 4, 3, 1, 1, 1, 5, 1, 6]
def baseStart_4866525 : Nat := 118140960795 + 4866525 * 2 ^ 59
def prefixEnd_4866525 : Nat := 4983230072969 + 3 ^ 40 * 4866525 * 2
def baseEnd_4866525 : Nat := 277651826902408603584085

theorem tailTrace_4866525 : CollatzResearch.WordTrace tailWord_4866525 prefixEnd_4866525 277651826902408603584085 := by
  unfold tailWord_4866525
  simp only [CollatzResearch.WordTrace]
  refine ⟨177496748694418536144969029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118331165796279024096646019 177496748694418536144969029)
  ·
    refine ⟨33280640380203475527181693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177496748694418536144969029 33280640380203475527181693)
    ·
      refine ⟨12480240142576303322693135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33280640380203475527181693 12480240142576303322693135)
      ·
        refine ⟨18720360213864454984039703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12480240142576303322693135 18720360213864454984039703)
        ·
          refine ⟨28080540320796682476059555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18720360213864454984039703 28080540320796682476059555)
          ·
            refine ⟨42120810481195023714089333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28080540320796682476059555 42120810481195023714089333)
            ·
              refine ⟨3948825982612033473195875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42120810481195023714089333 3948825982612033473195875)
              ·
                refine ⟨5923238973918050209793813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3948825982612033473195875 5923238973918050209793813)
                ·
                  refine ⟨277651826902408603584085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5923238973918050209793813 277651826902408603584085)
                  ·
                    rfl

theorem cell23_4866525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_4866525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866525 prefixEnd_4866525 := by exact prefixLift 4866525
  have htrace : WordTrace (prefixWord ++ tailWord_4866525) baseStart_4866525 baseEnd_4866525 := by
    simpa [prefixWord, tailWord_4866525, baseEnd_4866525] using wordTrace_append hprefix tailTrace_4866525
  have hstable : (prefixWord ++ tailWord_4866525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866525).length < 2 ^ (prefixWord ++ tailWord_4866525).sum := by decide
  have hdescent : baseEnd_4866525 < baseStart_4866525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866528 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 3, 5, 2]
def baseStart_4866528 : Nat := 118140960795 + 4866528 * 2 ^ 59
def prefixEnd_4866528 : Nat := 4983230072969 + 3 ^ 40 * 4866528 * 2
def baseEnd_4866528 : Nat := 2498867982563640920519251

theorem tailTrace_4866528 : CollatzResearch.WordTrace tailWord_4866528 prefixEnd_4866528 2498867982563640920519251 := by
  unfold tailWord_4866528
  simp only [CollatzResearch.WordTrace]
  refine ⟨88748429056703833828664119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118331238742271778438218825 88748429056703833828664119)
  ·
    refine ⟨133122643585055750742996179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88748429056703833828664119 133122643585055750742996179)
    ·
      refine ⟨199683965377583626114494269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133122643585055750742996179 199683965377583626114494269)
      ·
        refine ⟨74881487016593859792935351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199683965377583626114494269 74881487016593859792935351)
        ·
          refine ⟨112322230524890789689403027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74881487016593859792935351 112322230524890789689403027)
          ·
            refine ⟨168483345787336184534104541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112322230524890789689403027 168483345787336184534104541)
            ·
              refine ⟨63181254670251069200289203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168483345787336184534104541 63181254670251069200289203)
              ·
                refine ⟨94771882005376603800433805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63181254670251069200289203 94771882005376603800433805)
                ·
                  refine ⟨35539455752016226425162677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94771882005376603800433805 35539455752016226425162677)
                  ·
                    refine ⟨3331823976751521227359001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35539455752016226425162677 3331823976751521227359001)
                    ·
                      refine ⟨2498867982563640920519251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3331823976751521227359001 2498867982563640920519251)
                      ·
                        rfl

theorem cell23_4866528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_4866528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866528 prefixEnd_4866528 := by exact prefixLift 4866528
  have htrace : WordTrace (prefixWord ++ tailWord_4866528) baseStart_4866528 baseEnd_4866528 := by
    simpa [prefixWord, tailWord_4866528, baseEnd_4866528] using wordTrace_append hprefix tailTrace_4866528
  have hstable : (prefixWord ++ tailWord_4866528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866528).length < 2 ^ (prefixWord ++ tailWord_4866528).sum := by decide
  have hdescent : baseEnd_4866528 < baseStart_4866528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866535 : List Nat := [1, 1, 5, 2, 1, 1, 1, 4, 3, 1, 3]
def baseStart_4866535 : Nat := 118140960795 + 4866535 * 2 ^ 59
def prefixEnd_4866535 : Nat := 4983230072969 + 3 ^ 40 * 4866535 * 2
def baseEnd_4866535 : Nat := 2498871576928222393131719

theorem tailTrace_4866535 : CollatzResearch.WordTrace tailWord_4866535 prefixEnd_4866535 2498871576928222393131719 := by
  unfold tailWord_4866535
  simp only [CollatzResearch.WordTrace]
  refine ⟨177497113424382307852833059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118331408949588205235222039 177497113424382307852833059)
  ·
    refine ⟨266245670136573461779249589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177497113424382307852833059 266245670136573461779249589)
    ·
      refine ⟨24960531575303762041804649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 266245670136573461779249589 24960531575303762041804649)
      ·
        refine ⟨18720398681477821531353487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24960531575303762041804649 18720398681477821531353487)
        ·
          refine ⟨28080598022216732297030231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18720398681477821531353487 28080598022216732297030231)
          ·
            refine ⟨42120897033325098445545347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28080598022216732297030231 42120897033325098445545347)
            ·
              refine ⟨63181345549987647668318021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42120897033325098445545347 63181345549987647668318021)
              ·
                refine ⟨11846502290622683937809629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63181345549987647668318021 11846502290622683937809629)
                ·
                  refine ⟨4442438358983506476678611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11846502290622683937809629 4442438358983506476678611)
                  ·
                    refine ⟨6663657538475259715017917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4442438358983506476678611 6663657538475259715017917)
                    ·
                      refine ⟨2498871576928222393131719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6663657538475259715017917 2498871576928222393131719)
                      ·
                        rfl

theorem cell23_4866535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_4866535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866535 prefixEnd_4866535 := by exact prefixLift 4866535
  have htrace : WordTrace (prefixWord ++ tailWord_4866535) baseStart_4866535 baseEnd_4866535 := by
    simpa [prefixWord, tailWord_4866535, baseEnd_4866535] using wordTrace_append hprefix tailTrace_4866535
  have hstable : (prefixWord ++ tailWord_4866535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866535).length < 2 ^ (prefixWord ++ tailWord_4866535).sum := by decide
  have hdescent : baseEnd_4866535 < baseStart_4866535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866545 : List Nat := [1, 2, 2, 2, 3, 1, 2, 3, 2, 3, 2]
def baseStart_4866545 : Nat := 118140960795 + 4866545 * 2 ^ 59
def prefixEnd_4866545 : Nat := 4983230072969 + 3 ^ 40 * 4866545 * 2
def baseEnd_4866545 : Nat := 2498876711734767354006673

theorem tailTrace_4866545 : CollatzResearch.WordTrace tailWord_4866545 prefixEnd_4866545 2498876711734767354006673 := by
  unfold tailWord_4866545
  simp only [CollatzResearch.WordTrace]
  refine ⟨177497478154346079560697089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118331652102897386373798059 177497478154346079560697089)
  ·
    refine ⟨133123108615759559670522817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177497478154346079560697089 133123108615759559670522817)
    ·
      refine ⟨99842331461819669752892113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133123108615759559670522817 99842331461819669752892113)
      ·
        refine ⟨74881748596364752314669085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99842331461819669752892113 74881748596364752314669085)
        ·
          refine ⟨28080655723636782118000907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74881748596364752314669085 28080655723636782118000907)
          ·
            refine ⟨42120983585455173177001361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28080655723636782118000907 42120983585455173177001361)
            ·
              refine ⟨31590737689091379882751021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42120983585455173177001361 31590737689091379882751021)
              ·
                refine ⟨11846526633409267456031633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31590737689091379882751021 11846526633409267456031633)
                ·
                  refine ⟨8884894975056950592023725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11846526633409267456031633 8884894975056950592023725)
                  ·
                    refine ⟨3331835615646356472008897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8884894975056950592023725 3331835615646356472008897)
                    ·
                      refine ⟨2498876711734767354006673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3331835615646356472008897 2498876711734767354006673)
                      ·
                        rfl

theorem cell23_4866545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_4866545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866545 prefixEnd_4866545 := by exact prefixLift 4866545
  have htrace : WordTrace (prefixWord ++ tailWord_4866545) baseStart_4866545 baseEnd_4866545 := by
    simpa [prefixWord, tailWord_4866545, baseEnd_4866545] using wordTrace_append hprefix tailTrace_4866545
  have hstable : (prefixWord ++ tailWord_4866545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866545).length < 2 ^ (prefixWord ++ tailWord_4866545).sum := by decide
  have hdescent : baseEnd_4866545 < baseStart_4866545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866546 : List Nat := [3, 2, 1, 4, 3, 1, 1, 3, 1, 4]
def baseStart_4866546 : Nat := 118140960795 + 4866546 * 2 ^ 59
def prefixEnd_4866546 : Nat := 4983230072969 + 3 ^ 40 * 4866546 * 2
def baseEnd_4866546 : Nat := 832959075071807283364723

theorem tailTrace_4866546 : CollatzResearch.WordTrace tailWord_4866546 prefixEnd_4866546 832959075071807283364723 := by
  unfold tailWord_4866546
  simp only [CollatzResearch.WordTrace]
  refine ⟨44374378656835614182870873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118331676418228304487655661 44374378656835614182870873)
  ·
    refine ⟨33280783992626710637153155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44374378656835614182870873 33280783992626710637153155)
    ·
      refine ⟨49921175988940065955729733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33280783992626710637153155 49921175988940065955729733)
      ·
        refine ⟨9360220497926262366699325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49921175988940065955729733 9360220497926262366699325)
        ·
          refine ⟨3510082686722348387512247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9360220497926262366699325 3510082686722348387512247)
          ·
            refine ⟨5265124030083522581268371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3510082686722348387512247 5265124030083522581268371)
            ·
              refine ⟨7897686045125283871902557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5265124030083522581268371 7897686045125283871902557)
              ·
                refine ⟨2961632266921981451963459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7897686045125283871902557 2961632266921981451963459)
                ·
                  refine ⟨4442448400382972177945189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2961632266921981451963459 4442448400382972177945189)
                  ·
                    refine ⟨832959075071807283364723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4442448400382972177945189 832959075071807283364723)
                    ·
                      rfl

theorem cell23_4866546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_4866546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866546 prefixEnd_4866546 := by exact prefixLift 4866546
  have htrace : WordTrace (prefixWord ++ tailWord_4866546) baseStart_4866546 baseEnd_4866546 := by
    simpa [prefixWord, tailWord_4866546, baseEnd_4866546] using wordTrace_append hprefix tailTrace_4866546
  have hstable : (prefixWord ++ tailWord_4866546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866546).length < 2 ^ (prefixWord ++ tailWord_4866546).sum := by decide
  have hdescent : baseEnd_4866546 < baseStart_4866546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866588 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_4866588 : Nat := 118140960795 + 4866588 * 2 ^ 59
def prefixEnd_4866588 : Nat := 4983230072969 + 3 ^ 40 * 4866588 * 2
def baseEnd_4866588 : Nat := 2498898791402910685768975

theorem tailTrace_4866588 : CollatzResearch.WordTrace tailWord_4866588 prefixEnd_4866588 2498898791402910685768975 := by
  unfold tailWord_4866588
  simp only [CollatzResearch.WordTrace]
  refine ⟨88749523246595148952256209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118332697662126865269674945 88749523246595148952256209)
  ·
    refine ⟨66562142434946361714192157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88749523246595148952256209 66562142434946361714192157)
    ·
      refine ⟨24960803413104885642822059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66562142434946361714192157 24960803413104885642822059)
      ·
        refine ⟨37441205119657328464233089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24960803413104885642822059 37441205119657328464233089)
        ·
          refine ⟨28080903839742996348174817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37441205119657328464233089 28080903839742996348174817)
          ·
            refine ⟨21060677879807247261131113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28080903839742996348174817 21060677879807247261131113)
            ·
              refine ⟨15795508409855435445848335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21060677879807247261131113 15795508409855435445848335)
              ·
                refine ⟨23693262614783153168772503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15795508409855435445848335 23693262614783153168772503)
                ·
                  refine ⟨35539893922174729753158755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23693262614783153168772503 35539893922174729753158755)
                  ·
                    refine ⟨53309840883262094629738133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35539893922174729753158755 53309840883262094629738133)
                    ·
                      refine ⟨2498898791402910685768975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53309840883262094629738133 2498898791402910685768975)
                      ·
                        rfl

theorem cell23_4866588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_4866588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866588 prefixEnd_4866588 := by exact prefixLift 4866588
  have htrace : WordTrace (prefixWord ++ tailWord_4866588) baseStart_4866588 baseEnd_4866588 := by
    simpa [prefixWord, tailWord_4866588, baseEnd_4866588] using wordTrace_append hprefix tailTrace_4866588
  have hstable : (prefixWord ++ tailWord_4866588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866588).length < 2 ^ (prefixWord ++ tailWord_4866588).sum := by decide
  have hdescent : baseEnd_4866588 < baseStart_4866588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866595 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 3]
def baseStart_4866595 : Nat := 118140960795 + 4866595 * 2 ^ 59
def prefixEnd_4866595 : Nat := 4983230072969 + 3 ^ 40 * 4866595 * 2
def baseEnd_4866595 : Nat := 2498902385767492158381443

theorem tailTrace_4866595 : CollatzResearch.WordTrace tailWord_4866595 prefixEnd_4866595 2498902385767492158381443 := by
  unfold tailWord_4866595
  simp only [CollatzResearch.WordTrace]
  refine ⟨177499301804164938100017239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118332867869443292066678159 177499301804164938100017239)
  ·
    refine ⟨266248952706247407150025859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177499301804164938100017239 266248952706247407150025859)
    ·
      refine ⟨399373429059371110725038789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266248952706247407150025859 399373429059371110725038789)
      ·
        refine ⟨74882517948632083260944773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 399373429059371110725038789 74882517948632083260944773)
        ·
          refine ⟨14040472115368515611427145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74882517948632083260944773 14040472115368515611427145)
          ·
            refine ⟨10530354086526386708570359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14040472115368515611427145 10530354086526386708570359)
            ·
              refine ⟨15795531129789580062855539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10530354086526386708570359 15795531129789580062855539)
              ·
                refine ⟨23693296694684370094283309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15795531129789580062855539 23693296694684370094283309)
                ·
                  refine ⟨8884986260506638785356241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23693296694684370094283309 8884986260506638785356241)
                  ·
                    refine ⟨6663739695379979089017181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8884986260506638785356241 6663739695379979089017181)
                    ·
                      refine ⟨2498902385767492158381443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6663739695379979089017181 2498902385767492158381443)
                      ·
                        rfl

theorem cell23_4866595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_4866595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866595 prefixEnd_4866595 := by exact prefixLift 4866595
  have htrace : WordTrace (prefixWord ++ tailWord_4866595) baseStart_4866595 baseEnd_4866595 := by
    simpa [prefixWord, tailWord_4866595, baseEnd_4866595] using wordTrace_append hprefix tailTrace_4866595
  have hstable : (prefixWord ++ tailWord_4866595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866595).length < 2 ^ (prefixWord ++ tailWord_4866595).sum := by decide
  have hdescent : baseEnd_4866595 < baseStart_4866595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866608 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 3]
def baseStart_4866608 : Nat := 118140960795 + 4866608 * 2 ^ 59
def prefixEnd_4866608 : Nat := 4983230072969 + 3 ^ 40 * 4866608 * 2
def baseEnd_4866608 : Nat := 2498909061016000607518883

theorem tailTrace_4866608 : CollatzResearch.WordTrace tailWord_4866608 prefixEnd_4866608 2498909061016000607518883 := by
  unfold tailWord_4866608
  simp only [CollatzResearch.WordTrace]
  refine ⟨88749887976558920660120239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118333183968745227546826985 88749887976558920660120239)
  ·
    refine ⟨133124831964838380990180359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88749887976558920660120239 133124831964838380990180359)
    ·
      refine ⟨199687247947257571485270539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133124831964838380990180359 199687247947257571485270539)
      ·
        refine ⟨299530871920886357227905809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199687247947257571485270539 299530871920886357227905809)
        ·
          refine ⟨224648153940664767920929357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299530871920886357227905809 224648153940664767920929357)
          ·
            refine ⟨84243057727749287970348509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224648153940664767920929357 84243057727749287970348509)
            ·
              refine ⟨31591146647905982988880691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84243057727749287970348509 31591146647905982988880691)
              ·
                refine ⟨47386719971858974483321037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31591146647905982988880691 47386719971858974483321037)
                ·
                  refine ⟨17770019989447115431245389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47386719971858974483321037 17770019989447115431245389)
                  ·
                    refine ⟨6663757496042668286717021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17770019989447115431245389 6663757496042668286717021)
                    ·
                      refine ⟨2498909061016000607518883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6663757496042668286717021 2498909061016000607518883)
                      ·
                        rfl

theorem cell23_4866608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 3].length) (baseStart_4866608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866608 prefixEnd_4866608 := by exact prefixLift 4866608
  have htrace : WordTrace (prefixWord ++ tailWord_4866608) baseStart_4866608 baseEnd_4866608 := by
    simpa [prefixWord, tailWord_4866608, baseEnd_4866608] using wordTrace_append hprefix tailTrace_4866608
  have hstable : (prefixWord ++ tailWord_4866608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866608).length < 2 ^ (prefixWord ++ tailWord_4866608).sum := by decide
  have hdescent : baseEnd_4866608 < baseStart_4866608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866635 : List Nat := [1, 1, 1, 1, 3, 1, 5, 2, 3, 3, 2]
def baseStart_4866635 : Nat := 118140960795 + 4866635 * 2 ^ 59
def prefixEnd_4866635 : Nat := 4983230072969 + 3 ^ 40 * 4866635 * 2
def baseEnd_4866635 : Nat := 2498922924993672001881259

theorem tailTrace_4866635 : CollatzResearch.WordTrace tailWord_4866635 prefixEnd_4866635 2498922924993672001881259 := by
  unfold tailWord_4866635
  simp only [CollatzResearch.WordTrace]
  refine ⟨177500760724020024931473359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118333840482680016620982239 177500760724020024931473359)
  ·
    refine ⟨266251141086030037397210039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177500760724020024931473359 266251141086030037397210039)
    ·
      refine ⟨399376711629045056095815059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266251141086030037397210039 399376711629045056095815059)
      ·
        refine ⟨599065067443567584143722589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399376711629045056095815059 599065067443567584143722589)
        ·
          refine ⟨224649400291337844053895971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 599065067443567584143722589 224649400291337844053895971)
          ·
            refine ⟨336974100437006766080843957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224649400291337844053895971 336974100437006766080843957)
            ·
              refine ⟨31591321915969384320079121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 336974100437006766080843957 31591321915969384320079121)
              ·
                refine ⟨23693491436977038240059341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31591321915969384320079121 23693491436977038240059341)
                ·
                  refine ⟨8885059288866389340022253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23693491436977038240059341 8885059288866389340022253)
                  ·
                    refine ⟨3331897233324896002508345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8885059288866389340022253 3331897233324896002508345)
                    ·
                      refine ⟨2498922924993672001881259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3331897233324896002508345 2498922924993672001881259)
                      ·
                        rfl

theorem cell23_4866635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 3, 2].length) (baseStart_4866635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866635 prefixEnd_4866635 := by exact prefixLift 4866635
  have htrace : WordTrace (prefixWord ++ tailWord_4866635) baseStart_4866635 baseEnd_4866635 := by
    simpa [prefixWord, tailWord_4866635, baseEnd_4866635] using wordTrace_append hprefix tailTrace_4866635
  have hstable : (prefixWord ++ tailWord_4866635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866635).length < 2 ^ (prefixWord ++ tailWord_4866635).sum := by decide
  have hdescent : baseEnd_4866635 < baseStart_4866635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866642 : List Nat := [3, 2, 2, 1, 2, 1, 1, 5, 2, 1, 3]
def baseStart_4866642 : Nat := 118140960795 + 4866642 * 2 ^ 59
def prefixEnd_4866642 : Nat := 4983230072969 + 3 ^ 40 * 4866642 * 2
def baseEnd_4866642 : Nat := 2498926519358253474493727

theorem tailTrace_4866642 : CollatzResearch.WordTrace tailWord_4866642 prefixEnd_4866642 2498926519358253474493727 := by
  unfold tailWord_4866642
  simp only [CollatzResearch.WordTrace]
  refine ⟨44375254008748666281744545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118334010689996443417985453 44375254008748666281744545)
  ·
    refine ⟨33281440506561499711308409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44375254008748666281744545 33281440506561499711308409)
    ·
      refine ⟨24961080379921124783481307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33281440506561499711308409 24961080379921124783481307)
      ·
        refine ⟨37441620569881687175221961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24961080379921124783481307 37441620569881687175221961)
        ·
          refine ⟨28081215427411265381416471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37441620569881687175221961 28081215427411265381416471)
          ·
            refine ⟨42121823141116898072124707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28081215427411265381416471 42121823141116898072124707)
            ·
              refine ⟨63182734711675347108187061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42121823141116898072124707 63182734711675347108187061)
              ·
                refine ⟨5923381379219563791392537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63182734711675347108187061 5923381379219563791392537)
                ·
                  refine ⟨4442536034414672843544403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5923381379219563791392537 4442536034414672843544403)
                  ·
                    refine ⟨6663804051622009265316605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4442536034414672843544403 6663804051622009265316605)
                    ·
                      refine ⟨2498926519358253474493727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6663804051622009265316605 2498926519358253474493727)
                      ·
                        rfl

theorem cell23_4866642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_4866642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866642 prefixEnd_4866642 := by exact prefixLift 4866642
  have htrace : WordTrace (prefixWord ++ tailWord_4866642) baseStart_4866642 baseEnd_4866642 := by
    simpa [prefixWord, tailWord_4866642, baseEnd_4866642] using wordTrace_append hprefix tailTrace_4866642
  have hstable : (prefixWord ++ tailWord_4866642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866642).length < 2 ^ (prefixWord ++ tailWord_4866642).sum := by decide
  have hdescent : baseEnd_4866642 < baseStart_4866642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866668 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 5]
def baseStart_4866668 : Nat := 118140960795 + 4866668 * 2 ^ 59
def prefixEnd_4866668 : Nat := 4983230072969 + 3 ^ 40 * 4866668 * 2
def baseEnd_4866668 : Nat := 2498939869855270372768607

theorem tailTrace_4866668 : CollatzResearch.WordTrace tailWord_4866668 prefixEnd_4866668 2498939869855270372768607 := by
  unfold tailWord_4866668
  simp only [CollatzResearch.WordTrace]
  refine ⟨88750982166450235783712329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118334642888600314378283105 88750982166450235783712329)
  ·
    refine ⟨66563236624837676837784247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88750982166450235783712329 66563236624837676837784247)
    ·
      refine ⟨99844854937256515256676371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66563236624837676837784247 99844854937256515256676371)
      ·
        refine ⟨149767282405884772885014557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99844854937256515256676371 149767282405884772885014557)
        ·
          refine ⟨56162730902206789831880459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149767282405884772885014557 56162730902206789831880459)
          ·
            refine ⟨84244096353310184747820689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56162730902206789831880459 84244096353310184747820689)
            ·
              refine ⟨63183072264982638560865517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84244096353310184747820689 63183072264982638560865517)
              ·
                refine ⟨23693652099368489460324569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63183072264982638560865517 23693652099368489460324569)
                ·
                  refine ⟨17770239074526367095243427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23693652099368489460324569 17770239074526367095243427)
                  ·
                    refine ⟨26655358611789550642865141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17770239074526367095243427 26655358611789550642865141)
                    ·
                      refine ⟨2498939869855270372768607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26655358611789550642865141 2498939869855270372768607)
                      ·
                        rfl

theorem cell23_4866668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 5].length) (baseStart_4866668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866668 prefixEnd_4866668 := by exact prefixLift 4866668
  have htrace : WordTrace (prefixWord ++ tailWord_4866668) baseStart_4866668 baseEnd_4866668 := by
    simpa [prefixWord, tailWord_4866668, baseEnd_4866668] using wordTrace_append hprefix tailTrace_4866668
  have hstable : (prefixWord ++ tailWord_4866668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866668).length < 2 ^ (prefixWord ++ tailWord_4866668).sum := by decide
  have hdescent : baseEnd_4866668 < baseStart_4866668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866669 : List Nat := [1, 5, 1, 1, 3, 2, 1, 3, 1, 3, 2]
def baseStart_4866669 : Nat := 118140960795 + 4866669 * 2 ^ 59
def prefixEnd_4866669 : Nat := 4983230072969 + 3 ^ 40 * 4866669 * 2
def baseEnd_4866669 : Nat := 2498940383335924868856103

theorem tailTrace_4866669 : CollatzResearch.WordTrace tailWord_4866669 prefixEnd_4866669 2498940383335924868856103 := by
  unfold tailWord_4866669
  simp only [CollatzResearch.WordTrace]
  refine ⟨177502000805896848738211061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118334667203931232492140707 177502000805896848738211061)
  ·
    refine ⟨16640812575552829569207287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 177502000805896848738211061 16640812575552829569207287)
    ·
      refine ⟨24961218863329244353810931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16640812575552829569207287 24961218863329244353810931)
      ·
        refine ⟨37441828294993866530716397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24961218863329244353810931 37441828294993866530716397)
        ·
          refine ⟨14040685610622699949018649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37441828294993866530716397 14040685610622699949018649)
          ·
            refine ⟨10530514207967024961763987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14040685610622699949018649 10530514207967024961763987)
            ·
              refine ⟨15795771311950537442645981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10530514207967024961763987 15795771311950537442645981)
              ·
                refine ⟨5923414241981451540992243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15795771311950537442645981 5923414241981451540992243)
                ·
                  refine ⟨8885121362972177311488365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5923414241981451540992243 8885121362972177311488365)
                  ·
                    refine ⟨3331920511114566491808137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8885121362972177311488365 3331920511114566491808137)
                    ·
                      refine ⟨2498940383335924868856103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3331920511114566491808137 2498940383335924868856103)
                      ·
                        rfl

theorem cell23_4866669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_4866669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866669 prefixEnd_4866669 := by exact prefixLift 4866669
  have htrace : WordTrace (prefixWord ++ tailWord_4866669) baseStart_4866669 baseEnd_4866669 := by
    simpa [prefixWord, tailWord_4866669, baseEnd_4866669] using wordTrace_append hprefix tailTrace_4866669
  have hstable : (prefixWord ++ tailWord_4866669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866669).length < 2 ^ (prefixWord ++ tailWord_4866669).sum := by decide
  have hdescent : baseEnd_4866669 < baseStart_4866669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866688 : List Nat := [2, 1, 1, 2, 1, 5, 1, 3, 7]
def baseStart_4866688 : Nat := 118140960795 + 4866688 * 2 ^ 59
def prefixEnd_4866688 : Nat := 4983230072969 + 3 ^ 40 * 4866688 * 2
def baseEnd_4866688 : Nat := 277661126607595588279835

theorem tailTrace_4866688 : CollatzResearch.WordTrace tailWord_4866688 prefixEnd_4866688 277661126607595588279835 := by
  unfold tailWord_4866688
  simp only [CollatzResearch.WordTrace]
  refine ⟨88751346896414007491576359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118335129195218676655435145 88751346896414007491576359)
  ·
    refine ⟨133127020344621011237364539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88751346896414007491576359 133127020344621011237364539)
    ·
      refine ⟨199690530516931516856046809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133127020344621011237364539 199690530516931516856046809)
      ·
        refine ⟨149767897887698637642035107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199690530516931516856046809 149767897887698637642035107)
        ·
          refine ⟨224651846831547956463052661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149767897887698637642035107 224651846831547956463052661)
          ·
            refine ⟨21061110640457620918411187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 224651846831547956463052661 21061110640457620918411187)
            ·
              refine ⟨31591665960686431377616781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21061110640457620918411187 31591665960686431377616781)
              ·
                refine ⟨11846874735257411766606293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31591665960686431377616781 11846874735257411766606293)
                ·
                  refine ⟨277661126607595588279835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11846874735257411766606293 277661126607595588279835)
                  ·
                    rfl

theorem cell23_4866688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 7].length) (baseStart_4866688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866688 prefixEnd_4866688 := by exact prefixLift 4866688
  have htrace : WordTrace (prefixWord ++ tailWord_4866688) baseStart_4866688 baseEnd_4866688 := by
    simpa [prefixWord, tailWord_4866688, baseEnd_4866688] using wordTrace_append hprefix tailTrace_4866688
  have hstable : (prefixWord ++ tailWord_4866688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866688).length < 2 ^ (prefixWord ++ tailWord_4866688).sum := by decide
  have hdescent : baseEnd_4866688 < baseStart_4866688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866725 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 1, 7, 2]
def baseStart_4866725 : Nat := 118140960795 + 4866725 * 2 ^ 59
def prefixEnd_4866725 : Nat := 4983230072969 + 3 ^ 40 * 4866725 * 2
def baseEnd_4866725 : Nat := 2498969138252576649755845

theorem tailTrace_4866725 : CollatzResearch.WordTrace tailWord_4866725 prefixEnd_4866725 2498969138252576649755845 := by
  unfold tailWord_4866725
  simp only [CollatzResearch.WordTrace]
  refine ⟨177504043293693970302249629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118336028862462646868166419 177504043293693970302249629)
  ·
    refine ⟨66564016235135238863343611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177504043293693970302249629 66564016235135238863343611)
    ·
      refine ⟨99846024352702858295015417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66564016235135238863343611 99846024352702858295015417)
      ·
        refine ⟨74884518264527143721261563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99846024352702858295015417 74884518264527143721261563)
        ·
          refine ⟨112326777396790715581892345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74884518264527143721261563 112326777396790715581892345)
          ·
            refine ⟨84245083047593036686419259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112326777396790715581892345 84245083047593036686419259)
            ·
              refine ⟨126367624571389555029628889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84245083047593036686419259 126367624571389555029628889)
              ·
                refine ⟨94775718428542166272221667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126367624571389555029628889 94775718428542166272221667)
                ·
                  refine ⟨142163577642813249408332501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94775718428542166272221667 142163577642813249408332501)
                  ·
                    refine ⟨3331958851003435533007793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 142163577642813249408332501 3331958851003435533007793)
                    ·
                      refine ⟨2498969138252576649755845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3331958851003435533007793 2498969138252576649755845)
                      ·
                        rfl

theorem cell23_4866725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_4866725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866725 prefixEnd_4866725 := by exact prefixLift 4866725
  have htrace : WordTrace (prefixWord ++ tailWord_4866725) baseStart_4866725 baseEnd_4866725 := by
    simpa [prefixWord, tailWord_4866725, baseEnd_4866725] using wordTrace_append hprefix tailTrace_4866725
  have hstable : (prefixWord ++ tailWord_4866725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866725).length < 2 ^ (prefixWord ++ tailWord_4866725).sum := by decide
  have hdescent : baseEnd_4866725 < baseStart_4866725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866735 : List Nat := [1, 1, 2, 1, 2, 6, 1, 2, 2, 5]
def baseStart_4866735 : Nat := 118140960795 + 4866735 * 2 ^ 59
def prefixEnd_4866735 : Nat := 4983230072969 + 3 ^ 40 * 4866735 * 2
def baseEnd_4866735 : Nat := 832991424353040536876933

theorem tailTrace_4866735 : CollatzResearch.WordTrace tailWord_4866735 prefixEnd_4866735 832991424353040536876933 := by
  unfold tailWord_4866735
  simp only [CollatzResearch.WordTrace]
  refine ⟨177504408023657742010113659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118336272015771828006742439 177504408023657742010113659)
  ·
    refine ⟨266256612035486613015170489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177504408023657742010113659 266256612035486613015170489)
    ·
      refine ⟨199692459026614959761377867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266256612035486613015170489 199692459026614959761377867)
      ·
        refine ⟨299538688539922439642066801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199692459026614959761377867 299538688539922439642066801)
        ·
          refine ⟨224654016404941829731550101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299538688539922439642066801 224654016404941829731550101)
          ·
            refine ⟨10530657018981648268666411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 224654016404941829731550101 10530657018981648268666411)
            ·
              refine ⟨15795985528472472402999617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10530657018981648268666411 15795985528472472402999617)
              ·
                refine ⟨11846989146354354302249713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15795985528472472402999617 11846989146354354302249713)
                ·
                  refine ⟨8885241859765765726687285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11846989146354354302249713 8885241859765765726687285)
                  ·
                    refine ⟨832991424353040536876933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8885241859765765726687285 832991424353040536876933)
                    ·
                      rfl

theorem cell23_4866735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 2, 5].length) (baseStart_4866735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866735 prefixEnd_4866735 := by exact prefixLift 4866735
  have htrace : WordTrace (prefixWord ++ tailWord_4866735) baseStart_4866735 baseEnd_4866735 := by
    simpa [prefixWord, tailWord_4866735, baseEnd_4866735] using wordTrace_append hprefix tailTrace_4866735
  have hstable : (prefixWord ++ tailWord_4866735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866735).length < 2 ^ (prefixWord ++ tailWord_4866735).sum := by decide
  have hdescent : baseEnd_4866735 < baseStart_4866735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866799 : List Nat := [1, 1, 2, 1, 5, 3, 1, 4, 1, 4]
def baseStart_4866799 : Nat := 118140960795 + 4866799 * 2 ^ 59
def prefixEnd_4866799 : Nat := 4983230072969 + 3 ^ 40 * 4866799 * 2
def baseEnd_4866799 : Nat := 833002378607003120076835

theorem tailTrace_4866799 : CollatzResearch.WordTrace tailWord_4866799 prefixEnd_4866799 833002378607003120076835 := by
  unfold tailWord_4866799
  simp only [CollatzResearch.WordTrace]
  refine ⟨177506742295425880940443451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118337828196950587293628967 177506742295425880940443451)
  ·
    refine ⟨266260113443138821410665177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177506742295425880940443451 266260113443138821410665177)
    ·
      refine ⟨199695085082354116057998883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266260113443138821410665177 199695085082354116057998883)
      ·
        refine ⟨299542627623531174086998325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199695085082354116057998883 299542627623531174086998325)
        ·
          refine ⟨28082121339706047570656093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 299542627623531174086998325 28082121339706047570656093)
          ·
            refine ⟨10530795502389767838996035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28082121339706047570656093 10530795502389767838996035)
            ·
              refine ⟨15796193253584651758494053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10530795502389767838996035 15796193253584651758494053)
              ·
                refine ⟨2961786235047122204717635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15796193253584651758494053 2961786235047122204717635)
                ·
                  refine ⟨4442679352570683307076453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2961786235047122204717635 4442679352570683307076453)
                  ·
                    refine ⟨833002378607003120076835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4442679352570683307076453 833002378607003120076835)
                    ·
                      rfl

theorem cell23_4866799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4, 1, 4].length) (baseStart_4866799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866799 prefixEnd_4866799 := by exact prefixLift 4866799
  have htrace : WordTrace (prefixWord ++ tailWord_4866799) baseStart_4866799 baseEnd_4866799 := by
    simpa [prefixWord, tailWord_4866799, baseEnd_4866799] using wordTrace_append hprefix tailTrace_4866799
  have hstable : (prefixWord ++ tailWord_4866799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866799).length < 2 ^ (prefixWord ++ tailWord_4866799).sum := by decide
  have hdescent : baseEnd_4866799 < baseStart_4866799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866825 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 3, 5]
def baseStart_4866825 : Nat := 118140960795 + 4866825 * 2 ^ 59
def prefixEnd_4866825 : Nat := 4983230072969 + 3 ^ 40 * 4866825 * 2
def baseEnd_4866825 : Nat := 833006828772675419501795

theorem tailTrace_4866825 : CollatzResearch.WordTrace tailWord_4866825 prefixEnd_4866825 833006828772675419501795 := by
  unfold tailWord_4866825
  simp only [CollatzResearch.WordTrace]
  refine ⟨177507690593331687380889929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118338460395554458253926619 177507690593331687380889929)
  ·
    refine ⟨133130767944998765535667447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177507690593331687380889929 133130767944998765535667447)
    ·
      refine ⟨199696151917498148303501171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133130767944998765535667447 199696151917498148303501171)
      ·
        refine ⟨299544227876247222455251757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199696151917498148303501171 299544227876247222455251757)
        ·
          refine ⟨112329085453592708420719409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 299544227876247222455251757 112329085453592708420719409)
          ·
            refine ⟨84246814090194531315539557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112329085453592708420719409 84246814090194531315539557)
            ·
              refine ⟨15796277641911474621663667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84246814090194531315539557 15796277641911474621663667)
              ·
                refine ⟨23694416462867211932495501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15796277641911474621663667 23694416462867211932495501)
                ·
                  refine ⟨8885406173575204474685813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23694416462867211932495501 8885406173575204474685813)
                  ·
                    refine ⟨833006828772675419501795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8885406173575204474685813 833006828772675419501795)
                    ·
                      rfl

theorem cell23_4866825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 3, 5].length) (baseStart_4866825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866825 prefixEnd_4866825 := by exact prefixLift 4866825
  have htrace : WordTrace (prefixWord ++ tailWord_4866825) baseStart_4866825 baseEnd_4866825 := by
    simpa [prefixWord, tailWord_4866825, baseEnd_4866825] using wordTrace_append hprefix tailTrace_4866825
  have hstable : (prefixWord ++ tailWord_4866825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866825).length < 2 ^ (prefixWord ++ tailWord_4866825).sum := by decide
  have hdescent : baseEnd_4866825 < baseStart_4866825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866842 : List Nat := [3, 1, 1, 3, 2, 1, 3, 3, 1, 5]
def baseStart_4866842 : Nat := 118140960795 + 4866842 * 2 ^ 59
def prefixEnd_4866842 : Nat := 4983230072969 + 3 ^ 40 * 4866842 * 2
def baseEnd_4866842 : Nat := 833009738496384230664269

theorem tailTrace_4866842 : CollatzResearch.WordTrace tailWord_4866842 prefixEnd_4866842 833009738496384230664269 := by
  unfold tailWord_4866842
  simp only [CollatzResearch.WordTrace]
  refine ⟨44377077658567524821064695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118338873756180066189505853 44377077658567524821064695)
  ·
    refine ⟨66565616487851287231597043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44377077658567524821064695 66565616487851287231597043)
    ·
      refine ⟨99848424731776930847395565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66565616487851287231597043 99848424731776930847395565)
      ·
        refine ⟨37443159274416349067773337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99848424731776930847395565 37443159274416349067773337)
        ·
          refine ⟨28082369455812261800830003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37443159274416349067773337 28082369455812261800830003)
          ·
            refine ⟨42123554183718392701245005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28082369455812261800830003 42123554183718392701245005)
            ·
              refine ⟨15796332818894397262966877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42123554183718392701245005 15796332818894397262966877)
              ·
                refine ⟨5923624807085398973612579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15796332818894397262966877 5923624807085398973612579)
                ·
                  refine ⟨8885437210628098460418869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5923624807085398973612579 8885437210628098460418869)
                  ·
                    refine ⟨833009738496384230664269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8885437210628098460418869 833009738496384230664269)
                    ·
                      rfl

theorem cell23_4866842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 1, 5].length) (baseStart_4866842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866842 prefixEnd_4866842 := by exact prefixLift 4866842
  have htrace : WordTrace (prefixWord ++ tailWord_4866842) baseStart_4866842 baseEnd_4866842 := by
    simpa [prefixWord, tailWord_4866842, baseEnd_4866842] using wordTrace_append hprefix tailTrace_4866842
  have hstable : (prefixWord ++ tailWord_4866842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866842).length < 2 ^ (prefixWord ++ tailWord_4866842).sum := by decide
  have hdescent : baseEnd_4866842 < baseStart_4866842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866856 : List Nat := [2, 1, 5, 1, 1, 1, 1, 6, 1, 1, 3]
def baseStart_4866856 : Nat := 118140960795 + 4866856 * 2 ^ 59
def prefixEnd_4866856 : Nat := 4983230072969 + 3 ^ 40 * 4866856 * 2
def baseEnd_4866856 : Nat := 2499036404218315637217743

theorem tailTrace_4866856 : CollatzResearch.WordTrace tailWord_4866856 prefixEnd_4866856 2499036404218315637217743 := by
  unfold tailWord_4866856
  simp only [CollatzResearch.WordTrace]
  refine ⟨88754410628109689837634211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118339214170812919783512281 88754410628109689837634211)
  ·
    refine ⟨133131615942164534756451317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88754410628109689837634211 133131615942164534756451317)
    ·
      refine ⟨12481088994577925133417311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133131615942164534756451317 12481088994577925133417311)
      ·
        refine ⟨18721633491866887700125967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12481088994577925133417311 18721633491866887700125967)
        ·
          refine ⟨28082450237800331550188951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18721633491866887700125967 28082450237800331550188951)
          ·
            refine ⟨42123675356700497325283427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28082450237800331550188951 42123675356700497325283427)
            ·
              refine ⟨63185513035050745987925141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42123675356700497325283427 63185513035050745987925141)
              ·
                refine ⟨2961820923518003718183991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63185513035050745987925141 2961820923518003718183991)
                ·
                  refine ⟨4442731385277005577275987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2961820923518003718183991 4442731385277005577275987)
                  ·
                    refine ⟨6664097077915508365913981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4442731385277005577275987 6664097077915508365913981)
                    ·
                      refine ⟨2499036404218315637217743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6664097077915508365913981 2499036404218315637217743)
                      ·
                        rfl

theorem cell23_4866856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_4866856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866856 prefixEnd_4866856 := by exact prefixLift 4866856
  have htrace : WordTrace (prefixWord ++ tailWord_4866856) baseStart_4866856 baseEnd_4866856 := by
    simpa [prefixWord, tailWord_4866856, baseEnd_4866856] using wordTrace_append hprefix tailTrace_4866856
  have hstable : (prefixWord ++ tailWord_4866856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866856).length < 2 ^ (prefixWord ++ tailWord_4866856).sum := by decide
  have hdescent : baseEnd_4866856 < baseStart_4866856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866879 : List Nat := [1, 1, 2, 2, 5, 2, 2, 2, 1, 1, 4]
def baseStart_4866879 : Nat := 118140960795 + 4866879 * 2 ^ 59
def prefixEnd_4866879 : Nat := 4983230072969 + 3 ^ 40 * 4866879 * 2
def baseEnd_4866879 : Nat := 2499048214273369047230137

theorem tailTrace_4866879 : CollatzResearch.WordTrace tailWord_4866879 prefixEnd_4866879 2499048214273369047230137 := by
  unfold tailWord_4866879
  simp only [CollatzResearch.WordTrace]
  refine ⟨177509660135136054603355691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118339773423424036402237127 177509660135136054603355691)
  ·
    refine ⟨266264490202704081905033537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177509660135136054603355691 266264490202704081905033537)
    ·
      refine ⟨199698367652028061428775153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266264490202704081905033537 199698367652028061428775153)
      ·
        refine ⟨149773775739021046071581365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199698367652028061428775153 149773775739021046071581365)
        ·
          refine ⟨14041291475533223069210753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 149773775739021046071581365 14041291475533223069210753)
          ·
            refine ⟨10530968606649917301908065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14041291475533223069210753 10530968606649917301908065)
            ·
              refine ⟨7898226454987437976431049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10530968606649917301908065 7898226454987437976431049)
              ·
                refine ⟨5923669841240578482323287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7898226454987437976431049 5923669841240578482323287)
                ·
                  refine ⟨8885504761860867723484931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5923669841240578482323287 8885504761860867723484931)
                  ·
                    refine ⟨13328257142791301585227397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8885504761860867723484931 13328257142791301585227397)
                    ·
                      refine ⟨2499048214273369047230137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13328257142791301585227397 2499048214273369047230137)
                      ·
                        rfl

theorem cell23_4866879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 1, 4].length) (baseStart_4866879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866879 prefixEnd_4866879 := by exact prefixLift 4866879
  have htrace : WordTrace (prefixWord ++ tailWord_4866879) baseStart_4866879 baseEnd_4866879 := by
    simpa [prefixWord, tailWord_4866879, baseEnd_4866879] using wordTrace_append hprefix tailTrace_4866879
  have hstable : (prefixWord ++ tailWord_4866879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866879).length < 2 ^ (prefixWord ++ tailWord_4866879).sum := by decide
  have hdescent : baseEnd_4866879 < baseStart_4866879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4866966 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_4866966 : Nat := 118140960795 + 4866966 * 2 ^ 59
def prefixEnd_4866966 : Nat := 4983230072969 + 3 ^ 40 * 4866966 * 2
def baseEnd_4866966 : Nat := 833030962363436735614079

theorem tailTrace_4866966 : CollatzResearch.WordTrace tailWord_4866966 prefixEnd_4866966 833030962363436735614079 := by
  unfold tailWord_4866966
  simp only [CollatzResearch.WordTrace]
  refine ⟨11094552080363804278860797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118341888857213912307848501 11094552080363804278860797)
  ·
    refine ⟨4160457030136426604572799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11094552080363804278860797 4160457030136426604572799)
    ·
      refine ⟨6240685545204639906859199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4160457030136426604572799 6240685545204639906859199)
      ·
        refine ⟨9361028317806959860288799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6240685545204639906859199 9361028317806959860288799)
        ·
          refine ⟨14041542476710439790433199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9361028317806959860288799 14041542476710439790433199)
          ·
            refine ⟨21062313715065659685649799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14041542476710439790433199 21062313715065659685649799)
            ·
              refine ⟨31593470572598489528474699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21062313715065659685649799 31593470572598489528474699)
              ·
                refine ⟨47390205858897734292712049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31593470572598489528474699 47390205858897734292712049)
                ·
                  refine ⟨35542654394173300719534037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47390205858897734292712049 35542654394173300719534037)
                  ·
                    refine ⟨833030962363436735614079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35542654394173300719534037 833030962363436735614079)
                    ·
                      rfl

theorem cell23_4866966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_4866966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4866966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4866966 prefixEnd_4866966 := by exact prefixLift 4866966
  have htrace : WordTrace (prefixWord ++ tailWord_4866966) baseStart_4866966 baseEnd_4866966 := by
    simpa [prefixWord, tailWord_4866966, baseEnd_4866966] using wordTrace_append hprefix tailTrace_4866966
  have hstable : (prefixWord ++ tailWord_4866966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4866966).length < 2 ^ (prefixWord ++ tailWord_4866966).sum := by decide
  have hdescent : baseEnd_4866966 < baseStart_4866966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4866966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867002 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3]
def baseStart_4867002 : Nat := 118140960795 + 4867002 * 2 ^ 59
def prefixEnd_4867002 : Nat := 4983230072969 + 3 ^ 40 * 4867002 * 2
def baseEnd_4867002 : Nat := 2499111372393872065992071

theorem tailTrace_4867002 : CollatzResearch.WordTrace tailWord_4867002 prefixEnd_4867002 2499111372393872065992071 := by
  unfold tailWord_4867002
  simp only [CollatzResearch.WordTrace]
  refine ⟨44378536578422611652520815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118342764209126964406722173 44378536578422611652520815)
  ·
    refine ⟨66567804867633917478781223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44378536578422611652520815 66567804867633917478781223)
    ·
      refine ⟨99851707301450876218171835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66567804867633917478781223 99851707301450876218171835)
      ·
        refine ⟨149777560952176314327257753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99851707301450876218171835 149777560952176314327257753)
        ·
          refine ⟨112333170714132235745443315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149777560952176314327257753 112333170714132235745443315)
          ·
            refine ⟨168499756071198353618164973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112333170714132235745443315 168499756071198353618164973)
            ·
              refine ⟨63187408526699382606811865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168499756071198353618164973 63187408526699382606811865)
              ·
                refine ⟨47390556395024536955108899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63187408526699382606811865 47390556395024536955108899)
                ·
                  refine ⟨71085834592536805432663349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47390556395024536955108899 71085834592536805432663349)
                  ·
                    refine ⟨6664296993050325509312189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71085834592536805432663349 6664296993050325509312189)
                    ·
                      refine ⟨2499111372393872065992071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6664296993050325509312189 2499111372393872065992071)
                      ·
                        rfl

theorem cell23_4867002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_4867002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867002 prefixEnd_4867002 := by exact prefixLift 4867002
  have htrace : WordTrace (prefixWord ++ tailWord_4867002) baseStart_4867002 baseEnd_4867002 := by
    simpa [prefixWord, tailWord_4867002, baseEnd_4867002] using wordTrace_append hprefix tailTrace_4867002
  have hstable : (prefixWord ++ tailWord_4867002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867002).length < 2 ^ (prefixWord ++ tailWord_4867002).sum := by decide
  have hdescent : baseEnd_4867002 < baseStart_4867002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867026 : List Nat := [3, 2, 2, 3, 1, 1, 2, 4, 5]
def baseStart_4867026 : Nat := 118140960795 + 4867026 * 2 ^ 59
def prefixEnd_4867026 : Nat := 4983230072969 + 3 ^ 40 * 4867026 * 2
def baseEnd_4867026 : Nat := 277680410658842219121329

theorem tailTrace_4867026 : CollatzResearch.WordTrace tailWord_4867026 prefixEnd_4867026 277680410658842219121329 := by
  unfold tailWord_4867026
  simp only [CollatzResearch.WordTrace]
  refine ⟨44378755416400874677239233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118343347777068999139304621 44378755416400874677239233)
  ·
    refine ⟨33284066562300656007929425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44378755416400874677239233 33284066562300656007929425)
    ·
      refine ⟨24963049921725492005947069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33284066562300656007929425 24963049921725492005947069)
      ·
        refine ⟨9361143720647059502230151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24963049921725492005947069 9361143720647059502230151)
        ·
          refine ⟨14041715580970589253345227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9361143720647059502230151 14041715580970589253345227)
          ·
            refine ⟨21062573371455883880017841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14041715580970589253345227 21062573371455883880017841)
            ·
              refine ⟨15796930028591912910013381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21062573371455883880017841 15796930028591912910013381)
              ·
                refine ⟨2961924380360983670627509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15796930028591912910013381 2961924380360983670627509)
                ·
                  refine ⟨277680410658842219121329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2961924380360983670627509 277680410658842219121329)
                  ·
                    rfl

theorem cell23_4867026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_4867026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867026 prefixEnd_4867026 := by exact prefixLift 4867026
  have htrace : WordTrace (prefixWord ++ tailWord_4867026) baseStart_4867026 baseEnd_4867026 := by
    simpa [prefixWord, tailWord_4867026, baseEnd_4867026] using wordTrace_append hprefix tailTrace_4867026
  have hstable : (prefixWord ++ tailWord_4867026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867026).length < 2 ^ (prefixWord ++ tailWord_4867026).sum := by decide
  have hdescent : baseEnd_4867026 < baseStart_4867026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867086 : List Nat := [4, 1, 1, 2, 2, 2, 3, 1, 3, 4]
def baseStart_4867086 : Nat := 118140960795 + 4867086 * 2 ^ 59
def prefixEnd_4867086 : Nat := 4983230072969 + 3 ^ 40 * 4867086 * 2
def baseEnd_4867086 : Nat := 833051501589616579113895

theorem tailTrace_4867086 : CollatzResearch.WordTrace tailWord_4867086 prefixEnd_4867086 833051501589616579113895 := by
  unfold tailWord_4867086
  simp only [CollatzResearch.WordTrace]
  refine ⟨22189651255673266119517639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118344806696924085970760741 22189651255673266119517639)
  ·
    refine ⟨33284476883509899179276459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22189651255673266119517639 33284476883509899179276459)
    ·
      refine ⟨49926715325264848768914689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33284476883509899179276459 49926715325264848768914689)
      ·
        refine ⟨37445036493948636576686017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49926715325264848768914689 37445036493948636576686017)
        ·
          refine ⟨28083777370461477432514513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37445036493948636576686017 28083777370461477432514513)
          ·
            refine ⟨21062833027846108074385885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28083777370461477432514513 21062833027846108074385885)
            ·
              refine ⟨7898562385442290527894707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21062833027846108074385885 7898562385442290527894707)
              ·
                refine ⟨11847843578163435791842061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7898562385442290527894707 11847843578163435791842061)
                ·
                  refine ⟨4442941341811288421940773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11847843578163435791842061 4442941341811288421940773)
                  ·
                    refine ⟨833051501589616579113895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4442941341811288421940773 833051501589616579113895)
                    ·
                      rfl

theorem cell23_4867086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_4867086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867086 prefixEnd_4867086 := by exact prefixLift 4867086
  have htrace : WordTrace (prefixWord ++ tailWord_4867086) baseStart_4867086 baseEnd_4867086 := by
    simpa [prefixWord, tailWord_4867086, baseEnd_4867086] using wordTrace_append hprefix tailTrace_4867086
  have hstable : (prefixWord ++ tailWord_4867086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867086).length < 2 ^ (prefixWord ++ tailWord_4867086).sum := by decide
  have hdescent : baseEnd_4867086 < baseStart_4867086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867119 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 5, 5, 2]
def baseStart_4867119 : Nat := 118140960795 + 4867119 * 2 ^ 59
def prefixEnd_4867119 : Nat := 4983230072969 + 3 ^ 40 * 4867119 * 2
def baseEnd_4867119 : Nat := 2499171449630448108229033

theorem tailTrace_4867119 : CollatzResearch.WordTrace tailWord_4867119 prefixEnd_4867119 2499171449630448108229033 := by
  unfold tailWord_4867119
  simp only [CollatzResearch.WordTrace]
  refine ⟨177518413654266575592092411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118345609102844383728061607 177518413654266575592092411)
  ·
    refine ⟨266277620481399863388138617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177518413654266575592092411 266277620481399863388138617)
    ·
      refine ⟨199708215361049897541103963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266277620481399863388138617 199708215361049897541103963)
      ·
        refine ⟨299562323041574846311655945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199708215361049897541103963 299562323041574846311655945)
        ·
          refine ⟨224671742281181134733741959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299562323041574846311655945 224671742281181134733741959)
          ·
            refine ⟨337007613421771702100612939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224671742281181134733741959 337007613421771702100612939)
            ·
              refine ⟨505511420132657553150919409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337007613421771702100612939 505511420132657553150919409)
              ·
                refine ⟨379133565099493164863189557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 505511420132657553150919409 379133565099493164863189557)
                ·
                  refine ⟨35543771728077484205924021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 379133565099493164863189557 35543771728077484205924021)
                  ·
                    refine ⟨3332228599507264144305377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35543771728077484205924021 3332228599507264144305377)
                    ·
                      refine ⟨2499171449630448108229033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3332228599507264144305377 2499171449630448108229033)
                      ·
                        rfl

theorem cell23_4867119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 5, 2].length) (baseStart_4867119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867119 prefixEnd_4867119 := by exact prefixLift 4867119
  have htrace : WordTrace (prefixWord ++ tailWord_4867119) baseStart_4867119 baseEnd_4867119 := by
    simpa [prefixWord, tailWord_4867119, baseEnd_4867119] using wordTrace_append hprefix tailTrace_4867119
  have hstable : (prefixWord ++ tailWord_4867119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867119).length < 2 ^ (prefixWord ++ tailWord_4867119).sum := by decide
  have hdescent : baseEnd_4867119 < baseStart_4867119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867136 : List Nat := [2, 1, 1, 2, 2, 3, 1, 4, 2, 3, 2]
def baseStart_4867136 : Nat := 118140960795 + 4867136 * 2 ^ 59
def prefixEnd_4867136 : Nat := 4983230072969 + 3 ^ 40 * 4867136 * 2
def baseEnd_4867136 : Nat := 2499180178801574541716455

theorem tailTrace_4867136 : CollatzResearch.WordTrace tailWord_4867136 prefixEnd_4867136 2499180178801574541716455 := by
  unfold tailWord_4867136
  simp only [CollatzResearch.WordTrace]
  refine ⟨88759516847602493747730631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118346022463469991663640841 88759516847602493747730631)
  ·
    refine ⟨133139275271403740621595947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88759516847602493747730631 133139275271403740621595947)
    ·
      refine ⟨199708912907105610932393921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133139275271403740621595947 199708912907105610932393921)
      ·
        refine ⟨149781684680329208199295441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199708912907105610932393921 149781684680329208199295441)
        ·
          refine ⟨112336263510246906149471581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149781684680329208199295441 112336263510246906149471581)
          ·
            refine ⟨42126098816342589806051843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112336263510246906149471581 42126098816342589806051843)
            ·
              refine ⟨63189148224513884709077765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42126098816342589806051843 63189148224513884709077765)
              ·
                refine ⟨11847965292096353382952081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63189148224513884709077765 11847965292096353382952081)
                ·
                  refine ⟨8885973969072265037214061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11847965292096353382952081 8885973969072265037214061)
                  ·
                    refine ⟨3332240238402099388955273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8885973969072265037214061 3332240238402099388955273)
                    ·
                      refine ⟨2499180178801574541716455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3332240238402099388955273 2499180178801574541716455)
                      ·
                        rfl

theorem cell23_4867136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 4, 2, 3, 2].length) (baseStart_4867136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867136 prefixEnd_4867136 := by exact prefixLift 4867136
  have htrace : WordTrace (prefixWord ++ tailWord_4867136) baseStart_4867136 baseEnd_4867136 := by
    simpa [prefixWord, tailWord_4867136, baseEnd_4867136] using wordTrace_append hprefix tailTrace_4867136
  have hstable : (prefixWord ++ tailWord_4867136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867136).length < 2 ^ (prefixWord ++ tailWord_4867136).sum := by decide
  have hdescent : baseEnd_4867136 < baseStart_4867136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867137 : List Nat := [1, 2, 5, 1, 3, 2, 2, 2, 1, 4]
def baseStart_4867137 : Nat := 118140960795 + 4867137 * 2 ^ 59
def prefixEnd_4867137 : Nat := 4983230072969 + 3 ^ 40 * 4867137 * 2
def baseEnd_4867137 : Nat := 833060230760743012601317

theorem tailTrace_4867137 : CollatzResearch.WordTrace tailWord_4867137 prefixEnd_4867137 833060230760743012601317 := by
  unfold tailWord_4867137
  simp only [CollatzResearch.WordTrace]
  refine ⟨177519070168201364666247665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118346046778800909777498443 177519070168201364666247665)
  ·
    refine ⟨133139302626151023499685749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177519070168201364666247665 133139302626151023499685749)
    ·
      refine ⟨12481809621201658453095539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133139302626151023499685749 12481809621201658453095539)
      ·
        refine ⟨18722714431802487679643309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12481809621201658453095539 18722714431802487679643309)
        ·
          refine ⟨7021017911925932879866241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18722714431802487679643309 7021017911925932879866241)
          ·
            refine ⟨5265763433944449659899681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7021017911925932879866241 5265763433944449659899681)
            ·
              refine ⟨3949322575458337244924761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5265763433944449659899681 3949322575458337244924761)
              ·
                refine ⟨2961991931593752933693571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3949322575458337244924761 2961991931593752933693571)
                ·
                  refine ⟨4442987897390629400540357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2961991931593752933693571 4442987897390629400540357)
                  ·
                    refine ⟨833060230760743012601317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4442987897390629400540357 833060230760743012601317)
                    ·
                      rfl

theorem cell23_4867137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_4867137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867137 prefixEnd_4867137 := by exact prefixLift 4867137
  have htrace : WordTrace (prefixWord ++ tailWord_4867137) baseStart_4867137 baseEnd_4867137 := by
    simpa [prefixWord, tailWord_4867137, baseEnd_4867137] using wordTrace_append hprefix tailTrace_4867137
  have hstable : (prefixWord ++ tailWord_4867137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867137).length < 2 ^ (prefixWord ++ tailWord_4867137).sum := by decide
  have hdescent : baseEnd_4867137 < baseStart_4867137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867159 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 6, 4]
def baseStart_4867159 : Nat := 118140960795 + 4867159 * 2 ^ 59
def prefixEnd_4867159 : Nat := 4983230072969 + 3 ^ 40 * 4867159 * 2
def baseEnd_4867159 : Nat := 833063996285542650576283

theorem tailTrace_4867159 : CollatzResearch.WordTrace tailWord_4867159 prefixEnd_4867159 833063996285542650576283 := by
  unfold tailWord_4867159
  simp only [CollatzResearch.WordTrace]
  refine ⟨177519872574121662423548531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118346581716081108282365687 177519872574121662423548531)
  ·
    refine ⟨266279808861182493635322797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177519872574121662423548531 266279808861182493635322797)
    ·
      refine ⟨99854928322943435113246049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266279808861182493635322797 99854928322943435113246049)
      ·
        refine ⟨74891196242207576334934537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99854928322943435113246049 74891196242207576334934537)
        ·
          refine ⟨56168397181655682251200903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74891196242207576334934537 56168397181655682251200903)
          ·
            refine ⟨84252595772483523376801355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56168397181655682251200903 84252595772483523376801355)
            ·
              refine ⟨126378893658725285065202033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84252595772483523376801355 126378893658725285065202033)
              ·
                refine ⟨94784170244043963798901525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126378893658725285065202033 94784170244043963798901525)
                ·
                  refine ⟨4443007980189560803073509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94784170244043963798901525 4443007980189560803073509)
                  ·
                    refine ⟨833063996285542650576283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4443007980189560803073509 833063996285542650576283)
                    ·
                      rfl

theorem cell23_4867159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_4867159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867159 prefixEnd_4867159 := by exact prefixLift 4867159
  have htrace : WordTrace (prefixWord ++ tailWord_4867159) baseStart_4867159 baseEnd_4867159 := by
    simpa [prefixWord, tailWord_4867159, baseEnd_4867159] using wordTrace_append hprefix tailTrace_4867159
  have hstable : (prefixWord ++ tailWord_4867159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867159).length < 2 ^ (prefixWord ++ tailWord_4867159).sum := by decide
  have hdescent : baseEnd_4867159 < baseStart_4867159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867170 : List Nat := [3, 3, 2, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_4867170 : Nat := 118140960795 + 4867170 * 2 ^ 59
def prefixEnd_4867170 : Nat := 4983230072969 + 3 ^ 40 * 4867170 * 2
def baseEnd_4867170 : Nat := 2499197637143827408691299

theorem tailTrace_4867170 : CollatzResearch.WordTrace tailWord_4867170 prefixEnd_4867170 2499197637143827408691299 := by
  unfold tailWord_4867170
  simp only [CollatzResearch.WordTrace]
  refine ⟨44380068444270452825549741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118346849184721207534799309 44380068444270452825549741)
  ·
    refine ⟨16642525666601419809581153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44380068444270452825549741 16642525666601419809581153)
    ·
      refine ⟨12481894249951064857185865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16642525666601419809581153 12481894249951064857185865)
      ·
        refine ⟨9361420687463298642889399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12481894249951064857185865 9361420687463298642889399)
        ·
          refine ⟨14042131031194947964334099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9361420687463298642889399 14042131031194947964334099)
          ·
            refine ⟨21063196546792421946501149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14042131031194947964334099 21063196546792421946501149)
            ·
              refine ⟨7898698705047158229937931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21063196546792421946501149 7898698705047158229937931)
              ·
                refine ⟨11848048057570737344906897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7898698705047158229937931 11848048057570737344906897)
                ·
                  refine ⟨8886036043178053008680173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11848048057570737344906897 8886036043178053008680173)
                  ·
                    refine ⟨3332263516191769878255065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8886036043178053008680173 3332263516191769878255065)
                    ·
                      refine ⟨2499197637143827408691299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3332263516191769878255065 2499197637143827408691299)
                      ·
                        rfl

theorem cell23_4867170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_4867170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867170 prefixEnd_4867170 := by exact prefixLift 4867170
  have htrace : WordTrace (prefixWord ++ tailWord_4867170) baseStart_4867170 baseEnd_4867170 := by
    simpa [prefixWord, tailWord_4867170, baseEnd_4867170] using wordTrace_append hprefix tailTrace_4867170
  have hstable : (prefixWord ++ tailWord_4867170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867170).length < 2 ^ (prefixWord ++ tailWord_4867170).sum := by decide
  have hdescent : baseEnd_4867170 < baseStart_4867170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867200 : List Nat := [2, 1, 1, 2, 1, 3, 4, 4, 1, 2, 2]
def baseStart_4867200 : Nat := 118140960795 + 4867200 * 2 ^ 59
def prefixEnd_4867200 : Nat := 4983230072969 + 3 ^ 40 * 4867200 * 2
def baseEnd_4867200 : Nat := 2499213041563462291316161

theorem tailTrace_4867200 : CollatzResearch.WordTrace tailWord_4867200 prefixEnd_4867200 2499213041563462291316161 := by
  unfold tailWord_4867200
  simp only [CollatzResearch.WordTrace]
  refine ⟨88760683983486563212895527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118347578644648750950527369 88760683983486563212895527)
  ·
    refine ⟨133141025975229844819343291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88760683983486563212895527 133141025975229844819343291)
    ·
      refine ⟨199711538962844767229014937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133141025975229844819343291 199711538962844767229014937)
      ·
        refine ⟨149783654222133575421761203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199711538962844767229014937 149783654222133575421761203)
        ·
          refine ⟨224675481333200363132641805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149783654222133575421761203 224675481333200363132641805)
          ·
            refine ⟨84253305499950136174740677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224675481333200363132641805 84253305499950136174740677)
            ·
              refine ⟨15797494781240650532763877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84253305499950136174740677 15797494781240650532763877)
              ·
                refine ⟨2962030271482621974893227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15797494781240650532763877 2962030271482621974893227)
                ·
                  refine ⟨4443045407223932962339841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2962030271482621974893227 4443045407223932962339841)
                  ·
                    refine ⟨3332284055417949721754881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4443045407223932962339841 3332284055417949721754881)
                    ·
                      refine ⟨2499213041563462291316161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3332284055417949721754881 2499213041563462291316161)
                      ·
                        rfl

theorem cell23_4867200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 4, 1, 2, 2].length) (baseStart_4867200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867200 prefixEnd_4867200 := by exact prefixLift 4867200
  have htrace : WordTrace (prefixWord ++ tailWord_4867200) baseStart_4867200 baseEnd_4867200 := by
    simpa [prefixWord, tailWord_4867200, baseEnd_4867200] using wordTrace_append hprefix tailTrace_4867200
  have hstable : (prefixWord ++ tailWord_4867200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867200).length < 2 ^ (prefixWord ++ tailWord_4867200).sum := by decide
  have hdescent : baseEnd_4867200 < baseStart_4867200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867229 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_4867229 : Nat := 118140960795 + 4867229 * 2 ^ 59
def prefixEnd_4867229 : Nat := 4983230072969 + 3 ^ 40 * 4867229 * 2
def baseEnd_4867229 : Nat := 2499227932502442677853527

theorem tailTrace_4867229 : CollatzResearch.WordTrace tailWord_4867229 prefixEnd_4867229 2499227932502442677853527 := by
  unfold tailWord_4867229
  simp only [CollatzResearch.WordTrace]
  refine ⟨177522425683868064378596741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118348283789245376252397827 177522425683868064378596741)
  ·
    refine ⟨33285454815725262070986889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177522425683868064378596741 33285454815725262070986889)
    ·
      refine ⟨24964091111793946553240167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33285454815725262070986889 24964091111793946553240167)
      ·
        refine ⟨37446136667690919829860251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24964091111793946553240167 37446136667690919829860251)
        ·
          refine ⟨56169205001536379744790377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37446136667690919829860251 56169205001536379744790377)
          ·
            refine ⟨42126903751152284808592783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56169205001536379744790377 42126903751152284808592783)
            ·
              refine ⟨63190355626728427212889175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42126903751152284808592783 63190355626728427212889175)
              ·
                refine ⟨94785533440092640819333763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63190355626728427212889175 94785533440092640819333763)
                ·
                  refine ⟨142178300160138961229000645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94785533440092640819333763 142178300160138961229000645)
                  ·
                    refine ⟨26658431280026055230437621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 142178300160138961229000645 26658431280026055230437621)
                    ·
                      refine ⟨2499227932502442677853527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26658431280026055230437621 2499227932502442677853527)
                      ·
                        rfl

theorem cell23_4867229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_4867229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867229 prefixEnd_4867229 := by exact prefixLift 4867229
  have htrace : WordTrace (prefixWord ++ tailWord_4867229) baseStart_4867229 baseEnd_4867229 := by
    simpa [prefixWord, tailWord_4867229, baseEnd_4867229] using wordTrace_append hprefix tailTrace_4867229
  have hstable : (prefixWord ++ tailWord_4867229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867229).length < 2 ^ (prefixWord ++ tailWord_4867229).sum := by decide
  have hdescent : baseEnd_4867229 < baseStart_4867229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867256 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 5, 4, 2]
def baseStart_4867256 : Nat := 118140960795 + 4867256 * 2 ^ 59
def prefixEnd_4867256 : Nat := 4983230072969 + 3 ^ 40 * 4867256 * 2
def baseEnd_4867256 : Nat := 2499241796480114072215903

theorem tailTrace_4867256 : CollatzResearch.WordTrace tailWord_4867256 prefixEnd_4867256 2499241796480114072215903 := by
  unfold tailWord_4867256
  simp only [CollatzResearch.WordTrace]
  refine ⟨88761705227385123994914811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118348940303180165326553081 88761705227385123994914811)
  ·
    refine ⟨133142557841077685992372217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88761705227385123994914811 133142557841077685992372217)
    ·
      refine ⟨99856918380808264494279163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133142557841077685992372217 99856918380808264494279163)
      ·
        refine ⟨149785377571212396741418745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99856918380808264494279163 149785377571212396741418745)
        ·
          refine ⟨112339033178409297556064059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149785377571212396741418745 112339033178409297556064059)
          ·
            refine ⟨168508549767613946334096089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112339033178409297556064059 168508549767613946334096089)
            ·
              refine ⟨126381412325710459750572067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168508549767613946334096089 126381412325710459750572067)
              ·
                refine ⟨189572118488565689625858101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126381412325710459750572067 189572118488565689625858101)
                ·
                  refine ⟨17772386108303033402424197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 189572118488565689625858101 17772386108303033402424197)
                  ·
                    refine ⟨3332322395306818762954537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17772386108303033402424197 3332322395306818762954537)
                    ·
                      refine ⟨2499241796480114072215903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3332322395306818762954537 2499241796480114072215903)
                      ·
                        rfl

theorem cell23_4867256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 5, 4, 2].length) (baseStart_4867256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867256 prefixEnd_4867256 := by exact prefixLift 4867256
  have htrace : WordTrace (prefixWord ++ tailWord_4867256) baseStart_4867256 baseEnd_4867256 := by
    simpa [prefixWord, tailWord_4867256, baseEnd_4867256] using wordTrace_append hprefix tailTrace_4867256
  have hstable : (prefixWord ++ tailWord_4867256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867256).length < 2 ^ (prefixWord ++ tailWord_4867256).sum := by decide
  have hdescent : baseEnd_4867256 < baseStart_4867256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867269 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 1, 4, 4]
def baseStart_4867269 : Nat := 118140960795 + 4867269 * 2 ^ 59
def prefixEnd_4867269 : Nat := 4983230072969 + 3 ^ 40 * 4867269 * 2
def baseEnd_4867269 : Nat := 2499248471728622521353343

theorem tailTrace_4867269 : CollatzResearch.WordTrace tailWord_4867269 prefixEnd_4867269 2499248471728622521353343 := by
  unfold tailWord_4867269
  simp only [CollatzResearch.WordTrace]
  refine ⟨177523884603723151210052861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118349256402482100806701907 177523884603723151210052861)
  ·
    refine ⟨66571456726396181703769823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177523884603723151210052861 66571456726396181703769823)
    ·
      refine ⟨99857185089594272555654735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66571456726396181703769823 99857185089594272555654735)
      ·
        refine ⟨149785777634391408833482103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99857185089594272555654735 149785777634391408833482103)
        ·
          refine ⟨224678666451587113250223155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149785777634391408833482103 224678666451587113250223155)
          ·
            refine ⟨337017999677380669875334733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224678666451587113250223155 337017999677380669875334733)
            ·
              refine ⟨126381749879017751203250525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 337017999677380669875334733 126381749879017751203250525)
              ·
                refine ⟨47393156204631656701218947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126381749879017751203250525 47393156204631656701218947)
                ·
                  refine ⟨71089734306947485051828421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47393156204631656701218947 71089734306947485051828421)
                  ·
                    refine ⟨13329325182552653447217829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71089734306947485051828421 13329325182552653447217829)
                    ·
                      refine ⟨2499248471728622521353343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13329325182552653447217829 2499248471728622521353343)
                      ·
                        rfl

theorem cell23_4867269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_4867269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867269 prefixEnd_4867269 := by exact prefixLift 4867269
  have htrace : WordTrace (prefixWord ++ tailWord_4867269) baseStart_4867269 baseEnd_4867269 := by
    simpa [prefixWord, tailWord_4867269, baseEnd_4867269] using wordTrace_append hprefix tailTrace_4867269
  have hstable : (prefixWord ++ tailWord_4867269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867269).length < 2 ^ (prefixWord ++ tailWord_4867269).sum := by decide
  have hdescent : baseEnd_4867269 < baseStart_4867269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867358 : List Nat := [4, 3, 2, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_4867358 : Nat := 118140960795 + 4867358 * 2 ^ 59
def prefixEnd_4867358 : Nat := 4983230072969 + 3 ^ 40 * 4867358 * 2
def baseEnd_4867358 : Nat := 2499294171506872673140435

theorem tailTrace_4867358 : CollatzResearch.WordTrace tailWord_4867358 prefixEnd_4867358 2499294171506872673140435 := by
  unfold tailWord_4867358
  simp only [CollatzResearch.WordTrace]
  refine ⟨22190891337550089926255341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118351420466933812940028485 22190891337550089926255341)
  ·
    refine ⟨8321584251581283722345753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22190891337550089926255341 8321584251581283722345753)
    ·
      refine ⟨6241188188685962791759315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8321584251581283722345753 6241188188685962791759315)
      ·
        refine ⟨9361782283028944187638973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6241188188685962791759315 9361782283028944187638973)
        ·
          refine ⟨3510668356135854070364615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9361782283028944187638973 3510668356135854070364615)
          ·
            refine ⟨5266002534203781105546923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3510668356135854070364615 5266002534203781105546923)
            ·
              refine ⟨7899003801305671658320385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5266002534203781105546923 7899003801305671658320385)
              ·
                refine ⟨5924252850979253743740289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7899003801305671658320385 5924252850979253743740289)
                ·
                  refine ⟨4443189638234440307805217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5924252850979253743740289 4443189638234440307805217)
                  ·
                    refine ⟨3332392228675830230853913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4443189638234440307805217 3332392228675830230853913)
                    ·
                      refine ⟨2499294171506872673140435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3332392228675830230853913 2499294171506872673140435)
                      ·
                        rfl

theorem cell23_4867358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_4867358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867358 prefixEnd_4867358 := by exact prefixLift 4867358
  have htrace : WordTrace (prefixWord ++ tailWord_4867358) baseStart_4867358 baseEnd_4867358 := by
    simpa [prefixWord, tailWord_4867358, baseEnd_4867358] using wordTrace_append hprefix tailTrace_4867358
  have hstable : (prefixWord ++ tailWord_4867358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867358).length < 2 ^ (prefixWord ++ tailWord_4867358).sum := by decide
  have hdescent : baseEnd_4867358 < baseStart_4867358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867363 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 2, 4, 2]
def baseStart_4867363 : Nat := 118140960795 + 4867363 * 2 ^ 59
def prefixEnd_4867363 : Nat := 4983230072969 + 3 ^ 40 * 4867363 * 2
def baseEnd_4867363 : Nat := 2499296738910145153577911

theorem tailTrace_4867363 : CollatzResearch.WordTrace tailWord_4867363 prefixEnd_4867363 2499296738910145153577911 := by
  unfold tailWord_4867363
  simp only [CollatzResearch.WordTrace]
  refine ⟨177527313065382605263974743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118351542043588403509316495 177527313065382605263974743)
  ·
    refine ⟨266290969598073907895962115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177527313065382605263974743 266290969598073907895962115)
    ·
      refine ⟨399436454397110861843943173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266290969598073907895962115 399436454397110861843943173)
      ·
        refine ⟨74894335199458286595739345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 399436454397110861843943173 74894335199458286595739345)
        ·
          refine ⟨56170751399593714946804509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74894335199458286595739345 56170751399593714946804509)
          ·
            refine ⟨21064031774847643105051691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56170751399593714946804509 21064031774847643105051691)
            ·
              refine ⟨31596047662271464657577537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21064031774847643105051691 31596047662271464657577537)
              ·
                refine ⟨23697035746703598493183153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31596047662271464657577537 23697035746703598493183153)
                ·
                  refine ⟨17772776810027698869887365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23697035746703598493183153 17772776810027698869887365)
                  ·
                    refine ⟨3332395651880193538103881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17772776810027698869887365 3332395651880193538103881)
                    ·
                      refine ⟨2499296738910145153577911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3332395651880193538103881 2499296738910145153577911)
                      ·
                        rfl

theorem cell23_4867363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_4867363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867363 prefixEnd_4867363 := by exact prefixLift 4867363
  have htrace : WordTrace (prefixWord ++ tailWord_4867363) baseStart_4867363 baseEnd_4867363 := by
    simpa [prefixWord, tailWord_4867363, baseEnd_4867363] using wordTrace_append hprefix tailTrace_4867363
  have hstable : (prefixWord ++ tailWord_4867363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867363).length < 2 ^ (prefixWord ++ tailWord_4867363).sum := by decide
  have hdescent : baseEnd_4867363 < baseStart_4867363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867380 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_4867380 : Nat := 118140960795 + 4867380 * 2 ^ 59
def prefixEnd_4867380 : Nat := 4983230072969 + 3 ^ 40 * 4867380 * 2
def baseEnd_4867380 : Nat := 2499305468081271587065333

theorem tailTrace_4867380 : CollatzResearch.WordTrace tailWord_4867380 prefixEnd_4867380 2499305468081271587065333 := by
  unfold tailWord_4867380
  simp only [CollatzResearch.WordTrace]
  refine ⟨88763966553160508583671797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118351955404214011444895729 88763966553160508583671797)
  ·
    refine ⟨8321621864358797679719231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88763966553160508583671797 8321621864358797679719231)
    ·
      refine ⟨12482432796538196519578847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8321621864358797679719231 12482432796538196519578847)
      ·
        refine ⟨18723649194807294779368271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12482432796538196519578847 18723649194807294779368271)
        ·
          refine ⟨28085473792210942169052407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18723649194807294779368271 28085473792210942169052407)
          ·
            refine ⟨42128210688316413253578611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28085473792210942169052407 42128210688316413253578611)
            ·
              refine ⟨63192316032474619880367917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42128210688316413253578611 63192316032474619880367917)
              ·
                refine ⟨23697118512177982455137969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63192316032474619880367917 23697118512177982455137969)
                ·
                  refine ⟨17772838884133486841353477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23697118512177982455137969 17772838884133486841353477)
                  ·
                    refine ⟨3332407290775028782753777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17772838884133486841353477 3332407290775028782753777)
                    ·
                      refine ⟨2499305468081271587065333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3332407290775028782753777 2499305468081271587065333)
                      ·
                        rfl

theorem cell23_4867380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_4867380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867380 prefixEnd_4867380 := by exact prefixLift 4867380
  have htrace : WordTrace (prefixWord ++ tailWord_4867380) baseStart_4867380 baseEnd_4867380 := by
    simpa [prefixWord, tailWord_4867380, baseEnd_4867380] using wordTrace_append hprefix tailTrace_4867380
  have hstable : (prefixWord ++ tailWord_4867380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867380).length < 2 ^ (prefixWord ++ tailWord_4867380).sum := by decide
  have hdescent : baseEnd_4867380 < baseStart_4867380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867453 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 3, 1, 4]
def baseStart_4867453 : Nat := 118140960795 + 4867453 * 2 ^ 59
def prefixEnd_4867453 : Nat := 4983230072969 + 3 ^ 40 * 4867453 * 2
def baseEnd_4867453 : Nat := 2499342952169049801452497

theorem tailTrace_4867453 : CollatzResearch.WordTrace tailWord_4867453 prefixEnd_4867453 2499342952169049801452497 := by
  unfold tailWord_4867453
  simp only [CollatzResearch.WordTrace]
  refine ⟨177530595635056550634751013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118353730423371033756500675 177530595635056550634751013)
  ·
    refine ⟨33286986681573103244015815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177530595635056550634751013 33286986681573103244015815)
    ·
      refine ⟨49930480022359654866023723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33286986681573103244015815 49930480022359654866023723)
      ·
        refine ⟨74895720033539482299035585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49930480022359654866023723 74895720033539482299035585)
        ·
          refine ⟨56171790025154611724276689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74895720033539482299035585 56171790025154611724276689)
          ·
            refine ⟨42128842518865958793207517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56171790025154611724276689 42128842518865958793207517)
            ·
              refine ⟨15798315944574734547452819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42128842518865958793207517 15798315944574734547452819)
              ·
                refine ⟨23697473916862101821179229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15798315944574734547452819 23697473916862101821179229)
                ·
                  refine ⟨8886552718823288182942211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23697473916862101821179229 8886552718823288182942211)
                  ·
                    refine ⟨13329829078234932274413317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8886552718823288182942211 13329829078234932274413317)
                    ·
                      refine ⟨2499342952169049801452497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13329829078234932274413317 2499342952169049801452497)
                      ·
                        rfl

theorem cell23_4867453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_4867453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867453 prefixEnd_4867453 := by exact prefixLift 4867453
  have htrace : WordTrace (prefixWord ++ tailWord_4867453) baseStart_4867453 baseEnd_4867453 := by
    simpa [prefixWord, tailWord_4867453, baseEnd_4867453] using wordTrace_append hprefix tailTrace_4867453
  have hstable : (prefixWord ++ tailWord_4867453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867453).length < 2 ^ (prefixWord ++ tailWord_4867453).sum := by decide
  have hdescent : baseEnd_4867453 < baseStart_4867453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867456 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 5]
def baseStart_4867456 : Nat := 118140960795 + 4867456 * 2 ^ 59
def prefixEnd_4867456 : Nat := 4983230072969 + 3 ^ 40 * 4867456 * 2
def baseEnd_4867456 : Nat := 2499344492611013289714983

theorem tailTrace_4867456 : CollatzResearch.WordTrace tailWord_4867456 prefixEnd_4867456 2499344492611013289714983 := by
  unfold tailWord_4867456
  simp only [CollatzResearch.WordTrace]
  refine ⟨88765352527022841073555111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118353803369363788098073481 88765352527022841073555111)
  ·
    refine ⟨133148028790534261610332667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88765352527022841073555111 133148028790534261610332667)
    ·
      refine ⟨199722043185801392415499001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133148028790534261610332667 199722043185801392415499001)
      ·
        refine ⟨149791532389351044311624251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199722043185801392415499001 149791532389351044311624251)
        ·
          refine ⟨224687298584026566467436377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149791532389351044311624251 224687298584026566467436377)
          ·
            refine ⟨168515473938019924850577283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224687298584026566467436377 168515473938019924850577283)
            ·
              refine ⟨252773210907029887275865925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168515473938019924850577283 252773210907029887275865925)
              ·
                refine ⟨47394977045068103864224861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 252773210907029887275865925 47394977045068103864224861)
                ·
                  refine ⟨17773116391900538949084323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47394977045068103864224861 17773116391900538949084323)
                  ·
                    refine ⟨26659674587850808423626485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17773116391900538949084323 26659674587850808423626485)
                    ·
                      refine ⟨2499344492611013289714983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26659674587850808423626485 2499344492611013289714983)
                      ·
                        rfl

theorem cell23_4867456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_4867456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867456 prefixEnd_4867456 := by exact prefixLift 4867456
  have htrace : WordTrace (prefixWord ++ tailWord_4867456) baseStart_4867456 baseEnd_4867456 := by
    simpa [prefixWord, tailWord_4867456, baseEnd_4867456] using wordTrace_append hprefix tailTrace_4867456
  have hstable : (prefixWord ++ tailWord_4867456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867456).length < 2 ^ (prefixWord ++ tailWord_4867456).sum := by decide
  have hdescent : baseEnd_4867456 < baseStart_4867456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867463 : List Nat := [1, 1, 4, 2, 2, 3, 1, 2, 1, 6]
def baseStart_4867463 : Nat := 118140960795 + 4867463 * 2 ^ 59
def prefixEnd_4867463 : Nat := 4983230072969 + 3 ^ 40 * 4867463 * 2
def baseEnd_4867463 : Nat := 833116028991864920775817

theorem tailTrace_4867463 : CollatzResearch.WordTrace tailWord_4867463 prefixEnd_4867463 833116028991864920775817 := by
  unfold tailWord_4867463
  simp only [CollatzResearch.WordTrace]
  refine ⟨177530960365020322342615043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118353973576680214895076695 177530960365020322342615043)
  ·
    refine ⟨266296440547530483513922565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177530960365020322342615043 266296440547530483513922565)
    ·
      refine ⟨49930582602661965658860481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266296440547530483513922565 49930582602661965658860481)
      ·
        refine ⟨37447936951996474244145361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49930582602661965658860481 37447936951996474244145361)
        ·
          refine ⟨28085952713997355683109021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37447936951996474244145361 28085952713997355683109021)
          ·
            refine ⟨10532232267749008381165883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28085952713997355683109021 10532232267749008381165883)
            ·
              refine ⟨15798348401623512571748825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10532232267749008381165883 15798348401623512571748825)
              ·
                refine ⟨11848761301217634428811619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15798348401623512571748825 11848761301217634428811619)
                ·
                  refine ⟨17773141951826451643217429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11848761301217634428811619 17773141951826451643217429)
                  ·
                    refine ⟨833116028991864920775817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17773141951826451643217429 833116028991864920775817)
                    ·
                      rfl

theorem cell23_4867463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_4867463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867463 prefixEnd_4867463 := by exact prefixLift 4867463
  have htrace : WordTrace (prefixWord ++ tailWord_4867463) baseStart_4867463 baseEnd_4867463 := by
    simpa [prefixWord, tailWord_4867463, baseEnd_4867463] using wordTrace_append hprefix tailTrace_4867463
  have hstable : (prefixWord ++ tailWord_4867463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867463).length < 2 ^ (prefixWord ++ tailWord_4867463).sum := by decide
  have hdescent : baseEnd_4867463 < baseStart_4867463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867490 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_4867490 : Nat := 118140960795 + 4867490 * 2 ^ 59
def prefixEnd_4867490 : Nat := 4983230072969 + 3 ^ 40 * 4867490 * 2
def baseEnd_4867490 : Nat := 2499361950953266156689827

theorem tailTrace_4867490 : CollatzResearch.WordTrace tailWord_4867490 prefixEnd_4867490 2499361950953266156689827 := by
  unfold tailWord_4867490
  simp only [CollatzResearch.WordTrace]
  refine ⟨44382986283980626488461981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118354630090615003969231949 44382986283980626488461981)
  ·
    refine ⟨16643619856492734933173243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44382986283980626488461981 16643619856492734933173243)
    ·
      refine ⟨24965429784739102399759865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16643619856492734933173243 24965429784739102399759865)
      ·
        refine ⟨18724072338554326799819899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24965429784739102399759865 18724072338554326799819899)
        ·
          refine ⟨28086108507831490199729849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18724072338554326799819899 28086108507831490199729849)
          ·
            refine ⟨21064581380873617649797387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28086108507831490199729849 21064581380873617649797387)
            ·
              refine ⟨31596872071310426474696081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21064581380873617649797387 31596872071310426474696081)
              ·
                refine ⟨23697654053482819856022061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31596872071310426474696081 23697654053482819856022061)
                ·
                  refine ⟨8886620270056057446008273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23697654053482819856022061 8886620270056057446008273)
                  ·
                    refine ⟨6664965202542043084506205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8886620270056057446008273 6664965202542043084506205)
                    ·
                      refine ⟨2499361950953266156689827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6664965202542043084506205 2499361950953266156689827)
                      ·
                        rfl

theorem cell23_4867490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_4867490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867490 prefixEnd_4867490 := by exact prefixLift 4867490
  have htrace : WordTrace (prefixWord ++ tailWord_4867490) baseStart_4867490 baseEnd_4867490 := by
    simpa [prefixWord, tailWord_4867490, baseEnd_4867490] using wordTrace_append hprefix tailTrace_4867490
  have hstable : (prefixWord ++ tailWord_4867490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867490).length < 2 ^ (prefixWord ++ tailWord_4867490).sum := by decide
  have hdescent : baseEnd_4867490 < baseStart_4867490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867524 : List Nat := [2, 3, 3, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_4867524 : Nat := 118140960795 + 4867524 * 2 ^ 59
def prefixEnd_4867524 : Nat := 4983230072969 + 3 ^ 40 * 4867524 * 2
def baseEnd_4867524 : Nat := 2499379409295519023664671

theorem tailTrace_4867524 : CollatzResearch.WordTrace tailWord_4867524 prefixEnd_4867524 2499379409295519023664671 := by
  unfold tailWord_4867524
  simp only [CollatzResearch.WordTrace]
  refine ⟨88766592608899664880292813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118355456811866219840390417 88766592608899664880292813)
  ·
    refine ⟨33287472228337374330109805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88766592608899664880292813 33287472228337374330109805)
    ·
      refine ⟨12482802085626515373791177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33287472228337374330109805 12482802085626515373791177)
      ·
        refine ⟨9362101564219886530343383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12482802085626515373791177 9362101564219886530343383)
        ·
          refine ⟨14043152346329829795515075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9362101564219886530343383 14043152346329829795515075)
          ·
            refine ⟨21064728519494744693272613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14043152346329829795515075 21064728519494744693272613)
            ·
              refine ⟨3949636597405264629988615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21064728519494744693272613 3949636597405264629988615)
              ·
                refine ⟨5924454896107896944982923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3949636597405264629988615 5924454896107896944982923)
                ·
                  refine ⟨8886682344161845417474385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5924454896107896944982923 8886682344161845417474385)
                  ·
                    refine ⟨6665011758121384063105789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8886682344161845417474385 6665011758121384063105789)
                    ·
                      refine ⟨2499379409295519023664671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6665011758121384063105789 2499379409295519023664671)
                      ·
                        rfl

theorem cell23_4867524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_4867524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867524 prefixEnd_4867524 := by exact prefixLift 4867524
  have htrace : WordTrace (prefixWord ++ tailWord_4867524) baseStart_4867524 baseEnd_4867524 := by
    simpa [prefixWord, tailWord_4867524, baseEnd_4867524] using wordTrace_append hprefix tailTrace_4867524
  have hstable : (prefixWord ++ tailWord_4867524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867524).length < 2 ^ (prefixWord ++ tailWord_4867524).sum := by decide
  have hdescent : baseEnd_4867524 < baseStart_4867524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867536 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 3, 8]
def baseStart_4867536 : Nat := 118140960795 + 4867536 * 2 ^ 59
def prefixEnd_4867536 : Nat := 4983230072969 + 3 ^ 40 * 4867536 * 2
def baseEnd_4867536 : Nat := 833128523687790992238205

theorem tailTrace_4867536 : CollatzResearch.WordTrace tailWord_4867536 prefixEnd_4867536 833128523687790992238205 := by
  unfold tailWord_4867536
  simp only [CollatzResearch.WordTrace]
  refine ⟨88766811446877927905011231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118355748595837237206681641 88766811446877927905011231)
  ·
    refine ⟨133150217170316891857516847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88766811446877927905011231 133150217170316891857516847)
    ·
      refine ⟨199725325755475337786275271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133150217170316891857516847 199725325755475337786275271)
      ·
        refine ⟨299587988633213006679412907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199725325755475337786275271 299587988633213006679412907)
        ·
          refine ⟨449381982949819510019119361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299587988633213006679412907 449381982949819510019119361)
          ·
            refine ⟨337036487212364632514339521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 449381982949819510019119361 337036487212364632514339521)
            ·
              refine ⟨252777365409273474385754641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337036487212364632514339521 252777365409273474385754641)
              ·
                refine ⟨189583024056955105789315981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252777365409273474385754641 189583024056955105789315981)
                ·
                  refine ⟨71093634021358164670993493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189583024056955105789315981 71093634021358164670993493)
                  ·
                    refine ⟨833128523687790992238205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71093634021358164670993493 833128523687790992238205)
                    ·
                      rfl

theorem cell23_4867536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 3, 8].length) (baseStart_4867536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867536 prefixEnd_4867536 := by exact prefixLift 4867536
  have htrace : WordTrace (prefixWord ++ tailWord_4867536) baseStart_4867536 baseEnd_4867536 := by
    simpa [prefixWord, tailWord_4867536, baseEnd_4867536] using wordTrace_append hprefix tailTrace_4867536
  have hstable : (prefixWord ++ tailWord_4867536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867536).length < 2 ^ (prefixWord ++ tailWord_4867536).sum := by decide
  have hdescent : baseEnd_4867536 < baseStart_4867536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867553 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 2, 6]
def baseStart_4867553 : Nat := 118140960795 + 4867553 * 2 ^ 59
def prefixEnd_4867553 : Nat := 4983230072969 + 3 ^ 40 * 4867553 * 2
def baseEnd_4867553 : Nat := 833131433411499803400679

theorem tailTrace_4867553 : CollatzResearch.WordTrace tailWord_4867553 prefixEnd_4867553 833131433411499803400679 := by
  unfold tailWord_4867553
  simp only [CollatzResearch.WordTrace]
  refine ⟨177534242934694267713391313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118356161956462845142260875 177534242934694267713391313)
  ·
    refine ⟨133150682201020700785043485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177534242934694267713391313 133150682201020700785043485)
    ·
      refine ⟨49931505825382762794391307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133150682201020700785043485 49931505825382762794391307)
      ·
        refine ⟨74897258738074144191586961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49931505825382762794391307 74897258738074144191586961)
        ·
          refine ⟨56172944053555608143690221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74897258738074144191586961 56172944053555608143690221)
          ·
            refine ⟨21064854020083353053883833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56172944053555608143690221 21064854020083353053883833)
            ·
              refine ⟨15798640515062514790412875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21064854020083353053883833 15798640515062514790412875)
              ·
                refine ⟨23697960772593772185619313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15798640515062514790412875 23697960772593772185619313)
                ·
                  refine ⟨17773470579445329139214485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23697960772593772185619313 17773470579445329139214485)
                  ·
                    refine ⟨833131433411499803400679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17773470579445329139214485 833131433411499803400679)
                    ·
                      rfl

theorem cell23_4867553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_4867553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867553 prefixEnd_4867553 := by exact prefixLift 4867553
  have htrace : WordTrace (prefixWord ++ tailWord_4867553) baseStart_4867553 baseEnd_4867553 := by
    simpa [prefixWord, tailWord_4867553, baseEnd_4867553] using wordTrace_append hprefix tailTrace_4867553
  have hstable : (prefixWord ++ tailWord_4867553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867553).length < 2 ^ (prefixWord ++ tailWord_4867553).sum := by decide
  have hdescent : baseEnd_4867553 < baseStart_4867553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867653 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 2, 3, 5]
def baseStart_4867653 : Nat := 118140960795 + 4867653 * 2 ^ 59
def prefixEnd_4867653 : Nat := 4983230072969 + 3 ^ 40 * 4867653 * 2
def baseEnd_4867653 : Nat := 2499445648299949018951577

theorem tailTrace_4867653 : CollatzResearch.WordTrace tailWord_4867653 prefixEnd_4867653 2499445648299949018951577 := by
  unfold tailWord_4867653
  simp only [CollatzResearch.WordTrace]
  refine ⟨177537890234331984792031613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118358593489554656528021075 177537890234331984792031613)
  ·
    refine ⟨66576708837874494297011855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177537890234331984792031613 66576708837874494297011855)
    ·
      refine ⟨99865063256811741445517783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66576708837874494297011855 99865063256811741445517783)
      ·
        refine ⟨149797594885217612168276675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99865063256811741445517783 149797594885217612168276675)
        ·
          refine ⟨224696392327826418252415013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149797594885217612168276675 224696392327826418252415013)
          ·
            refine ⟨42130573561467453422327815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 224696392327826418252415013 42130573561467453422327815)
            ·
              refine ⟨63195860342201180133491723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42130573561467453422327815 63195860342201180133491723)
              ·
                refine ⟨94793790513301770200237585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63195860342201180133491723 94793790513301770200237585)
                ·
                  refine ⟨71095342884976327650178189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94793790513301770200237585 71095342884976327650178189)
                  ·
                    refine ⟨26660753581866122868816821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71095342884976327650178189 26660753581866122868816821)
                    ·
                      refine ⟨2499445648299949018951577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26660753581866122868816821 2499445648299949018951577)
                      ·
                        rfl

theorem cell23_4867653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_4867653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867653 prefixEnd_4867653 := by exact prefixLift 4867653
  have htrace : WordTrace (prefixWord ++ tailWord_4867653) baseStart_4867653 baseEnd_4867653 := by
    simpa [prefixWord, tailWord_4867653, baseEnd_4867653] using wordTrace_append hprefix tailTrace_4867653
  have hstable : (prefixWord ++ tailWord_4867653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867653).length < 2 ^ (prefixWord ++ tailWord_4867653).sum := by decide
  have hdescent : baseEnd_4867653 < baseStart_4867653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867663 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 4]
def baseStart_4867663 : Nat := 118140960795 + 4867663 * 2 ^ 59
def prefixEnd_4867663 : Nat := 4983230072969 + 3 ^ 40 * 4867663 * 2
def baseEnd_4867663 : Nat := 2499450783106493979826531

theorem tailTrace_4867663 : CollatzResearch.WordTrace tailWord_4867663 prefixEnd_4867663 2499450783106493979826531 := by
  unfold tailWord_4867663
  simp only [CollatzResearch.WordTrace]
  refine ⟨177538254964295756499895643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118358836642863837666597095 177538254964295756499895643)
  ·
    refine ⟨266307382446443634749843465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177538254964295756499895643 266307382446443634749843465)
    ·
      refine ⟨199730536834832726062382599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266307382446443634749843465 199730536834832726062382599)
      ·
        refine ⟨299595805252249089093573899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199730536834832726062382599 299595805252249089093573899)
        ·
          refine ⟨449393707878373633640360849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299595805252249089093573899 449393707878373633640360849)
          ·
            refine ⟨337045280908780225230270637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 449393707878373633640360849 337045280908780225230270637)
            ·
              refine ⟨126391980340792584461351489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 337045280908780225230270637 126391980340792584461351489)
              ·
                refine ⟨94793985255594438346013617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126391980340792584461351489 94793985255594438346013617)
                ·
                  refine ⟨71095488941695828759510213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94793985255594438346013617 71095488941695828759510213)
                  ·
                    refine ⟨13330404176567967892408165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71095488941695828759510213 13330404176567967892408165)
                    ·
                      refine ⟨2499450783106493979826531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13330404176567967892408165 2499450783106493979826531)
                      ·
                        rfl

theorem cell23_4867663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 4, 4].length) (baseStart_4867663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867663 prefixEnd_4867663 := by exact prefixLift 4867663
  have htrace : WordTrace (prefixWord ++ tailWord_4867663) baseStart_4867663 baseEnd_4867663 := by
    simpa [prefixWord, tailWord_4867663, baseEnd_4867663] using wordTrace_append hprefix tailTrace_4867663
  have hstable : (prefixWord ++ tailWord_4867663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867663).length < 2 ^ (prefixWord ++ tailWord_4867663).sum := by decide
  have hdescent : baseEnd_4867663 < baseStart_4867663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867687 : List Nat := [1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 3]
def baseStart_4867687 : Nat := 118140960795 + 4867687 * 2 ^ 59
def prefixEnd_4867687 : Nat := 4983230072969 + 3 ^ 40 * 4867687 * 2
def baseEnd_4867687 : Nat := 2499463106642201885926421

theorem tailTrace_4867687 : CollatzResearch.WordTrace tailWord_4867687 prefixEnd_4867687 2499463106642201885926421 := by
  unfold tailWord_4867687
  simp only [CollatzResearch.WordTrace]
  refine ⟨177539130316208808598769315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118359420210805872399179543 177539130316208808598769315)
  ·
    refine ⟨266308695474313212898153973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177539130316208808598769315 266308695474313212898153973)
    ·
      refine ⟨24966440200716863709201935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 266308695474313212898153973 24966440200716863709201935)
      ·
        refine ⟨37449660301075295563802903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24966440200716863709201935 37449660301075295563802903)
        ·
          refine ⟨56174490451612943345704355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37449660301075295563802903 56174490451612943345704355)
          ·
            refine ⟨84261735677419415018556533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56174490451612943345704355 84261735677419415018556533)
            ·
              refine ⟨7899537719758070157989675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84261735677419415018556533 7899537719758070157989675)
              ·
                refine ⟨11849306579637105236984513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7899537719758070157989675 11849306579637105236984513)
                ·
                  refine ⟨8886979934727828927738385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11849306579637105236984513 8886979934727828927738385)
                  ·
                    refine ⟨6665234951045871695803789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8886979934727828927738385 6665234951045871695803789)
                    ·
                      refine ⟨2499463106642201885926421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6665234951045871695803789 2499463106642201885926421)
                      ·
                        rfl

theorem cell23_4867687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_4867687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867687 prefixEnd_4867687 := by exact prefixLift 4867687
  have htrace : WordTrace (prefixWord ++ tailWord_4867687) baseStart_4867687 baseEnd_4867687 := by
    simpa [prefixWord, tailWord_4867687, baseEnd_4867687] using wordTrace_append hprefix tailTrace_4867687
  have hstable : (prefixWord ++ tailWord_4867687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867687).length < 2 ^ (prefixWord ++ tailWord_4867687).sum := by decide
  have hdescent : baseEnd_4867687 < baseStart_4867687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867760 : List Nat := [2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 5]
def baseStart_4867760 : Nat := 118140960795 + 4867760 * 2 ^ 59
def prefixEnd_4867760 : Nat := 4983230072969 + 3 ^ 40 * 4867760 * 2
def baseEnd_4867760 : Nat := 2499500590729980100313585

theorem tailTrace_4867760 : CollatzResearch.WordTrace tailWord_4867760 prefixEnd_4867760 2499500590729980100313585 := by
  unfold tailWord_4867760
  simp only [CollatzResearch.WordTrace]
  refine ⟨88770896422472171033088367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118361195229962894710784489 88770896422472171033088367)
  ·
    refine ⟨133156344633708256549632551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88770896422472171033088367 133156344633708256549632551)
    ·
      refine ⟨199734516950562384824448827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133156344633708256549632551 199734516950562384824448827)
      ·
        refine ⟨299601775425843577236673241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199734516950562384824448827 299601775425843577236673241)
        ·
          refine ⟨224701331569382682927504931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299601775425843577236673241 224701331569382682927504931)
          ·
            refine ⟨337051997354074024391257397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224701331569382682927504931 337051997354074024391257397)
            ·
              refine ⟨31598624751944439786680381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 337051997354074024391257397 31598624751944439786680381)
              ·
                refine ⟨11849484281979164920005143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31598624751944439786680381 11849484281979164920005143)
                ·
                  refine ⟨17774226422968747380007715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11849484281979164920005143 17774226422968747380007715)
                  ·
                    refine ⟨26661339634453121070011573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17774226422968747380007715 26661339634453121070011573)
                    ·
                      refine ⟨2499500590729980100313585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26661339634453121070011573 2499500590729980100313585)
                      ·
                        rfl

theorem cell23_4867760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 5].length) (baseStart_4867760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867760 prefixEnd_4867760 := by exact prefixLift 4867760
  have htrace : WordTrace (prefixWord ++ tailWord_4867760) baseStart_4867760 baseEnd_4867760 := by
    simpa [prefixWord, tailWord_4867760, baseEnd_4867760] using wordTrace_append hprefix tailTrace_4867760
  have hstable : (prefixWord ++ tailWord_4867760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867760).length < 2 ^ (prefixWord ++ tailWord_4867760).sum := by decide
  have hdescent : baseEnd_4867760 < baseStart_4867760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867767 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 4, 4]
def baseStart_4867767 : Nat := 118140960795 + 4867767 * 2 ^ 59
def prefixEnd_4867767 : Nat := 4983230072969 + 3 ^ 40 * 4867767 * 2
def baseEnd_4867767 : Nat := 833168061698187190975351

theorem tailTrace_4867767 : CollatzResearch.WordTrace tailWord_4867767 prefixEnd_4867767 833168061698187190975351 := by
  unfold tailWord_4867767
  simp only [CollatzResearch.WordTrace]
  refine ⟨177542048155918982261681555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118361365437279321507787703 177542048155918982261681555)
  ·
    refine ⟨266313072233878473392522333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177542048155918982261681555 266313072233878473392522333)
    ·
      refine ⟨99867402087704427522195875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266313072233878473392522333 99867402087704427522195875)
      ·
        refine ⟨149801103131556641283293813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99867402087704427522195875 149801103131556641283293813)
        ·
          refine ⟨14043853418583435120308795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 149801103131556641283293813 14043853418583435120308795)
          ·
            refine ⟨21065780127875152680463193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14043853418583435120308795 21065780127875152680463193)
            ·
              refine ⟨15799335095906364510347395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21065780127875152680463193 15799335095906364510347395)
              ·
                refine ⟨23699002643859546765521093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15799335095906364510347395 23699002643859546765521093)
                ·
                  refine ⟨4443562995723665018535205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23699002643859546765521093 4443562995723665018535205)
                  ·
                    refine ⟨833168061698187190975351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4443562995723665018535205 833168061698187190975351)
                    ·
                      rfl

theorem cell23_4867767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 4, 4].length) (baseStart_4867767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867767 prefixEnd_4867767 := by exact prefixLift 4867767
  have htrace : WordTrace (prefixWord ++ tailWord_4867767) baseStart_4867767 baseEnd_4867767 := by
    simpa [prefixWord, tailWord_4867767, baseEnd_4867767] using wordTrace_append hprefix tailTrace_4867767
  have hstable : (prefixWord ++ tailWord_4867767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867767).length < 2 ^ (prefixWord ++ tailWord_4867767).sum := by decide
  have hdescent : baseEnd_4867767 < baseStart_4867767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867770 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6]
def baseStart_4867770 : Nat := 118140960795 + 4867770 * 2 ^ 59
def prefixEnd_4867770 : Nat := 4983230072969 + 3 ^ 40 * 4867770 * 2
def baseEnd_4867770 : Nat := 2499505725536525061188539

theorem tailTrace_4867770 : CollatzResearch.WordTrace tailWord_4867770 prefixEnd_4867770 2499505725536525061188539 := by
  unfold tailWord_4867770
  simp only [CollatzResearch.WordTrace]
  refine ⟨44385539393727028443510191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118361438383272075849360509 44385539393727028443510191)
  ·
    refine ⟨66578309090590542665265287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44385539393727028443510191 66578309090590542665265287)
    ·
      refine ⟨99867463635885813997897931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66578309090590542665265287 99867463635885813997897931)
      ·
        refine ⟨149801195453828720996846897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99867463635885813997897931 149801195453828720996846897)
        ·
          refine ⟨112350896590371540747635173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149801195453828720996846897 112350896590371540747635173)
          ·
            refine ⟨21065793110694663890181595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112350896590371540747635173 21065793110694663890181595)
            ·
              refine ⟨31598689666041995835272393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21065793110694663890181595 31598689666041995835272393)
              ·
                refine ⟨23699017249531496876454295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31598689666041995835272393 23699017249531496876454295)
                ·
                  refine ⟨35548525874297245314681443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23699017249531496876454295 35548525874297245314681443)
                  ·
                    refine ⟨53322788811445867972022165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35548525874297245314681443 53322788811445867972022165)
                    ·
                      refine ⟨2499505725536525061188539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53322788811445867972022165 2499505725536525061188539)
                      ·
                        rfl

theorem cell23_4867770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_4867770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867770 prefixEnd_4867770 := by exact prefixLift 4867770
  have htrace : WordTrace (prefixWord ++ tailWord_4867770) baseStart_4867770 baseEnd_4867770 := by
    simpa [prefixWord, tailWord_4867770, baseEnd_4867770] using wordTrace_append hprefix tailTrace_4867770
  have hstable : (prefixWord ++ tailWord_4867770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867770).length < 2 ^ (prefixWord ++ tailWord_4867770).sum := by decide
  have hdescent : baseEnd_4867770 < baseStart_4867770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867794 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_4867794 : Nat := 118140960795 + 4867794 * 2 ^ 59
def prefixEnd_4867794 : Nat := 4983230072969 + 3 ^ 40 * 4867794 * 2
def baseEnd_4867794 : Nat := 2499518049072232967288429

theorem tailTrace_4867794 : CollatzResearch.WordTrace tailWord_4867794 prefixEnd_4867794 2499518049072232967288429 := by
  unfold tailWord_4867794
  simp only [CollatzResearch.WordTrace]
  refine ⟨44385758231705291468228609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118362021951214110581942957 44385758231705291468228609)
  ·
    refine ⟨33289318673778968601171457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44385758231705291468228609 33289318673778968601171457)
    ·
      refine ⟨24966989005334226450878593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33289318673778968601171457 24966989005334226450878593)
      ·
        refine ⟨18725241754000669838158945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24966989005334226450878593 18725241754000669838158945)
        ·
          refine ⟨14043931315500502378619209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18725241754000669838158945 14043931315500502378619209)
          ·
            refine ⟨10532948486625376783964407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14043931315500502378619209 10532948486625376783964407)
            ·
              refine ⟨15799422729938065175946611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10532948486625376783964407 15799422729938065175946611)
              ·
                refine ⟨23699134094907097763919917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15799422729938065175946611 23699134094907097763919917)
                ·
                  refine ⟨8887175285590161661469969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23699134094907097763919917 8887175285590161661469969)
                  ·
                    refine ⟨6665381464192621246102477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8887175285590161661469969 6665381464192621246102477)
                    ·
                      refine ⟨2499518049072232967288429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6665381464192621246102477 2499518049072232967288429)
                      ·
                        rfl

theorem cell23_4867794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_4867794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867794 prefixEnd_4867794 := by exact prefixLift 4867794
  have htrace : WordTrace (prefixWord ++ tailWord_4867794) baseStart_4867794 baseEnd_4867794 := by
    simpa [prefixWord, tailWord_4867794, baseEnd_4867794] using wordTrace_append hprefix tailTrace_4867794
  have hstable : (prefixWord ++ tailWord_4867794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867794).length < 2 ^ (prefixWord ++ tailWord_4867794).sum := by decide
  have hdescent : baseEnd_4867794 < baseStart_4867794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867807 : List Nat := [1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 3]
def baseStart_4867807 : Nat := 118140960795 + 4867807 * 2 ^ 59
def prefixEnd_4867807 : Nat := 4983230072969 + 3 ^ 40 * 4867807 * 2
def baseEnd_4867807 : Nat := 2499524724320741416425869

theorem tailTrace_4867807 : CollatzResearch.WordTrace tailWord_4867807 prefixEnd_4867807 2499524724320741416425869 := by
  unfold tailWord_4867807
  simp only [CollatzResearch.WordTrace]
  refine ⟨177543507075774069093137675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118362338050516046062091783 177543507075774069093137675)
  ·
    refine ⟨266315260613661103639706513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177543507075774069093137675 266315260613661103639706513)
    ·
      refine ⟨199736445460245827729779885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266315260613661103639706513 199736445460245827729779885)
      ·
        refine ⟨74901167047592185398667457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199736445460245827729779885 74901167047592185398667457)
        ·
          refine ⟨56175875285694139049000593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74901167047592185398667457 56175875285694139049000593)
          ·
            refine ⟨42131906464270604286750445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56175875285694139049000593 42131906464270604286750445)
            ·
              refine ⟨15799464924101476607531417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42131906464270604286750445 15799464924101476607531417)
              ·
                refine ⟨11849598693076107455648563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15799464924101476607531417 11849598693076107455648563)
                ·
                  refine ⟨17774398039614161183472845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11849598693076107455648563 17774398039614161183472845)
                  ·
                    refine ⟨6665399264855310443802317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17774398039614161183472845 6665399264855310443802317)
                    ·
                      refine ⟨2499524724320741416425869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6665399264855310443802317 2499524724320741416425869)
                      ·
                        rfl

theorem cell23_4867807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_4867807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867807 prefixEnd_4867807 := by exact prefixLift 4867807
  have htrace : WordTrace (prefixWord ++ tailWord_4867807) baseStart_4867807 baseEnd_4867807 := by
    simpa [prefixWord, tailWord_4867807, baseEnd_4867807] using wordTrace_append hprefix tailTrace_4867807
  have hstable : (prefixWord ++ tailWord_4867807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867807).length < 2 ^ (prefixWord ++ tailWord_4867807).sum := by decide
  have hdescent : baseEnd_4867807 < baseStart_4867807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867811 : List Nat := [1, 1, 1, 7, 3, 1, 1, 1, 1, 1, 5]
def baseStart_4867811 : Nat := 118140960795 + 4867811 * 2 ^ 59
def prefixEnd_4867811 : Nat := 4983230072969 + 3 ^ 40 * 4867811 * 2
def baseEnd_4867811 : Nat := 2499526778243359400775851

theorem tailTrace_4867811 : CollatzResearch.WordTrace tailWord_4867811 prefixEnd_4867811 2499526778243359400775851 := by
  unfold tailWord_4867811
  simp only [CollatzResearch.WordTrace]
  refine ⟨177543652967759577776283287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118362435311839718517522191 177543652967759577776283287)
  ·
    refine ⟨266315479451639366664424931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177543652967759577776283287 266315479451639366664424931)
    ·
      refine ⟨399473219177459049996637397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266315479451639366664424931 399473219177459049996637397)
      ·
        refine ⟨9362653574471696484296189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 399473219177459049996637397 9362653574471696484296189)
        ·
          refine ⟨3510995090426886181611071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9362653574471696484296189 3510995090426886181611071)
          ·
            refine ⟨5266492635640329272416607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3510995090426886181611071 5266492635640329272416607)
            ·
              refine ⟨7899738953460493908624911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5266492635640329272416607 7899738953460493908624911)
              ·
                refine ⟨11849608430190740862937367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7899738953460493908624911 11849608430190740862937367)
                ·
                  refine ⟨17774412645286111294406051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11849608430190740862937367 17774412645286111294406051)
                  ·
                    refine ⟨26661618967929166941609077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17774412645286111294406051 26661618967929166941609077)
                    ·
                      refine ⟨2499526778243359400775851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26661618967929166941609077 2499526778243359400775851)
                      ·
                        rfl

theorem cell23_4867811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_4867811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867811 prefixEnd_4867811 := by exact prefixLift 4867811
  have htrace : WordTrace (prefixWord ++ tailWord_4867811) baseStart_4867811 baseEnd_4867811 := by
    simpa [prefixWord, tailWord_4867811, baseEnd_4867811] using wordTrace_append hprefix tailTrace_4867811
  have hstable : (prefixWord ++ tailWord_4867811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867811).length < 2 ^ (prefixWord ++ tailWord_4867811).sum := by decide
  have hdescent : baseEnd_4867811 < baseStart_4867811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867820 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 5]
def baseStart_4867820 : Nat := 118140960795 + 4867820 * 2 ^ 59
def prefixEnd_4867820 : Nat := 4983230072969 + 3 ^ 40 * 4867820 * 2
def baseEnd_4867820 : Nat := 2499531399569249865563309

theorem tailTrace_4867820 : CollatzResearch.WordTrace tailWord_4867820 prefixEnd_4867820 2499531399569249865563309 := by
  unfold tailWord_4867820
  simp only [CollatzResearch.WordTrace]
  refine ⟨88771990612363486156680457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118362654149817981542240609 88771990612363486156680457)
  ·
    refine ⟨66578992959272614617510343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88771990612363486156680457 66578992959272614617510343)
    ·
      refine ⟨99868489438908921926265515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66578992959272614617510343 99868489438908921926265515)
      ·
        refine ⟨149802734158363382889398273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99868489438908921926265515 149802734158363382889398273)
        ·
          refine ⟨112352050618772537167048705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149802734158363382889398273 112352050618772537167048705)
          ·
            refine ⟨84264037964079402875286529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112352050618772537167048705 84264037964079402875286529)
            ·
              refine ⟨63198028473059552156464897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84264037964079402875286529 63198028473059552156464897)
              ·
                refine ⟨47398521354794664117348673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63198028473059552156464897 47398521354794664117348673)
                ·
                  refine ⟨35548891016095998088011505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47398521354794664117348673 35548891016095998088011505)
                  ·
                    refine ⟨26661668262071998566008629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35548891016095998088011505 26661668262071998566008629)
                    ·
                      refine ⟨2499531399569249865563309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26661668262071998566008629 2499531399569249865563309)
                      ·
                        rfl

theorem cell23_4867820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_4867820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867820 prefixEnd_4867820 := by exact prefixLift 4867820
  have htrace : WordTrace (prefixWord ++ tailWord_4867820) baseStart_4867820 baseEnd_4867820 := by
    simpa [prefixWord, tailWord_4867820, baseEnd_4867820] using wordTrace_append hprefix tailTrace_4867820
  have hstable : (prefixWord ++ tailWord_4867820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867820).length < 2 ^ (prefixWord ++ tailWord_4867820).sum := by decide
  have hdescent : baseEnd_4867820 < baseStart_4867820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867825 : List Nat := [1, 2, 2, 2, 2, 5, 2, 2, 1, 2, 2]
def baseStart_4867825 : Nat := 118140960795 + 4867825 * 2 ^ 59
def prefixEnd_4867825 : Nat := 4983230072969 + 3 ^ 40 * 4867825 * 2
def baseEnd_4867825 : Nat := 2499533966972522346000787

theorem tailTrace_4867825 : CollatzResearch.WordTrace tailWord_4867825 prefixEnd_4867825 2499533966972522346000787 := by
  unfold tailWord_4867825
  simp only [CollatzResearch.WordTrace]
  refine ⟨177544163589708858167292929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118362775726472572111528619 177544163589708858167292929)
  ·
    refine ⟨133158122692281643625469697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177544163589708858167292929 133158122692281643625469697)
    ·
      refine ⟨99868592019211232719102273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133158122692281643625469697 99868592019211232719102273)
      ·
        refine ⟨74901444014408424539326705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99868592019211232719102273 74901444014408424539326705)
        ·
          refine ⟨56176083010806318404495029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74901444014408424539326705 56176083010806318404495029)
          ·
            refine ⟨5266507782263092350421409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56176083010806318404495029 5266507782263092350421409)
            ·
              refine ⟨3949880836697319262816057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5266507782263092350421409 3949880836697319262816057)
              ·
                refine ⟨2962410627522989447112043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3949880836697319262816057 2962410627522989447112043)
                ·
                  refine ⟨4443615941284484170668065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2962410627522989447112043 4443615941284484170668065)
                  ·
                    refine ⟨3332711955963363128001049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4443615941284484170668065 3332711955963363128001049)
                    ·
                      refine ⟨2499533966972522346000787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3332711955963363128001049 2499533966972522346000787)
                      ·
                        rfl

theorem cell23_4867825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2, 1, 2, 2].length) (baseStart_4867825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867825 prefixEnd_4867825 := by exact prefixLift 4867825
  have htrace : WordTrace (prefixWord ++ tailWord_4867825) baseStart_4867825 baseEnd_4867825 := by
    simpa [prefixWord, tailWord_4867825, baseEnd_4867825] using wordTrace_append hprefix tailTrace_4867825
  have hstable : (prefixWord ++ tailWord_4867825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867825).length < 2 ^ (prefixWord ++ tailWord_4867825).sum := by decide
  have hdescent : baseEnd_4867825 < baseStart_4867825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867840 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 2, 6]
def baseStart_4867840 : Nat := 118140960795 + 4867840 * 2 ^ 59
def prefixEnd_4867840 : Nat := 4983230072969 + 3 ^ 40 * 4867840 * 2
def baseEnd_4867840 : Nat := 833180556394113262437739

theorem tailTrace_4867840 : CollatzResearch.WordTrace tailWord_4867840 prefixEnd_4867840 833180556394113262437739 := by
  unfold tailWord_4867840
  simp only [CollatzResearch.WordTrace]
  refine ⟨88772355342327257864544487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118363140456436343819392649 88772355342327257864544487)
  ·
    refine ⟨133158533013490886796816731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88772355342327257864544487 133158533013490886796816731)
    ·
      refine ⟨199737799520236330195225097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133158533013490886796816731 199737799520236330195225097)
      ·
        refine ⟨149803349640177247646418823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199737799520236330195225097 149803349640177247646418823)
        ·
          refine ⟨224705024460265871469628235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149803349640177247646418823 224705024460265871469628235)
          ·
            refine ⟨337057536690398807204442353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224705024460265871469628235 337057536690398807204442353)
            ·
              refine ⟨252793152517799105403331765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337057536690398807204442353 252793152517799105403331765)
              ·
                refine ⟨23699358048543666131562353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 252793152517799105403331765 23699358048543666131562353)
                ·
                  refine ⟨17774518536407749598671765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23699358048543666131562353 17774518536407749598671765)
                  ·
                    refine ⟨833180556394113262437739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17774518536407749598671765 833180556394113262437739)
                    ·
                      rfl

theorem cell23_4867840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 2, 6].length) (baseStart_4867840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867840 prefixEnd_4867840 := by exact prefixLift 4867840
  have htrace : WordTrace (prefixWord ++ tailWord_4867840) baseStart_4867840 baseEnd_4867840 := by
    simpa [prefixWord, tailWord_4867840, baseEnd_4867840] using wordTrace_append hprefix tailTrace_4867840
  have hstable : (prefixWord ++ tailWord_4867840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867840).length < 2 ^ (prefixWord ++ tailWord_4867840).sum := by decide
  have hdescent : baseEnd_4867840 < baseStart_4867840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867846 : List Nat := [6, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_4867846 : Nat := 118140960795 + 4867846 * 2 ^ 59
def prefixEnd_4867846 : Nat := 4983230072969 + 3 ^ 40 * 4867846 * 2
def baseEnd_4867846 : Nat := 2499544750066266763838191

theorem tailTrace_4867846 : CollatzResearch.WordTrace tailWord_4867846 prefixEnd_4867846 2499544750066266763838191 := by
  unfold tailWord_4867846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5548279047582274336056481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 118363286348421852502538261 5548279047582274336056481)
  ·
    refine ⟨4161209285686705752042361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5548279047582274336056481 4161209285686705752042361)
    ·
      refine ⟨3120906964265029314031771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4161209285686705752042361 3120906964265029314031771)
      ·
        refine ⟨4681360446397543971047657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3120906964265029314031771 4681360446397543971047657)
        ·
          refine ⟨3511020334798157978285743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4681360446397543971047657 3511020334798157978285743)
          ·
            refine ⟨5266530502197236967428615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3511020334798157978285743 5266530502197236967428615)
            ·
              refine ⟨7899795753295855451142923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5266530502197236967428615 7899795753295855451142923)
              ·
                refine ⟨11849693629943783176714385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7899795753295855451142923 11849693629943783176714385)
                ·
                  refine ⟨8887270222457837382535789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11849693629943783176714385 8887270222457837382535789)
                  ·
                    refine ⟨3332726333421689018450921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8887270222457837382535789 3332726333421689018450921)
                    ·
                      refine ⟨2499544750066266763838191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3332726333421689018450921 2499544750066266763838191)
                      ·
                        rfl

theorem cell23_4867846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_4867846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867846 prefixEnd_4867846 := by exact prefixLift 4867846
  have htrace : WordTrace (prefixWord ++ tailWord_4867846) baseStart_4867846 baseEnd_4867846 := by
    simpa [prefixWord, tailWord_4867846, baseEnd_4867846] using wordTrace_append hprefix tailTrace_4867846
  have hstable : (prefixWord ++ tailWord_4867846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867846).length < 2 ^ (prefixWord ++ tailWord_4867846).sum := by decide
  have hdescent : baseEnd_4867846 < baseStart_4867846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867864 : List Nat := [2, 1, 2, 3, 1, 1, 4, 2, 1, 4, 2]
def baseStart_4867864 : Nat := 118140960795 + 4867864 * 2 ^ 59
def prefixEnd_4867864 : Nat := 4983230072969 + 3 ^ 40 * 4867864 * 2
def baseEnd_4867864 : Nat := 2499553992718047693413107

theorem tailTrace_4867864 : CollatzResearch.WordTrace tailWord_4867864 prefixEnd_4867864 2499553992718047693413107 := by
  unfold tailWord_4867864
  simp only [CollatzResearch.WordTrace]
  refine ⟨88772793018283783913981323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118363724024378378551975097 88772793018283783913981323)
  ·
    refine ⟨133159189527425675870971985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88772793018283783913981323 133159189527425675870971985)
    ·
      refine ⟨99869392145569256903228989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133159189527425675870971985 99869392145569256903228989)
      ·
        refine ⟨37451022054588471338710871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99869392145569256903228989 37451022054588471338710871)
        ·
          refine ⟨56176533081882707008066307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37451022054588471338710871 56176533081882707008066307)
          ·
            refine ⟨84264799622824060512099461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56176533081882707008066307 84264799622824060512099461)
            ·
              refine ⟨15799649929279511346018649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84264799622824060512099461 15799649929279511346018649)
              ·
                refine ⟨11849737446959633509513987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15799649929279511346018649 11849737446959633509513987)
                ·
                  refine ⟨17774606170439450264270981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11849737446959633509513987 17774606170439450264270981)
                  ·
                    refine ⟨3332738656957396924550809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17774606170439450264270981 3332738656957396924550809)
                    ·
                      refine ⟨2499553992718047693413107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3332738656957396924550809 2499553992718047693413107)
                      ·
                        rfl

theorem cell23_4867864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_4867864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867864 prefixEnd_4867864 := by exact prefixLift 4867864
  have htrace : WordTrace (prefixWord ++ tailWord_4867864) baseStart_4867864 baseEnd_4867864 := by
    simpa [prefixWord, tailWord_4867864, baseEnd_4867864] using wordTrace_append hprefix tailTrace_4867864
  have hstable : (prefixWord ++ tailWord_4867864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867864).length < 2 ^ (prefixWord ++ tailWord_4867864).sum := by decide
  have hdescent : baseEnd_4867864 < baseStart_4867864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867877 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 2, 2, 4]
def baseStart_4867877 : Nat := 118140960795 + 4867877 * 2 ^ 59
def prefixEnd_4867877 : Nat := 4983230072969 + 3 ^ 40 * 4867877 * 2
def baseEnd_4867877 : Nat := 2499560667966556142550547

theorem tailTrace_4867877 : CollatzResearch.WordTrace tailWord_4867877 prefixEnd_4867877 2499560667966556142550547 := by
  unfold tailWord_4867877
  simp only [CollatzResearch.WordTrace]
  refine ⟨177546060185520471048185885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118364040123680314032123923 177546060185520471048185885)
  ·
    refine ⟨66579772569570176643069707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177546060185520471048185885 66579772569570176643069707)
    ·
      refine ⟨99869658854355264964604561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66579772569570176643069707 99869658854355264964604561)
      ·
        refine ⟨74902244140766448723453421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99869658854355264964604561 74902244140766448723453421)
        ·
          refine ⟨28088341552787418271295033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74902244140766448723453421 28088341552787418271295033)
          ·
            refine ⟨21066256164590563703471275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28088341552787418271295033 21066256164590563703471275)
            ·
              refine ⟨31599384246885845555206913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21066256164590563703471275 31599384246885845555206913)
              ·
                refine ⟨23699538185164384166405185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31599384246885845555206913 23699538185164384166405185)
                ·
                  refine ⟨17774653638873288124803889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23699538185164384166405185 17774653638873288124803889)
                  ·
                    refine ⟨13330990229154966093602917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17774653638873288124803889 13330990229154966093602917)
                    ·
                      refine ⟨2499560667966556142550547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13330990229154966093602917 2499560667966556142550547)
                      ·
                        rfl

theorem cell23_4867877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_4867877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867877 prefixEnd_4867877 := by exact prefixLift 4867877
  have htrace : WordTrace (prefixWord ++ tailWord_4867877) baseStart_4867877 baseEnd_4867877 := by
    simpa [prefixWord, tailWord_4867877, baseEnd_4867877] using wordTrace_append hprefix tailTrace_4867877
  have hstable : (prefixWord ++ tailWord_4867877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867877).length < 2 ^ (prefixWord ++ tailWord_4867877).sum := by decide
  have hdescent : baseEnd_4867877 < baseStart_4867877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867921 : List Nat := [1, 2, 2, 1, 5, 3, 1, 3, 5]
def baseStart_4867921 : Nat := 118140960795 + 4867921 * 2 ^ 59
def prefixEnd_4867921 : Nat := 4983230072969 + 3 ^ 40 * 4867921 * 2
def baseEnd_4867921 : Nat := 277731473457261552266705

theorem tailTrace_4867921 : CollatzResearch.WordTrace tailWord_4867921 prefixEnd_4867921 277731473457261552266705 := by
  unfold tailWord_4867921
  simp only [CollatzResearch.WordTrace]
  refine ⟨177547664997361066562787617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118365109998240711041858411 177547664997361066562787617)
  ·
    refine ⟨133160748748020799922090713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177547664997361066562787617 133160748748020799922090713)
    ·
      refine ⟨99870561561015599941568035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133160748748020799922090713 99870561561015599941568035)
      ·
        refine ⟨149805842341523399912352053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99870561561015599941568035 149805842341523399912352053)
        ·
          refine ⟨14044297719517818741783005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 149805842341523399912352053 14044297719517818741783005)
          ·
            refine ⟨5266611644819182028168627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14044297719517818741783005 5266611644819182028168627)
            ·
              refine ⟨7899917467228773042252941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5266611644819182028168627 7899917467228773042252941)
              ·
                refine ⟨2962469050210789890844853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7899917467228773042252941 2962469050210789890844853)
                ·
                  refine ⟨277731473457261552266705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2962469050210789890844853 277731473457261552266705)
                  ·
                    rfl

theorem cell23_4867921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 3, 5].length) (baseStart_4867921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867921 prefixEnd_4867921 := by exact prefixLift 4867921
  have htrace : WordTrace (prefixWord ++ tailWord_4867921) baseStart_4867921 baseEnd_4867921 := by
    simpa [prefixWord, tailWord_4867921, baseEnd_4867921] using wordTrace_append hprefix tailTrace_4867921
  have hstable : (prefixWord ++ tailWord_4867921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867921).length < 2 ^ (prefixWord ++ tailWord_4867921).sum := by decide
  have hdescent : baseEnd_4867921 < baseStart_4867921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867938 : List Nat := [3, 3, 2, 1, 2, 2, 3, 2, 5]
def baseStart_4867938 : Nat := 118140960795 + 4867938 * 2 ^ 59
def prefixEnd_4867938 : Nat := 4983230072969 + 3 ^ 40 * 4867938 * 2
def baseEnd_4867938 : Nat := 277732443365164489320863

theorem tailTrace_4867938 : CollatzResearch.WordTrace tailWord_4867938 prefixEnd_4867938 277732443365164489320863 := by
  unfold tailWord_4867938
  simp only [CollatzResearch.WordTrace]
  refine ⟨44387071259574869616539117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118365523358866318977437645 44387071259574869616539117)
  ·
    refine ⟨16645151722340576106202169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44387071259574869616539117 16645151722340576106202169)
    ·
      refine ⟨12483863791755432079651627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16645151722340576106202169 12483863791755432079651627)
      ·
        refine ⟨18725795687633148119477441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12483863791755432079651627 18725795687633148119477441)
        ·
          refine ⟨14044346765724861089608081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18725795687633148119477441 14044346765724861089608081)
          ·
            refine ⟨10533260074293645817206061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14044346765724861089608081 10533260074293645817206061)
            ·
              refine ⟨3949972527860117181452273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10533260074293645817206061 3949972527860117181452273)
              ·
                refine ⟨2962479395895087886089205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3949972527860117181452273 2962479395895087886089205)
                ·
                  refine ⟨277732443365164489320863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2962479395895087886089205 277732443365164489320863)
                  ·
                    rfl

theorem cell23_4867938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_4867938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867938 prefixEnd_4867938 := by exact prefixLift 4867938
  have htrace : WordTrace (prefixWord ++ tailWord_4867938) baseStart_4867938 baseEnd_4867938 := by
    simpa [prefixWord, tailWord_4867938, baseEnd_4867938] using wordTrace_append hprefix tailTrace_4867938
  have hstable : (prefixWord ++ tailWord_4867938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867938).length < 2 ^ (prefixWord ++ tailWord_4867938).sum := by decide
  have hdescent : baseEnd_4867938 < baseStart_4867938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867954 : List Nat := [3, 2, 1, 2, 1, 1, 1, 3, 1, 6, 2]
def baseStart_4867954 : Nat := 118140960795 + 4867954 * 2 ^ 59
def prefixEnd_4867954 : Nat := 4983230072969 + 3 ^ 40 * 4867954 * 2
def baseEnd_4867954 : Nat := 2499600205976952341287693

theorem tailTrace_4867954 : CollatzResearch.WordTrace tailWord_4867954 prefixEnd_4867954 2499600205976952341287693 := by
  unfold tailWord_4867954
  simp only [CollatzResearch.WordTrace]
  refine ⟨44387217151560378299684729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118365912404161008799159277 44387217151560378299684729)
  ·
    refine ⟨33290412863670283724763547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44387217151560378299684729 33290412863670283724763547)
    ·
      refine ⟨49935619295505425587145321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33290412863670283724763547 49935619295505425587145321)
      ·
        refine ⟨37451714471629069190358991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49935619295505425587145321 37451714471629069190358991)
        ·
          refine ⟨56177571707443603785538487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37451714471629069190358991 56177571707443603785538487)
          ·
            refine ⟨84266357561165405678307731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56177571707443603785538487 84266357561165405678307731)
            ·
              refine ⟨126399536341748108517461597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84266357561165405678307731 126399536341748108517461597)
              ·
                refine ⟨47399826128155540694048099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126399536341748108517461597 47399826128155540694048099)
                ·
                  refine ⟨71099739192233311041072149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47399826128155540694048099 71099739192233311041072149)
                  ·
                    refine ⟨3332800274635936455050257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71099739192233311041072149 3332800274635936455050257)
                    ·
                      refine ⟨2499600205976952341287693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3332800274635936455050257 2499600205976952341287693)
                      ·
                        rfl

theorem cell23_4867954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_4867954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867954 prefixEnd_4867954 := by exact prefixLift 4867954
  have htrace : WordTrace (prefixWord ++ tailWord_4867954) baseStart_4867954 baseEnd_4867954 := by
    simpa [prefixWord, tailWord_4867954, baseEnd_4867954] using wordTrace_append hprefix tailTrace_4867954
  have hstable : (prefixWord ++ tailWord_4867954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867954).length < 2 ^ (prefixWord ++ tailWord_4867954).sum := by decide
  have hdescent : baseEnd_4867954 < baseStart_4867954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867987 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 3]
def baseStart_4867987 : Nat := 118140960795 + 4867987 * 2 ^ 59
def prefixEnd_4867987 : Nat := 4983230072969 + 3 ^ 40 * 4867987 * 2
def baseEnd_4867987 : Nat := 2499617150838550712175041

theorem tailTrace_4867987 : CollatzResearch.WordTrace tailWord_4867987 prefixEnd_4867987 2499617150838550712175041 := by
  unfold tailWord_4867987
  simp only [CollatzResearch.WordTrace]
  refine ⟨177550072215121959834690215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118366714810081306556460143 177550072215121959834690215)
  ·
    refine ⟨266325108322682939752035323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177550072215121959834690215 266325108322682939752035323)
    ·
      refine ⟨399487662484024409628052985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266325108322682939752035323 399487662484024409628052985)
      ·
        refine ⟨299615746863018307221039739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 399487662484024409628052985 299615746863018307221039739)
        ·
          refine ⟨449423620294527460831559609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299615746863018307221039739 449423620294527460831559609)
          ·
            refine ⟨337067715220895595623669707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 449423620294527460831559609 337067715220895595623669707)
            ·
              refine ⟨505601572831343393435504561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337067715220895595623669707 505601572831343393435504561)
              ·
                refine ⟨379201179623507545076628421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 505601572831343393435504561 379201179623507545076628421)
                ·
                  refine ⟨71100221179407664701867829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 379201179623507545076628421 71100221179407664701867829)
                  ·
                    refine ⟨6665645735569468565800109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71100221179407664701867829 6665645735569468565800109)
                    ·
                      refine ⟨2499617150838550712175041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6665645735569468565800109 2499617150838550712175041)
                      ·
                        rfl

theorem cell23_4867987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 5, 3].length) (baseStart_4867987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867987 prefixEnd_4867987 := by exact prefixLift 4867987
  have htrace : WordTrace (prefixWord ++ tailWord_4867987) baseStart_4867987 baseEnd_4867987 := by
    simpa [prefixWord, tailWord_4867987, baseEnd_4867987] using wordTrace_append hprefix tailTrace_4867987
  have hstable : (prefixWord ++ tailWord_4867987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867987).length < 2 ^ (prefixWord ++ tailWord_4867987).sum := by decide
  have hdescent : baseEnd_4867987 < baseStart_4867987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4867994 : List Nat := [3, 1, 1, 4, 2, 1, 1, 4, 6]
def baseStart_4867994 : Nat := 118140960795 + 4867994 * 2 ^ 59
def prefixEnd_4867994 : Nat := 4983230072969 + 3 ^ 40 * 4867994 * 2
def baseEnd_4867994 : Nat := 277735638355903576087501

theorem tailTrace_4867994 : CollatzResearch.WordTrace tailWord_4867994 prefixEnd_4867994 277735638355903576087501 := by
  unfold tailWord_4867994
  simp only [CollatzResearch.WordTrace]
  refine ⟨44387581881524150007548759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118366885017397733353463357 44387581881524150007548759)
  ·
    refine ⟨66581372822286225011323139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44387581881524150007548759 66581372822286225011323139)
    ·
      refine ⟨99872059233429337516984709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66581372822286225011323139 99872059233429337516984709)
      ·
        refine ⟨18726011106268000784434633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99872059233429337516984709 18726011106268000784434633)
        ·
          refine ⟨14044508329701000588325975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18726011106268000784434633 14044508329701000588325975)
          ·
            refine ⟨21066762494551500882488963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14044508329701000588325975 21066762494551500882488963)
            ·
              refine ⟨31600143741827251323733445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21066762494551500882488963 31600143741827251323733445)
              ·
                refine ⟨5925026951592609623200021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31600143741827251323733445 5925026951592609623200021)
                ·
                  refine ⟨277735638355903576087501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5925026951592609623200021 277735638355903576087501)
                  ·
                    rfl

theorem cell23_4867994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 6].length) (baseStart_4867994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4867994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4867994 prefixEnd_4867994 := by exact prefixLift 4867994
  have htrace : WordTrace (prefixWord ++ tailWord_4867994) baseStart_4867994 baseEnd_4867994 := by
    simpa [prefixWord, tailWord_4867994, baseEnd_4867994] using wordTrace_append hprefix tailTrace_4867994
  have hstable : (prefixWord ++ tailWord_4867994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4867994).length < 2 ^ (prefixWord ++ tailWord_4867994).sum := by decide
  have hdescent : baseEnd_4867994 < baseStart_4867994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4867994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868021 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 5, 1, 3]
def baseStart_4868021 : Nat := 118140960795 + 4868021 * 2 ^ 59
def prefixEnd_4868021 : Nat := 4983230072969 + 3 ^ 40 * 4868021 * 2
def baseEnd_4868021 : Nat := 2499634609180803579149885

theorem tailTrace_4868021 : CollatzResearch.WordTrace tailWord_4868021 prefixEnd_4868021 2499634609180803579149885 := by
  unfold tailWord_4868021
  simp only [CollatzResearch.WordTrace]
  refine ⟨177551312296998783641427917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118367541531332522427618611 177551312296998783641427917)
  ·
    refine ⟨66581742111374543865535469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177551312296998783641427917 66581742111374543865535469)
    ·
      refine ⟨24968153291765453949575801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66581742111374543865535469 24968153291765453949575801)
      ·
        refine ⟨18726114968824090462181851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24968153291765453949575801 18726114968824090462181851)
        ·
          refine ⟨28089172453236135693272777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18726114968824090462181851 28089172453236135693272777)
          ·
            refine ⟨21066879339927101769954583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28089172453236135693272777 21066879339927101769954583)
            ·
              refine ⟨31600319009890652654931875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21066879339927101769954583 31600319009890652654931875)
              ·
                refine ⟨47400478514835978982397813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31600319009890652654931875 47400478514835978982397813)
                ·
                  refine ⟨4443794860765873029599795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47400478514835978982397813 4443794860765873029599795)
                  ·
                    refine ⟨6665692291148809544399693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4443794860765873029599795 6665692291148809544399693)
                    ·
                      refine ⟨2499634609180803579149885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6665692291148809544399693 2499634609180803579149885)
                      ·
                        rfl

theorem cell23_4868021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_4868021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868021 prefixEnd_4868021 := by exact prefixLift 4868021
  have htrace : WordTrace (prefixWord ++ tailWord_4868021) baseStart_4868021 baseEnd_4868021 := by
    simpa [prefixWord, tailWord_4868021, baseEnd_4868021] using wordTrace_append hprefix tailTrace_4868021
  have hstable : (prefixWord ++ tailWord_4868021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868021).length < 2 ^ (prefixWord ++ tailWord_4868021).sum := by decide
  have hdescent : baseEnd_4868021 < baseStart_4868021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868024 : List Nat := [2, 1, 2, 1, 2, 3, 2, 4, 1, 5]
def baseStart_4868024 : Nat := 118140960795 + 4868024 * 2 ^ 59
def prefixEnd_4868024 : Nat := 4983230072969 + 3 ^ 40 * 4868024 * 2
def baseEnd_4868024 : Nat := 833212049874255689137457

theorem tailTrace_4868024 : CollatzResearch.WordTrace tailWord_4868024 prefixEnd_4868024 833212049874255689137457 := by
  unfold tailWord_4868024
  simp only [CollatzResearch.WordTrace]
  refine ⟨88775710857993957576893563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118367614477325276769191417 88775710857993957576893563)
  ·
    refine ⟨133163566286990936365340345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88775710857993957576893563 133163566286990936365340345)
    ·
      refine ⟨99872674715243202274005259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133163566286990936365340345 99872674715243202274005259)
      ·
        refine ⟨149809012072864803411007889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99872674715243202274005259 149809012072864803411007889)
        ·
          refine ⟨112356759054648602558255917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149809012072864803411007889 112356759054648602558255917)
          ·
            refine ⟨42133784645493225959345969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112356759054648602558255917 42133784645493225959345969)
            ·
              refine ⟨31600338484119919469509477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42133784645493225959345969 31600338484119919469509477)
              ·
                refine ⟨5925063465772484900533027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31600338484119919469509477 5925063465772484900533027)
                ·
                  refine ⟨8887595198658727350799541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5925063465772484900533027 8887595198658727350799541)
                  ·
                    refine ⟨833212049874255689137457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8887595198658727350799541 833212049874255689137457)
                    ·
                      rfl

theorem cell23_4868024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 1, 5].length) (baseStart_4868024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868024 prefixEnd_4868024 := by exact prefixLift 4868024
  have htrace : WordTrace (prefixWord ++ tailWord_4868024) baseStart_4868024 baseEnd_4868024 := by
    simpa [prefixWord, tailWord_4868024, baseEnd_4868024] using wordTrace_append hprefix tailTrace_4868024
  have hstable : (prefixWord ++ tailWord_4868024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868024).length < 2 ^ (prefixWord ++ tailWord_4868024).sum := by decide
  have hdescent : baseEnd_4868024 < baseStart_4868024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868037 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 3, 6]
def baseStart_4868037 : Nat := 118140960795 + 4868037 * 2 ^ 59
def prefixEnd_4868037 : Nat := 4983230072969 + 3 ^ 40 * 4868037 * 2
def baseEnd_4868037 : Nat := 833214274957091838849937

theorem tailTrace_4868037 : CollatzResearch.WordTrace tailWord_4868037 prefixEnd_4868037 833214274957091838849937 := by
  unfold tailWord_4868037
  simp only [CollatzResearch.WordTrace]
  refine ⟨177551895864940818374010365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118367930576627212249340243 177551895864940818374010365)
  ·
    refine ⟨66581960949352806890253887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177551895864940818374010365 66581960949352806890253887)
    ·
      refine ⟨99872941424029210335380831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66581960949352806890253887 99872941424029210335380831)
      ·
        refine ⟨149809412136043815503071247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99872941424029210335380831 149809412136043815503071247)
        ·
          refine ⟨224714118204065723254606871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149809412136043815503071247 224714118204065723254606871)
          ·
            refine ⟨337071177306098584881910307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224714118204065723254606871 337071177306098584881910307)
            ·
              refine ⟨505606765959147877322865461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337071177306098584881910307 505606765959147877322865461)
              ·
                refine ⟨47400634308670113499018637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 505606765959147877322865461 47400634308670113499018637)
                ·
                  refine ⟨17775237865751292562131989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47400634308670113499018637 17775237865751292562131989)
                  ·
                    refine ⟨833214274957091838849937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17775237865751292562131989 833214274957091838849937)
                    ·
                      rfl

theorem cell23_4868037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_4868037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868037 prefixEnd_4868037 := by exact prefixLift 4868037
  have htrace : WordTrace (prefixWord ++ tailWord_4868037) baseStart_4868037 baseEnd_4868037 := by
    simpa [prefixWord, tailWord_4868037, baseEnd_4868037] using wordTrace_append hprefix tailTrace_4868037
  have hstable : (prefixWord ++ tailWord_4868037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868037).length < 2 ^ (prefixWord ++ tailWord_4868037).sum := by decide
  have hdescent : baseEnd_4868037 < baseStart_4868037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868064 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 3]
def baseStart_4868064 : Nat := 118140960795 + 4868064 * 2 ^ 59
def prefixEnd_4868064 : Nat := 4983230072969 + 3 ^ 40 * 4868064 * 2
def baseEnd_4868064 : Nat := 2499656688848946910912187

theorem tailTrace_4868064 : CollatzResearch.WordTrace tailWord_4868064 prefixEnd_4868064 2499656688848946910912187 := by
  unfold tailWord_4868064
  simp only [CollatzResearch.WordTrace]
  refine ⟨88776440317921500992621623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118368587090562001323495497 88776440317921500992621623)
  ·
    refine ⟨133164660476882251488932435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88776440317921500992621623 133164660476882251488932435)
    ·
      refine ⟨199746990715323377233398653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133164660476882251488932435 199746990715323377233398653)
      ·
        refine ⟨74905121518246266462524495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199746990715323377233398653 74905121518246266462524495)
        ·
          refine ⟨112357682277369399693786743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74905121518246266462524495 112357682277369399693786743)
          ·
            refine ⟨168536523416054099540680115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112357682277369399693786743 168536523416054099540680115)
            ·
              refine ⟨252804785124081149311020173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168536523416054099540680115 252804785124081149311020173)
              ·
                refine ⟨94801794421530430991632565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 252804785124081149311020173 94801794421530430991632565)
                ·
                  refine ⟨8887668227018477905465553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94801794421530430991632565 8887668227018477905465553)
                  ·
                    refine ⟨6665751170263858429099165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8887668227018477905465553 6665751170263858429099165)
                    ·
                      refine ⟨2499656688848946910912187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6665751170263858429099165 2499656688848946910912187)
                      ·
                        rfl

theorem cell23_4868064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_4868064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868064 prefixEnd_4868064 := by exact prefixLift 4868064
  have htrace : WordTrace (prefixWord ++ tailWord_4868064) baseStart_4868064 baseEnd_4868064 := by
    simpa [prefixWord, tailWord_4868064, baseEnd_4868064] using wordTrace_append hprefix tailTrace_4868064
  have hstable : (prefixWord ++ tailWord_4868064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868064).length < 2 ^ (prefixWord ++ tailWord_4868064).sum := by decide
  have hdescent : baseEnd_4868064 < baseStart_4868064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868074 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_4868074 : Nat := 118140960795 + 4868074 * 2 ^ 59
def prefixEnd_4868074 : Nat := 4983230072969 + 3 ^ 40 * 4868074 * 2
def baseEnd_4868074 : Nat := 2499661823655491871787141

theorem tailTrace_4868074 : CollatzResearch.WordTrace tailWord_4868074 prefixEnd_4868074 2499661823655491871787141 := by
  unfold tailWord_4868074
  simp only [CollatzResearch.WordTrace]
  refine ⟨44388311341451693423276819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118368830243871182462071517 44388311341451693423276819)
  ·
    refine ⟨66582467012177540134915229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44388311341451693423276819 66582467012177540134915229)
    ·
      refine ⟨24968425129566577550593211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66582467012177540134915229 24968425129566577550593211)
      ·
        refine ⟨37452637694349866325889817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24968425129566577550593211 37452637694349866325889817)
        ·
          refine ⟨28089478270762399744417363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37452637694349866325889817 28089478270762399744417363)
          ·
            refine ⟨42134217406143599616626045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28089478270762399744417363 42134217406143599616626045)
            ·
              refine ⟨15800331527303849856234767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42134217406143599616626045 15800331527303849856234767)
              ·
                refine ⟨23700497290955774784352151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15800331527303849856234767 23700497290955774784352151)
                ·
                  refine ⟨35550745936433662176528227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23700497290955774784352151 35550745936433662176528227)
                  ·
                    refine ⟨53326118904650493264792341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35550745936433662176528227 53326118904650493264792341)
                    ·
                      refine ⟨2499661823655491871787141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53326118904650493264792341 2499661823655491871787141)
                      ·
                        rfl

theorem cell23_4868074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_4868074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868074 prefixEnd_4868074 := by exact prefixLift 4868074
  have htrace : WordTrace (prefixWord ++ tailWord_4868074) baseStart_4868074 baseEnd_4868074 := by
    simpa [prefixWord, tailWord_4868074, baseEnd_4868074] using wordTrace_append hprefix tailTrace_4868074
  have hstable : (prefixWord ++ tailWord_4868074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868074).length < 2 ^ (prefixWord ++ tailWord_4868074).sum := by decide
  have hdescent : baseEnd_4868074 < baseStart_4868074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868078 : List Nat := [4, 1, 2, 1, 3, 2, 2, 2, 1, 1, 4]
def baseStart_4868078 : Nat := 118140960795 + 4868078 * 2 ^ 59
def prefixEnd_4868078 : Nat := 4983230072969 + 3 ^ 40 * 4868078 * 2
def baseEnd_4868078 : Nat := 2499663877578109856137123

theorem tailTrace_4868078 : CollatzResearch.WordTrace tailWord_4868078 prefixEnd_4868078 2499663877578109856137123 := by
  unfold tailWord_4868078
  simp only [CollatzResearch.WordTrace]
  refine ⟨22194173907224035297031611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118368927505194854917501925 22194173907224035297031611)
  ·
    refine ⟨33291260860836052945547417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22194173907224035297031611 33291260860836052945547417)
    ·
      refine ⟨24968445645627039709160563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33291260860836052945547417 24968445645627039709160563)
      ·
        refine ⟨37452668468440559563740845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24968445645627039709160563 37452668468440559563740845)
        ·
          refine ⟨14044750675665209836402817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37452668468440559563740845 14044750675665209836402817)
          ·
            refine ⟨10533563006748907377302113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14044750675665209836402817 10533563006748907377302113)
            ·
              refine ⟨7900172255061680532976585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10533563006748907377302113 7900172255061680532976585)
              ·
                refine ⟨5925129191296260399732439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7900172255061680532976585 5925129191296260399732439)
                ·
                  refine ⟨8887693786944390599598659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5925129191296260399732439 8887693786944390599598659)
                  ·
                    refine ⟨13331540680416585899397989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8887693786944390599598659 13331540680416585899397989)
                    ·
                      refine ⟨2499663877578109856137123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13331540680416585899397989 2499663877578109856137123)
                      ·
                        rfl

theorem cell23_4868078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_4868078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868078 prefixEnd_4868078 := by exact prefixLift 4868078
  have htrace : WordTrace (prefixWord ++ tailWord_4868078) baseStart_4868078 baseEnd_4868078 := by
    simpa [prefixWord, tailWord_4868078, baseEnd_4868078] using wordTrace_append hprefix tailTrace_4868078
  have hstable : (prefixWord ++ tailWord_4868078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868078).length < 2 ^ (prefixWord ++ tailWord_4868078).sum := by decide
  have hdescent : baseEnd_4868078 < baseStart_4868078 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868087 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 6]
def baseStart_4868087 : Nat := 118140960795 + 4868087 * 2 ^ 59
def prefixEnd_4868087 : Nat := 4983230072969 + 3 ^ 40 * 4868087 * 2
def baseEnd_4868087 : Nat := 2499668498904000320924581

theorem tailTrace_4868087 : CollatzResearch.WordTrace tailWord_4868087 prefixEnd_4868087 2499668498904000320924581 := by
  unfold tailWord_4868087
  simp only [CollatzResearch.WordTrace]
  refine ⟨177553719514759676913330515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118369146343173117942220343 177553719514759676913330515)
  ·
    refine ⟨266330579272139515369995773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177553719514759676913330515 266330579272139515369995773)
    ·
      refine ⟨99873967227052318263748415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266330579272139515369995773 99873967227052318263748415)
      ·
        refine ⟨149810950840578477395622623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99873967227052318263748415 149810950840578477395622623)
        ·
          refine ⟨224716426260867716093433935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149810950840578477395622623 224716426260867716093433935)
          ·
            refine ⟨337074639391301574140150903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224716426260867716093433935 337074639391301574140150903)
            ·
              refine ⟨505611959086952361210226355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337074639391301574140150903 505611959086952361210226355)
              ·
                refine ⟨758417938630428541815339533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505611959086952361210226355 758417938630428541815339533)
                ·
                  refine ⟨284406726986410703180752325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 758417938630428541815339533 284406726986410703180752325)
                  ·
                    refine ⟨53326261309952006846391061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 284406726986410703180752325 53326261309952006846391061)
                    ·
                      refine ⟨2499668498904000320924581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53326261309952006846391061 2499668498904000320924581)
                      ·
                        rfl

theorem cell23_4868087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_4868087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868087 prefixEnd_4868087 := by exact prefixLift 4868087
  have htrace : WordTrace (prefixWord ++ tailWord_4868087) baseStart_4868087 baseEnd_4868087 := by
    simpa [prefixWord, tailWord_4868087, baseEnd_4868087] using wordTrace_append hprefix tailTrace_4868087
  have hstable : (prefixWord ++ tailWord_4868087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868087).length < 2 ^ (prefixWord ++ tailWord_4868087).sum := by decide
  have hdescent : baseEnd_4868087 < baseStart_4868087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868121 : List Nat := [1, 2, 1, 2, 1, 1, 3, 4, 3, 3, 2]
def baseStart_4868121 : Nat := 118140960795 + 4868121 * 2 ^ 59
def prefixEnd_4868121 : Nat := 4983230072969 + 3 ^ 40 * 4868121 * 2
def baseEnd_4868121 : Nat := 2499685957246253187899425

theorem tailTrace_4868121 : CollatzResearch.WordTrace tailWord_4868121 prefixEnd_4868121 2499685957246253187899425 := by
  unfold tailWord_4868121
  simp only [CollatzResearch.WordTrace]
  refine ⟨177554959596636500720068217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118369973064424333813378811 177554959596636500720068217)
  ·
    refine ⟨133166219697477375540051163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177554959596636500720068217 133166219697477375540051163)
    ·
      refine ⟨199749329546216063310076745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133166219697477375540051163 199749329546216063310076745)
      ·
        refine ⟨149811997159662047482557559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199749329546216063310076745 149811997159662047482557559)
        ·
          refine ⟨224717995739493071223836339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149811997159662047482557559 224717995739493071223836339)
          ·
            refine ⟨337076993609239606835754509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224717995739493071223836339 337076993609239606835754509)
            ·
              refine ⟨126403872603464852563407941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 337076993609239606835754509 126403872603464852563407941)
              ·
                refine ⟨23700726113149659855638989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126403872603464852563407941 23700726113149659855638989)
                ·
                  refine ⟨8887772292431122445864621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23700726113149659855638989 8887772292431122445864621)
                  ·
                    refine ⟨3332914609661670917199233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8887772292431122445864621 3332914609661670917199233)
                    ·
                      refine ⟨2499685957246253187899425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3332914609661670917199233 2499685957246253187899425)
                      ·
                        rfl

theorem cell23_4868121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 3, 3, 2].length) (baseStart_4868121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868121 prefixEnd_4868121 := by exact prefixLift 4868121
  have htrace : WordTrace (prefixWord ++ tailWord_4868121) baseStart_4868121 baseEnd_4868121 := by
    simpa [prefixWord, tailWord_4868121, baseEnd_4868121] using wordTrace_append hprefix tailTrace_4868121
  have hstable : (prefixWord ++ tailWord_4868121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868121).length < 2 ^ (prefixWord ++ tailWord_4868121).sum := by decide
  have hdescent : baseEnd_4868121 < baseStart_4868121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868132 : List Nat := [2, 3, 1, 4, 3, 1, 1, 2, 1, 2, 3]
def baseStart_4868132 : Nat := 118140960795 + 4868132 * 2 ^ 59
def prefixEnd_4868132 : Nat := 4983230072969 + 3 ^ 40 * 4868132 * 2
def baseEnd_4868132 : Nat := 2499691605533452644861875

theorem tailTrace_4868132 : CollatzResearch.WordTrace tailWord_4868132 prefixEnd_4868132 2499691605533452644861875 := by
  unfold tailWord_4868132
  simp only [CollatzResearch.WordTrace]
  refine ⟨88777680399798324799359325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118370240533064433065812433 88777680399798324799359325)
  ·
    refine ⟨33291630149924371799759747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88777680399798324799359325 33291630149924371799759747)
    ·
      refine ⟨49937445224886557699639621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33291630149924371799759747 49937445224886557699639621)
      ·
        refine ⟨9363270979666229568682429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49937445224886557699639621 9363270979666229568682429)
        ·
          refine ⟨3511226617374836088255911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9363270979666229568682429 3511226617374836088255911)
          ·
            refine ⟨5266839926062254132383867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3511226617374836088255911 5266839926062254132383867)
            ·
              refine ⟨7900259889093381198575801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5266839926062254132383867 7900259889093381198575801)
              ·
                refine ⟨5925194916820035898931851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7900259889093381198575801 5925194916820035898931851)
                ·
                  refine ⟨8887792375230053848397777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5925194916820035898931851 8887792375230053848397777)
                  ·
                    refine ⟨6665844281422540386298333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8887792375230053848397777 6665844281422540386298333)
                    ·
                      refine ⟨2499691605533452644861875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6665844281422540386298333 2499691605533452644861875)
                      ·
                        rfl

theorem cell23_4868132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_4868132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868132 prefixEnd_4868132 := by exact prefixLift 4868132
  have htrace : WordTrace (prefixWord ++ tailWord_4868132) baseStart_4868132 baseEnd_4868132 := by
    simpa [prefixWord, tailWord_4868132, baseEnd_4868132] using wordTrace_append hprefix tailTrace_4868132
  have hstable : (prefixWord ++ tailWord_4868132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868132).length < 2 ^ (prefixWord ++ tailWord_4868132).sum := by decide
  have hdescent : baseEnd_4868132 < baseStart_4868132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868151 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 3, 4, 2]
def baseStart_4868151 : Nat := 118140960795 + 4868151 * 2 ^ 59
def prefixEnd_4868151 : Nat := 4983230072969 + 3 ^ 40 * 4868151 * 2
def baseEnd_4868151 : Nat := 2499701361665888070524287

theorem tailTrace_4868151 : CollatzResearch.WordTrace tailWord_4868151 prefixEnd_4868151 2499701361665888070524287 := by
  unfold tailWord_4868151
  simp only [CollatzResearch.WordTrace]
  refine ⟨177556053786527815843660307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118370702524351877229106871 177556053786527815843660307)
  ·
    refine ⟨266334080679791723765490461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177556053786527815843660307 266334080679791723765490461)
    ·
      refine ⟨99875280254921896412058923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266334080679791723765490461 99875280254921896412058923)
      ·
        refine ⟨149812920382382844618088385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99875280254921896412058923 149812920382382844618088385)
        ·
          refine ⟨112359690286787133463566289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149812920382382844618088385 112359690286787133463566289)
          ·
            refine ⟨84269767715090350097674717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112359690286787133463566289 84269767715090350097674717)
            ·
              refine ⟨31601162893158881286628019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84269767715090350097674717 31601162893158881286628019)
              ·
                refine ⟨47401744339738321929942029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31601162893158881286628019 47401744339738321929942029)
                ·
                  refine ⟨17775654127401870723728261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47401744339738321929942029 17775654127401870723728261)
                  ·
                    refine ⟨3332935148887850760699049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17775654127401870723728261 3332935148887850760699049)
                    ·
                      refine ⟨2499701361665888070524287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3332935148887850760699049 2499701361665888070524287)
                      ·
                        rfl

theorem cell23_4868151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 4, 2].length) (baseStart_4868151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868151 prefixEnd_4868151 := by exact prefixLift 4868151
  have htrace : WordTrace (prefixWord ++ tailWord_4868151) baseStart_4868151 baseEnd_4868151 := by
    simpa [prefixWord, tailWord_4868151, baseEnd_4868151] using wordTrace_append hprefix tailTrace_4868151
  have hstable : (prefixWord ++ tailWord_4868151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868151).length < 2 ^ (prefixWord ++ tailWord_4868151).sum := by decide
  have hdescent : baseEnd_4868151 < baseStart_4868151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868181 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 2, 2, 4]
def baseStart_4868181 : Nat := 118140960795 + 4868181 * 2 ^ 59
def prefixEnd_4868181 : Nat := 4983230072969 + 3 ^ 40 * 4868181 * 2
def baseEnd_4868181 : Nat := 2499716766085522953149149

theorem tailTrace_4868181 : CollatzResearch.WordTrace tailWord_4868181 prefixEnd_4868181 2499716766085522953149149 := by
  unfold tailWord_4868181
  simp only [CollatzResearch.WordTrace]
  refine ⟨177557147976419130967252397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118371431984279420644834931 177557147976419130967252397)
  ·
    refine ⟨66583930491157174112719649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177557147976419130967252397 66583930491157174112719649)
    ·
      refine ⟨49937947868367880584539737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66583930491157174112719649 49937947868367880584539737)
      ·
        refine ⟨37453460901275910438404803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49937947868367880584539737 37453460901275910438404803)
        ·
          refine ⟨56180191351913865657607205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37453460901275910438404803 56180191351913865657607205)
          ·
            refine ⟨10533785878483849810801351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56180191351913865657607205 10533785878483849810801351)
            ·
              refine ⟨15800678817725774716202027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10533785878483849810801351 15800678817725774716202027)
              ·
                refine ⟨23701018226588662074303041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15800678817725774716202027 23701018226588662074303041)
                ·
                  refine ⟨17775763669941496555727281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23701018226588662074303041 17775763669941496555727281)
                  ·
                    refine ⟨13331822752456122416795461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17775763669941496555727281 13331822752456122416795461)
                    ·
                      refine ⟨2499716766085522953149149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13331822752456122416795461 2499716766085522953149149)
                      ·
                        rfl

theorem cell23_4868181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_4868181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868181 prefixEnd_4868181 := by exact prefixLift 4868181
  have htrace : WordTrace (prefixWord ++ tailWord_4868181) baseStart_4868181 baseEnd_4868181 := by
    simpa [prefixWord, tailWord_4868181, baseEnd_4868181] using wordTrace_append hprefix tailTrace_4868181
  have hstable : (prefixWord ++ tailWord_4868181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868181).length < 2 ^ (prefixWord ++ tailWord_4868181).sum := by decide
  have hdescent : baseEnd_4868181 < baseStart_4868181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868208 : List Nat := [2, 1, 1, 1, 5, 3, 2, 3, 5]
def baseStart_4868208 : Nat := 118140960795 + 4868208 * 2 ^ 59
def prefixEnd_4868208 : Nat := 4983230072969 + 3 ^ 40 * 4868208 * 2
def baseEnd_4868208 : Nat := 277747847784799371945725

theorem tailTrace_4868208 : CollatzResearch.WordTrace tailWord_4868208 prefixEnd_4868208 277747847784799371945725 := by
  unfold tailWord_4868208
  simp only [CollatzResearch.WordTrace]
  refine ⟨88779066373660657289242639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118372088498214209718990185 88779066373660657289242639)
  ·
    refine ⟨133168599560490985933863959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88779066373660657289242639 133168599560490985933863959)
    ·
      refine ⟨199752899340736478900795939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133168599560490985933863959 199752899340736478900795939)
      ·
        refine ⟨299629349011104718351193909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199752899340736478900795939 299629349011104718351193909)
        ·
          refine ⟨28090251469791067345424429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 299629349011104718351193909 28090251469791067345424429)
          ·
            refine ⟨10533844301171650254534161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28090251469791067345424429 10533844301171650254534161)
            ·
              refine ⟨7900383225878737690900621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10533844301171650254534161 7900383225878737690900621)
              ·
                refine ⟨2962643709704526634087733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7900383225878737690900621 2962643709704526634087733)
                ·
                  refine ⟨277747847784799371945725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2962643709704526634087733 277747847784799371945725)
                  ·
                    rfl

theorem cell23_4868208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 3, 5].length) (baseStart_4868208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868208 prefixEnd_4868208 := by exact prefixLift 4868208
  have htrace : WordTrace (prefixWord ++ tailWord_4868208) baseStart_4868208 baseEnd_4868208 := by
    simpa [prefixWord, tailWord_4868208, baseEnd_4868208] using wordTrace_append hprefix tailTrace_4868208
  have hstable : (prefixWord ++ tailWord_4868208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868208).length < 2 ^ (prefixWord ++ tailWord_4868208).sum := by decide
  have hdescent : baseEnd_4868208 < baseStart_4868208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868251 : List Nat := [1, 1, 1, 1, 1, 1, 2, 8, 3, 4]
def baseStart_4868251 : Nat := 118140960795 + 4868251 * 2 ^ 59
def prefixEnd_4868251 : Nat := 4983230072969 + 3 ^ 40 * 4868251 * 2
def baseEnd_4868251 : Nat := 833250903243779226424609

theorem tailTrace_4868251 : CollatzResearch.WordTrace tailWord_4868251 prefixEnd_4868251 833250903243779226424609 := by
  unfold tailWord_4868251
  simp only [CollatzResearch.WordTrace]
  refine ⟨177559701086165532922300607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118373134057443688614867071 177559701086165532922300607)
  ·
    refine ⟨266339551629248299383450911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177559701086165532922300607 266339551629248299383450911)
    ·
      refine ⟨399509327443872449075176367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266339551629248299383450911 399509327443872449075176367)
      ·
        refine ⟨599263991165808673612764551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399509327443872449075176367 599263991165808673612764551)
        ·
          refine ⟨898895986748713010419146827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599263991165808673612764551 898895986748713010419146827)
          ·
            refine ⟨1348343980123069515628720241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 898895986748713010419146827 1348343980123069515628720241)
            ·
              refine ⟨1011257985092302136721540181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1348343980123069515628720241 1011257985092302136721540181)
              ·
                refine ⟨11850679512800415664705549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1011257985092302136721540181 11850679512800415664705549)
                ·
                  refine ⟨4444004817300155874264581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11850679512800415664705549 4444004817300155874264581)
                  ·
                    refine ⟨833250903243779226424609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4444004817300155874264581 833250903243779226424609)
                    ·
                      rfl

theorem cell23_4868251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 3, 4].length) (baseStart_4868251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868251 prefixEnd_4868251 := by exact prefixLift 4868251
  have htrace : WordTrace (prefixWord ++ tailWord_4868251) baseStart_4868251 baseEnd_4868251 := by
    simpa [prefixWord, tailWord_4868251, baseEnd_4868251] using wordTrace_append hprefix tailTrace_4868251
  have hstable : (prefixWord ++ tailWord_4868251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868251).length < 2 ^ (prefixWord ++ tailWord_4868251).sum := by decide
  have hdescent : baseEnd_4868251 < baseStart_4868251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868258 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_4868258 : Nat := 118140960795 + 4868258 * 2 ^ 59
def prefixEnd_4868258 : Nat := 4983230072969 + 3 ^ 40 * 4868258 * 2
def baseEnd_4868258 : Nat := 2499756304095919151886295

theorem tailTrace_4868258 : CollatzResearch.WordTrace tailWord_4868258 prefixEnd_4868258 2499756304095919151886295 := by
  unfold tailWord_4868258
  simp only [CollatzResearch.WordTrace]
  refine ⟨44389989099285043279451357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118373304264760115411870285 44389989099285043279451357)
  ·
    refine ⟨16646245912231891229794259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44389989099285043279451357 16646245912231891229794259)
    ·
      refine ⟨24969368868347836844691389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16646245912231891229794259 24969368868347836844691389)
      ·
        refine ⟨9363513325630438816759271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24969368868347836844691389 9363513325630438816759271)
        ·
          refine ⟨14045269988445658225138907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9363513325630438816759271 14045269988445658225138907)
          ·
            refine ⟨21067904982668487337708361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14045269988445658225138907 21067904982668487337708361)
            ·
              refine ⟨15800928737001365503281271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21067904982668487337708361 15800928737001365503281271)
              ·
                refine ⟨23701393105502048254921907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15800928737001365503281271 23701393105502048254921907)
                ·
                  refine ⟨35552089658253072382382861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23701393105502048254921907 35552089658253072382382861)
                  ·
                    refine ⟨13332033621844902143393573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35552089658253072382382861 13332033621844902143393573)
                    ·
                      refine ⟨2499756304095919151886295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13332033621844902143393573 2499756304095919151886295)
                      ·
                        rfl

theorem cell23_4868258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_4868258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868258 prefixEnd_4868258 := by exact prefixLift 4868258
  have htrace : WordTrace (prefixWord ++ tailWord_4868258) baseStart_4868258 baseEnd_4868258 := by
    simpa [prefixWord, tailWord_4868258, baseEnd_4868258] using wordTrace_append hprefix tailTrace_4868258
  have hstable : (prefixWord ++ tailWord_4868258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868258).length < 2 ^ (prefixWord ++ tailWord_4868258).sum := by decide
  have hdescent : baseEnd_4868258 < baseStart_4868258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868261 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 1, 4, 3]
def baseStart_4868261 : Nat := 118140960795 + 4868261 * 2 ^ 59
def prefixEnd_4868261 : Nat := 4983230072969 + 3 ^ 40 * 4868261 * 2
def baseEnd_4868261 : Nat := 2499757844537882640148781

theorem tailTrace_4868261 : CollatzResearch.WordTrace tailWord_4868261 prefixEnd_4868261 2499757844537882640148781 := by
  unfold tailWord_4868261
  simp only [CollatzResearch.WordTrace]
  refine ⟨177560065816129304630164637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118373377210752869753443091 177560065816129304630164637)
  ·
    refine ⟨66585024681048489236311739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177560065816129304630164637 66585024681048489236311739)
    ·
      refine ⟨99877537021572733854467609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66585024681048489236311739 99877537021572733854467609)
      ·
        refine ⟨74908152766179550390850707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99877537021572733854467609 74908152766179550390850707)
        ·
          refine ⟨112362229149269325586276061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74908152766179550390850707 112362229149269325586276061)
          ·
            refine ⟨42135835930975997094853523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112362229149269325586276061 42135835930975997094853523)
            ·
              refine ⟨63203753896463995642280285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42135835930975997094853523 63203753896463995642280285)
              ·
                refine ⟨23701407711173998365855107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63203753896463995642280285 23701407711173998365855107)
                ·
                  refine ⟨35552111566760997548782661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23701407711173998365855107 35552111566760997548782661)
                  ·
                    refine ⟨6666020918767687040396749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35552111566760997548782661 6666020918767687040396749)
                    ·
                      refine ⟨2499757844537882640148781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6666020918767687040396749 2499757844537882640148781)
                      ·
                        rfl

theorem cell23_4868261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_4868261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868261 prefixEnd_4868261 := by exact prefixLift 4868261
  have htrace : WordTrace (prefixWord ++ tailWord_4868261) baseStart_4868261 baseEnd_4868261 := by
    simpa [prefixWord, tailWord_4868261, baseEnd_4868261] using wordTrace_append hprefix tailTrace_4868261
  have hstable : (prefixWord ++ tailWord_4868261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868261).length < 2 ^ (prefixWord ++ tailWord_4868261).sum := by decide
  have hdescent : baseEnd_4868261 < baseStart_4868261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868276 : List Nat := [2, 5, 3, 1, 1, 1, 3, 2, 5]
def baseStart_4868276 : Nat := 118140960795 + 4868276 * 2 ^ 59
def prefixEnd_4868276 : Nat := 4983230072969 + 3 ^ 40 * 4868276 * 2
def baseEnd_4868276 : Nat := 277751727416411120162357

theorem tailTrace_4868276 : CollatzResearch.WordTrace tailWord_4868276 prefixEnd_4868276 277751727416411120162357 := by
  unfold tailWord_4868276
  simp only [CollatzResearch.WordTrace]
  refine ⟨88780306455537481095980341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118373741940716641461307121 88780306455537481095980341)
  ·
    refine ⟨8323153730206638852748157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88780306455537481095980341 8323153730206638852748157)
    ·
      refine ⟨3121182648827489569780559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8323153730206638852748157 3121182648827489569780559)
      ·
        refine ⟨4681773973241234354670839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3121182648827489569780559 4681773973241234354670839)
        ·
          refine ⟨7022660959861851532006259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4681773973241234354670839 7022660959861851532006259)
          ·
            refine ⟨10533991439792777298009389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7022660959861851532006259 10533991439792777298009389)
            ·
              refine ⟨3950246789922291486753521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10533991439792777298009389 3950246789922291486753521)
              ·
                refine ⟨2962685092441718615065141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3950246789922291486753521 2962685092441718615065141)
                ·
                  refine ⟨277751727416411120162357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2962685092441718615065141 277751727416411120162357)
                  ·
                    rfl

theorem cell23_4868276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_4868276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868276 prefixEnd_4868276 := by exact prefixLift 4868276
  have htrace : WordTrace (prefixWord ++ tailWord_4868276) baseStart_4868276 baseEnd_4868276 := by
    simpa [prefixWord, tailWord_4868276, baseEnd_4868276] using wordTrace_append hprefix tailTrace_4868276
  have hstable : (prefixWord ++ tailWord_4868276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868276).length < 2 ^ (prefixWord ++ tailWord_4868276).sum := by decide
  have hdescent : baseEnd_4868276 < baseStart_4868276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868281 : List Nat := [1, 2, 1, 4, 1, 2, 2, 4, 6]
def baseStart_4868281 : Nat := 118140960795 + 4868281 * 2 ^ 59
def prefixEnd_4868281 : Nat := 4983230072969 + 3 ^ 40 * 4868281 * 2
def baseEnd_4868281 : Nat := 277752012683441395766521

theorem tailTrace_4868281 : CollatzResearch.WordTrace tailWord_4868281 prefixEnd_4868281 277752012683441395766521 := by
  unfold tailWord_4868281
  simp only [CollatzResearch.WordTrace]
  refine ⟨177560795276056848045892697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118373863517371232030595131 177560795276056848045892697)
  ·
    refine ⟨133170596457042636034419523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177560795276056848045892697 133170596457042636034419523)
    ·
      refine ⟨199755894685563954051629285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133170596457042636034419523 199755894685563954051629285)
      ·
        refine ⟨37454230253543241384680491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199755894685563954051629285 37454230253543241384680491)
        ·
          refine ⟨56181345380314862077020737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37454230253543241384680491 56181345380314862077020737)
          ·
            refine ⟨42136009035236146557765553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56181345380314862077020737 42136009035236146557765553)
            ·
              refine ⟨31602006776427109918324165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42136009035236146557765553 31602006776427109918324165)
              ·
                refine ⟨5925376270580083109685781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31602006776427109918324165 5925376270580083109685781)
                ·
                  refine ⟨277752012683441395766521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5925376270580083109685781 277752012683441395766521)
                  ·
                    rfl

theorem cell23_4868281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 6].length) (baseStart_4868281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868281 prefixEnd_4868281 := by exact prefixLift 4868281
  have htrace : WordTrace (prefixWord ++ tailWord_4868281) baseStart_4868281 baseEnd_4868281 := by
    simpa [prefixWord, tailWord_4868281, baseEnd_4868281] using wordTrace_append hprefix tailTrace_4868281
  have hstable : (prefixWord ++ tailWord_4868281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868281).length < 2 ^ (prefixWord ++ tailWord_4868281).sum := by decide
  have hdescent : baseEnd_4868281 < baseStart_4868281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868335 : List Nat := [1, 1, 2, 1, 6, 1, 2, 2, 2, 3, 2]
def baseStart_4868335 : Nat := 118140960795 + 4868335 * 2 ^ 59
def prefixEnd_4868335 : Nat := 4983230072969 + 3 ^ 40 * 4868335 * 2
def baseEnd_4868335 : Nat := 2499795842106315350623441

theorem tailTrace_4868335 : CollatzResearch.WordTrace tailWord_4868335 prefixEnd_4868335 2499795842106315350623441 := by
  unfold tailWord_4868335
  simp only [CollatzResearch.WordTrace]
  refine ⟨177562764817861215268358459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118375176545240810178905639 177562764817861215268358459)
  ·
    refine ⟨266344147226791822902537689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177562764817861215268358459 266344147226791822902537689)
    ·
      refine ⟨199758110420093867176903267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266344147226791822902537689 199758110420093867176903267)
      ·
        refine ⟨299637165630140800765354901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199758110420093867176903267 299637165630140800765354901)
        ·
          refine ⟨14045492138912850035876011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 299637165630140800765354901 14045492138912850035876011)
          ·
            refine ⟨21068238208369275053814017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14045492138912850035876011 21068238208369275053814017)
            ·
              refine ⟨15801178656276956290360513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21068238208369275053814017 15801178656276956290360513)
              ·
                refine ⟨11850883992207717217770385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15801178656276956290360513 11850883992207717217770385)
                ·
                  refine ⟨8888162994155787913327789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11850883992207717217770385 8888162994155787913327789)
                  ·
                    refine ⟨3333061122808420467497921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8888162994155787913327789 3333061122808420467497921)
                    ·
                      refine ⟨2499795842106315350623441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3333061122808420467497921 2499795842106315350623441)
                      ·
                        rfl

theorem cell23_4868335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 2, 2, 3, 2].length) (baseStart_4868335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868335 prefixEnd_4868335 := by exact prefixLift 4868335
  have htrace : WordTrace (prefixWord ++ tailWord_4868335) baseStart_4868335 baseEnd_4868335 := by
    simpa [prefixWord, tailWord_4868335, baseEnd_4868335] using wordTrace_append hprefix tailTrace_4868335
  have hstable : (prefixWord ++ tailWord_4868335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868335).length < 2 ^ (prefixWord ++ tailWord_4868335).sum := by decide
  have hdescent : baseEnd_4868335 < baseStart_4868335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868348 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 3, 1, 4]
def baseStart_4868348 : Nat := 118140960795 + 4868348 * 2 ^ 59
def prefixEnd_4868348 : Nat := 4983230072969 + 3 ^ 40 * 4868348 * 2
def baseEnd_4868348 : Nat := 2499802517354823799760881

theorem tailTrace_4868348 : CollatzResearch.WordTrace tailWord_4868348 prefixEnd_4868348 2499802517354823799760881 := by
  unfold tailWord_4868348
  simp only [CollatzResearch.WordTrace]
  refine ⟨88781619483407059244290849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118375492644542745659054465 88781619483407059244290849)
  ·
    refine ⟨66586214612555294433218137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88781619483407059244290849 66586214612555294433218137)
    ·
      refine ⟨49939660959416470824913603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66586214612555294433218137 49939660959416470824913603)
      ·
        refine ⟨74909491439124706237370405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49939660959416470824913603 74909491439124706237370405)
        ·
          refine ⟨14045529644835882419506951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74909491439124706237370405 14045529644835882419506951)
          ·
            refine ⟨21068294467253823629260427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14045529644835882419506951 21068294467253823629260427)
            ·
              refine ⟨31602441700880735443890641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21068294467253823629260427 31602441700880735443890641)
              ·
                refine ⟨23701831275660551582917981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31602441700880735443890641 23701831275660551582917981)
                ·
                  refine ⟨8888186728372706843594243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23701831275660551582917981 8888186728372706843594243)
                  ·
                    refine ⟨13332280092559060265391365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8888186728372706843594243 13332280092559060265391365)
                    ·
                      refine ⟨2499802517354823799760881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13332280092559060265391365 2499802517354823799760881)
                      ·
                        rfl

theorem cell23_4868348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_4868348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868348 prefixEnd_4868348 := by exact prefixLift 4868348
  have htrace : WordTrace (prefixWord ++ tailWord_4868348) baseStart_4868348 baseEnd_4868348 := by
    simpa [prefixWord, tailWord_4868348, baseEnd_4868348] using wordTrace_append hprefix tailTrace_4868348
  have hstable : (prefixWord ++ tailWord_4868348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868348).length < 2 ^ (prefixWord ++ tailWord_4868348).sum := by decide
  have hdescent : baseEnd_4868348 < baseStart_4868348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868351 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 5]
def baseStart_4868351 : Nat := 118140960795 + 4868351 * 2 ^ 59
def prefixEnd_4868351 : Nat := 4983230072969 + 3 ^ 40 * 4868351 * 2
def baseEnd_4868351 : Nat := 2499804057796787288023367

theorem tailTrace_4868351 : CollatzResearch.WordTrace tailWord_4868351 prefixEnd_4868351 2499804057796787288023367 := by
  unfold tailWord_4868351
  simp only [CollatzResearch.WordTrace]
  refine ⟨177563348385803250000940907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118375565590535500000627271 177563348385803250000940907)
  ·
    refine ⟨266345022578704875001411361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177563348385803250000940907 266345022578704875001411361)
    ·
      refine ⟨199758766934028656251058521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266345022578704875001411361 199758766934028656251058521)
      ·
        refine ⟨149819075200521492188293891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199758766934028656251058521 149819075200521492188293891)
        ·
          refine ⟨224728612800782238282440837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149819075200521492188293891 224728612800782238282440837)
          ·
            refine ⟨42136614900146669677957657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 224728612800782238282440837 42136614900146669677957657)
            ·
              refine ⟨31602461175110002258468243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42136614900146669677957657 31602461175110002258468243)
              ·
                refine ⟨47403691762665003387702365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31602461175110002258468243 47403691762665003387702365)
                ·
                  refine ⟨17776384410999376270388387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47403691762665003387702365 17776384410999376270388387)
                  ·
                    refine ⟨26664576616499064405582581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17776384410999376270388387 26664576616499064405582581)
                    ·
                      refine ⟨2499804057796787288023367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26664576616499064405582581 2499804057796787288023367)
                      ·
                        rfl

theorem cell23_4868351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_4868351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868351 prefixEnd_4868351 := by exact prefixLift 4868351
  have htrace : WordTrace (prefixWord ++ tailWord_4868351) baseStart_4868351 baseEnd_4868351 := by
    simpa [prefixWord, tailWord_4868351, baseEnd_4868351] using wordTrace_append hprefix tailTrace_4868351
  have hstable : (prefixWord ++ tailWord_4868351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868351).length < 2 ^ (prefixWord ++ tailWord_4868351).sum := by decide
  have hdescent : baseEnd_4868351 < baseStart_4868351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868431 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 4, 6]
def baseStart_4868431 : Nat := 118140960795 + 4868431 * 2 ^ 59
def prefixEnd_4868431 : Nat := 4983230072969 + 3 ^ 40 * 4868431 * 2
def baseEnd_4868431 : Nat := 833281712083048991674333

theorem tailTrace_4868431 : CollatzResearch.WordTrace tailWord_4868431 prefixEnd_4868431 833281712083048991674333 := by
  unfold tailWord_4868431
  simp only [CollatzResearch.WordTrace]
  refine ⟨177566266225513423663853147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118377510817008949109235431 177566266225513423663853147)
  ·
    refine ⟨266349399338270135495779721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177566266225513423663853147 266349399338270135495779721)
    ·
      refine ⟨199762049503702601621834791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266349399338270135495779721 199762049503702601621834791)
      ·
        refine ⟨299643074255553902432752187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199762049503702601621834791 299643074255553902432752187)
        ·
          refine ⟨449464611383330853649128281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299643074255553902432752187 449464611383330853649128281)
          ·
            refine ⟨337098458537498140236846211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 449464611383330853649128281 337098458537498140236846211)
            ·
              refine ⟨505647687806247210355269317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337098458537498140236846211 505647687806247210355269317)
              ·
                refine ⟨94808941463671351941612997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 505647687806247210355269317 94808941463671351941612997)
                ·
                  refine ⟨17776676524438378489052437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94808941463671351941612997 17776676524438378489052437)
                  ·
                    refine ⟨833281712083048991674333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17776676524438378489052437 833281712083048991674333)
                    ·
                      rfl

theorem cell23_4868431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 6].length) (baseStart_4868431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868431 prefixEnd_4868431 := by exact prefixLift 4868431
  have htrace : WordTrace (prefixWord ++ tailWord_4868431) baseStart_4868431 baseEnd_4868431 := by
    simpa [prefixWord, tailWord_4868431, baseEnd_4868431] using wordTrace_append hprefix tailTrace_4868431
  have hstable : (prefixWord ++ tailWord_4868431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868431).length < 2 ^ (prefixWord ++ tailWord_4868431).sum := by decide
  have hdescent : baseEnd_4868431 < baseStart_4868431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868512 : List Nat := [2, 1, 1, 4, 1, 3, 4, 2, 5]
def baseStart_4868512 : Nat := 118140960795 + 4868512 * 2 ^ 59
def prefixEnd_4868512 : Nat := 4983230072969 + 3 ^ 40 * 4868512 * 2
def baseEnd_4868512 : Nat := 277765192020240128678903

theorem tailTrace_4868512 : CollatzResearch.WordTrace tailWord_4868512 prefixEnd_4868512 277765192020240128678903 := by
  unfold tailWord_4868512
  simp only [CollatzResearch.WordTrace]
  refine ⟨88784610269109987248775895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118379480358813316331701193 88784610269109987248775895)
  ·
    refine ⟨133176915403664980873163843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88784610269109987248775895 133176915403664980873163843)
    ·
      refine ⟨199765373105497471309745765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133176915403664980873163843 199765373105497471309745765)
      ·
        refine ⟨37456007457280775870577331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199765373105497471309745765 37456007457280775870577331)
        ·
          refine ⟨56184011185921163805865997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37456007457280775870577331 56184011185921163805865997)
          ·
            refine ⟨21069004194720436427199749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56184011185921163805865997 21069004194720436427199749)
            ·
              refine ⟨3950438286510081830099953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21069004194720436427199749 3950438286510081830099953)
              ·
                refine ⟨2962828714882561372574965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3950438286510081830099953 2962828714882561372574965)
                ·
                  refine ⟨277765192020240128678903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2962828714882561372574965 277765192020240128678903)
                  ·
                    rfl

theorem cell23_4868512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 2, 5].length) (baseStart_4868512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868512 prefixEnd_4868512 := by exact prefixLift 4868512
  have htrace : WordTrace (prefixWord ++ tailWord_4868512) baseStart_4868512 baseEnd_4868512 := by
    simpa [prefixWord, tailWord_4868512, baseEnd_4868512] using wordTrace_append hprefix tailTrace_4868512
  have hstable : (prefixWord ++ tailWord_4868512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868512).length < 2 ^ (prefixWord ++ tailWord_4868512).sum := by decide
  have hdescent : baseEnd_4868512 < baseStart_4868512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868515 : List Nat := [1, 1, 1, 4, 1, 4, 1, 1, 2, 5, 2]
def baseStart_4868515 : Nat := 118140960795 + 4868515 * 2 ^ 59
def prefixEnd_4868515 : Nat := 4983230072969 + 3 ^ 40 * 4868515 * 2
def baseEnd_4868515 : Nat := 2499888268624124646372613

theorem tailTrace_4868515 : CollatzResearch.WordTrace tailWord_4868515 prefixEnd_4868515 2499888268624124646372613 := by
  unfold tailWord_4868515
  simp only [CollatzResearch.WordTrace]
  refine ⟨177569329957209106009910999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118379553304806070673273999 177569329957209106009910999)
  ·
    refine ⟨266353994935813659014866499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177569329957209106009910999 266353994935813659014866499)
    ·
      refine ⟨399530992403720488522299749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266353994935813659014866499 399530992403720488522299749)
      ·
        refine ⟨74912061075697591597931203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 399530992403720488522299749 74912061075697591597931203)
        ·
          refine ⟨112368091613546387396896805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74912061075697591597931203 112368091613546387396896805)
          ·
            refine ⟨21069017177539947636918151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112368091613546387396896805 21069017177539947636918151)
            ·
              refine ⟨31603525766309921455377227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21069017177539947636918151 31603525766309921455377227)
              ·
                refine ⟨47405288649464882183065841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31603525766309921455377227 47405288649464882183065841)
                ·
                  refine ⟨35553966487098661637299381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47405288649464882183065841 35553966487098661637299381)
                  ·
                    refine ⟨3333184358165499528496817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35553966487098661637299381 3333184358165499528496817)
                    ·
                      refine ⟨2499888268624124646372613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3333184358165499528496817 2499888268624124646372613)
                      ·
                        rfl

theorem cell23_4868515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_4868515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868515 prefixEnd_4868515 := by exact prefixLift 4868515
  have htrace : WordTrace (prefixWord ++ tailWord_4868515) baseStart_4868515 baseEnd_4868515 := by
    simpa [prefixWord, tailWord_4868515, baseEnd_4868515] using wordTrace_append hprefix tailTrace_4868515
  have hstable : (prefixWord ++ tailWord_4868515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868515).length < 2 ^ (prefixWord ++ tailWord_4868515).sum := by decide
  have hdescent : baseEnd_4868515 < baseStart_4868515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868588 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 6]
def baseStart_4868588 : Nat := 118140960795 + 4868588 * 2 ^ 59
def prefixEnd_4868588 : Nat := 4983230072969 + 3 ^ 40 * 4868588 * 2
def baseEnd_4868588 : Nat := 2499925752711902860759777

theorem tailTrace_4868588 : CollatzResearch.WordTrace tailWord_4868588 prefixEnd_4868588 2499925752711902860759777 := by
  unfold tailWord_4868588
  simp only [CollatzResearch.WordTrace]
  refine ⟨88785996242972319738659209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118381328323963092984878945 88785996242972319738659209)
  ·
    refine ⟨66589497182229239803994407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88785996242972319738659209 66589497182229239803994407)
    ·
      refine ⟨99884245773343859705991611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66589497182229239803994407 99884245773343859705991611)
      ·
        refine ⟨149826368660015789558987417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99884245773343859705991611 149826368660015789558987417)
        ·
          refine ⟨112369776495011842169240563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149826368660015789558987417 112369776495011842169240563)
          ·
            refine ⟨168554664742517763253860845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112369776495011842169240563 168554664742517763253860845)
            ·
              refine ⟨63207999278444161220197817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168554664742517763253860845 63207999278444161220197817)
              ·
                refine ⟨47405999458833120915148363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63207999278444161220197817 47405999458833120915148363)
                ·
                  refine ⟨71108999188249681372722545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47405999458833120915148363 71108999188249681372722545)
                  ·
                    refine ⟨53331749391187261029541909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71108999188249681372722545 53331749391187261029541909)
                    ·
                      refine ⟨2499925752711902860759777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53331749391187261029541909 2499925752711902860759777)
                      ·
                        rfl

theorem cell23_4868588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_4868588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868588 prefixEnd_4868588 := by exact prefixLift 4868588
  have htrace : WordTrace (prefixWord ++ tailWord_4868588) baseStart_4868588 baseEnd_4868588 := by
    simpa [prefixWord, tailWord_4868588, baseEnd_4868588] using wordTrace_append hprefix tailTrace_4868588
  have hstable : (prefixWord ++ tailWord_4868588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868588).length < 2 ^ (prefixWord ++ tailWord_4868588).sum := by decide
  have hdescent : baseEnd_4868588 < baseStart_4868588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868662 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_4868662 : Nat := 118140960795 + 4868662 * 2 ^ 59
def prefixEnd_4868662 : Nat := 4983230072969 + 3 ^ 40 * 4868662 * 2
def baseEnd_4868662 : Nat := 833321250093445190411479

theorem tailTrace_4868662 : CollatzResearch.WordTrace tailWord_4868662 prefixEnd_4868662 833321250093445190411479 := by
  unfold tailWord_4868662
  simp only [CollatzResearch.WordTrace]
  refine ⟨11098418217979784382219515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118383127658451033410341493 11098418217979784382219515)
  ·
    refine ⟨16647627326969676573329273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11098418217979784382219515 16647627326969676573329273)
    ·
      refine ⟨12485720495227257429996955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16647627326969676573329273 12485720495227257429996955)
      ·
        refine ⟨18728580742840886144995433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12485720495227257429996955 18728580742840886144995433)
        ·
          refine ⟨14046435557130664608746575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18728580742840886144995433 14046435557130664608746575)
          ·
            refine ⟨21069653335695996913119863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14046435557130664608746575 21069653335695996913119863)
            ·
              refine ⟨31604480003543995369679795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21069653335695996913119863 31604480003543995369679795)
              ·
                refine ⟨47406720005315993054519693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31604480003543995369679795 47406720005315993054519693)
                ·
                  refine ⟨17777520001993497395444885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47406720005315993054519693 17777520001993497395444885)
                  ·
                    refine ⟨833321250093445190411479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17777520001993497395444885 833321250093445190411479)
                    ·
                      rfl

theorem cell23_4868662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_4868662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868662 prefixEnd_4868662 := by exact prefixLift 4868662
  have htrace : WordTrace (prefixWord ++ tailWord_4868662) baseStart_4868662 baseEnd_4868662 := by
    simpa [prefixWord, tailWord_4868662, baseEnd_4868662] using wordTrace_append hprefix tailTrace_4868662
  have hstable : (prefixWord ++ tailWord_4868662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868662).length < 2 ^ (prefixWord ++ tailWord_4868662).sum := by decide
  have hdescent : baseEnd_4868662 < baseStart_4868662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868672 : List Nat := [2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 3]
def baseStart_4868672 : Nat := 118140960795 + 4868672 * 2 ^ 59
def prefixEnd_4868672 : Nat := 4983230072969 + 3 ^ 40 * 4868672 * 2
def baseEnd_4868672 : Nat := 2499968885086880532109391

theorem tailTrace_4868672 : CollatzResearch.WordTrace tailWord_4868672 prefixEnd_4868672 2499968885086880532109391 := by
  unfold tailWord_4868672
  simp only [CollatzResearch.WordTrace]
  refine ⟨88787528108820160911688135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118383370811760214548917513 88787528108820160911688135)
  ·
    refine ⟨133181292163230241367532203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88787528108820160911688135 133181292163230241367532203)
    ·
      refine ⟨199771938244845362051298305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133181292163230241367532203 199771938244845362051298305)
      ·
        refine ⟨149828953683634021538473729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199771938244845362051298305 149828953683634021538473729)
        ·
          refine ⟨112371715262725516153855297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149828953683634021538473729 112371715262725516153855297)
          ·
            refine ⟨84278786447044137115391473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112371715262725516153855297 84278786447044137115391473)
            ·
              refine ⟨63209089835283102836543605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84278786447044137115391473 63209089835283102836543605)
              ·
                refine ⟨5925852172057790890925963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63209089835283102836543605 5925852172057790890925963)
                ·
                  refine ⟨8888778258086686336388945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5925852172057790890925963 8888778258086686336388945)
                  ·
                    refine ⟨6666583693565014752291709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8888778258086686336388945 6666583693565014752291709)
                    ·
                      refine ⟨2499968885086880532109391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6666583693565014752291709 2499968885086880532109391)
                      ·
                        rfl

theorem cell23_4868672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 3].length) (baseStart_4868672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868672 prefixEnd_4868672 := by exact prefixLift 4868672
  have htrace : WordTrace (prefixWord ++ tailWord_4868672) baseStart_4868672 baseEnd_4868672 := by
    simpa [prefixWord, tailWord_4868672, baseEnd_4868672] using wordTrace_append hprefix tailTrace_4868672
  have hstable : (prefixWord ++ tailWord_4868672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868672).length < 2 ^ (prefixWord ++ tailWord_4868672).sum := by decide
  have hdescent : baseEnd_4868672 < baseStart_4868672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868679 : List Nat := [1, 1, 4, 1, 4, 2, 2, 2, 2, 4]
def baseStart_4868679 : Nat := 118140960795 + 4868679 * 2 ^ 59
def prefixEnd_4868679 : Nat := 4983230072969 + 3 ^ 40 * 4868679 * 2
def baseEnd_4868679 : Nat := 833324159817154001573953

theorem tailTrace_4868679 : CollatzResearch.WordTrace tailWord_4868679 prefixEnd_4868679 833324159817154001573953 := by
  unfold tailWord_4868679
  simp only [CollatzResearch.WordTrace]
  refine ⟨177575311528614962018881091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118383541019076641345920727 177575311528614962018881091)
  ·
    refine ⟨266362967292922443028321637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177575311528614962018881091 266362967292922443028321637)
    ·
      refine ⟨49943056367422958067810307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266362967292922443028321637 49943056367422958067810307)
      ·
        refine ⟨74914584551134437101715461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49943056367422958067810307 74914584551134437101715461)
        ·
          refine ⟨14046484603337706956571649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74914584551134437101715461 14046484603337706956571649)
          ·
            refine ⟨10534863452503280217428737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14046484603337706956571649 10534863452503280217428737)
            ·
              refine ⟨7901147589377460163071553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10534863452503280217428737 7901147589377460163071553)
              ·
                refine ⟨5925860692033095122303665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7901147589377460163071553 5925860692033095122303665)
                ·
                  refine ⟨4444395519024821341727749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5925860692033095122303665 4444395519024821341727749)
                  ·
                    refine ⟨833324159817154001573953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4444395519024821341727749 833324159817154001573953)
                    ·
                      rfl

theorem cell23_4868679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_4868679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868679 prefixEnd_4868679 := by exact prefixLift 4868679
  have htrace : WordTrace (prefixWord ++ tailWord_4868679) baseStart_4868679 baseEnd_4868679 := by
    simpa [prefixWord, tailWord_4868679, baseEnd_4868679] using wordTrace_append hprefix tailTrace_4868679
  have hstable : (prefixWord ++ tailWord_4868679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868679).length < 2 ^ (prefixWord ++ tailWord_4868679).sum := by decide
  have hdescent : baseEnd_4868679 < baseStart_4868679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868692 : List Nat := [2, 4, 1, 1, 1, 5, 1, 8]
def baseStart_4868692 : Nat := 118140960795 + 4868692 * 2 ^ 59
def prefixEnd_4868692 : Nat := 4983230072969 + 3 ^ 40 * 4868692 * 2
def baseEnd_4868692 : Nat := 92591820544443350142937

theorem tailTrace_4868692 : CollatzResearch.WordTrace tailWord_4868692 prefixEnd_4868692 92591820544443350142937 := by
  unfold tailWord_4868692
  simp only [CollatzResearch.WordTrace]
  refine ⟨88787892838783932619552165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118383857118378576826069553 88787892838783932619552165)
  ·
    refine ⟨16647729907271987366166031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88787892838783932619552165 16647729907271987366166031)
    ·
      refine ⟨24971594860907981049249047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16647729907271987366166031 24971594860907981049249047)
      ·
        refine ⟨37457392291361971573873571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24971594860907981049249047 37457392291361971573873571)
        ·
          refine ⟨56186088437042957360810357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37457392291361971573873571 56186088437042957360810357)
          ·
            refine ⟨5267445790972777252575971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56186088437042957360810357 5267445790972777252575971)
            ·
              refine ⟨7901168686459165878863957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5267445790972777252575971 7901168686459165878863957)
              ·
                refine ⟨92591820544443350142937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7901168686459165878863957 92591820544443350142937)
                ·
                  rfl

theorem cell23_4868692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 8].length) (baseStart_4868692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868692 prefixEnd_4868692 := by exact prefixLift 4868692
  have htrace : WordTrace (prefixWord ++ tailWord_4868692) baseStart_4868692 baseEnd_4868692 := by
    simpa [prefixWord, tailWord_4868692, baseEnd_4868692] using wordTrace_append hprefix tailTrace_4868692
  have hstable : (prefixWord ++ tailWord_4868692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868692).length < 2 ^ (prefixWord ++ tailWord_4868692).sum := by decide
  have hdescent : baseEnd_4868692 < baseStart_4868692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868736 : List Nat := [2, 1, 1, 2, 1, 7, 1, 2, 2, 1, 3]
def baseStart_4868736 : Nat := 118140960795 + 4868736 * 2 ^ 59
def prefixEnd_4868736 : Nat := 4983230072969 + 3 ^ 40 * 4868736 * 2
def baseEnd_4868736 : Nat := 2500001747848768281709097

theorem tailTrace_4868736 : CollatzResearch.WordTrace tailWord_4868736 prefixEnd_4868736 2500001747848768281709097 := by
  unfold tailWord_4868736
  simp only [CollatzResearch.WordTrace]
  refine ⟨88788695244704230376853031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118384926992938973835804041 88788695244704230376853031)
  ·
    refine ⟨133183042867056345565279547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88788695244704230376853031 133183042867056345565279547)
    ·
      refine ⟨199774564300584518347919321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133183042867056345565279547 199774564300584518347919321)
      ·
        refine ⟨149830923225438388760939491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199774564300584518347919321 149830923225438388760939491)
        ·
          refine ⟨224746384838157583141409237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149830923225438388760939491 224746384838157583141409237)
          ·
            refine ⟨5267493394644318354876779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 224746384838157583141409237 5267493394644318354876779)
            ·
              refine ⟨7901240091966477532315169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5267493394644318354876779 7901240091966477532315169)
              ·
                refine ⟨5925930068974858149236377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7901240091966477532315169 5925930068974858149236377)
                ·
                  refine ⟨4444447551731143611927283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5925930068974858149236377 4444447551731143611927283)
                  ·
                    refine ⟨6666671327596715417890925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4444447551731143611927283 6666671327596715417890925)
                    ·
                      refine ⟨2500001747848768281709097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6666671327596715417890925 2500001747848768281709097)
                      ·
                        rfl

theorem cell23_4868736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 2, 1, 3].length) (baseStart_4868736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868736 prefixEnd_4868736 := by exact prefixLift 4868736
  have htrace : WordTrace (prefixWord ++ tailWord_4868736) baseStart_4868736 baseEnd_4868736 := by
    simpa [prefixWord, tailWord_4868736, baseEnd_4868736] using wordTrace_append hprefix tailTrace_4868736
  have hstable : (prefixWord ++ tailWord_4868736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868736).length < 2 ^ (prefixWord ++ tailWord_4868736).sum := by decide
  have hdescent : baseEnd_4868736 < baseStart_4868736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868745 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 4, 1, 5]
def baseStart_4868745 : Nat := 118140960795 + 4868745 * 2 ^ 59
def prefixEnd_4868745 : Nat := 4983230072969 + 3 ^ 40 * 4868745 * 2
def baseEnd_4868745 : Nat := 2500006369174658746496555

theorem tailTrace_4868745 : CollatzResearch.WordTrace tailWord_4868745 prefixEnd_4868745 2500006369174658746496555 := by
  unfold tailWord_4868745
  simp only [CollatzResearch.WordTrace]
  refine ⟨177577718746375855290783689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118385145830917236860522459 177577718746375855290783689)
  ·
    refine ⟨133183289059781891468087767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177577718746375855290783689 133183289059781891468087767)
    ·
      refine ⟨199774933589672837202131651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133183289059781891468087767 199774933589672837202131651)
      ·
        refine ⟨299662400384509255803197477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199774933589672837202131651 299662400384509255803197477)
        ·
          refine ⟨56186700072095485463099527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 299662400384509255803197477 56186700072095485463099527)
          ·
            refine ⟨84280050108143228194649291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56186700072095485463099527 84280050108143228194649291)
            ·
              refine ⟨126420075162214842291973937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84280050108143228194649291 126420075162214842291973937)
              ·
                refine ⟨94815056371661131718980453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126420075162214842291973937 94815056371661131718980453)
                ·
                  refine ⟨17777823069686462197308835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94815056371661131718980453 17777823069686462197308835)
                  ·
                    refine ⟨26666734604529693295963253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17777823069686462197308835 26666734604529693295963253)
                    ·
                      refine ⟨2500006369174658746496555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26666734604529693295963253 2500006369174658746496555)
                      ·
                        rfl

theorem cell23_4868745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 1, 5].length) (baseStart_4868745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868745 prefixEnd_4868745 := by exact prefixLift 4868745
  have htrace : WordTrace (prefixWord ++ tailWord_4868745) baseStart_4868745 baseEnd_4868745 := by
    simpa [prefixWord, tailWord_4868745, baseEnd_4868745] using wordTrace_append hprefix tailTrace_4868745
  have hstable : (prefixWord ++ tailWord_4868745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868745).length < 2 ^ (prefixWord ++ tailWord_4868745).sum := by decide
  have hdescent : baseEnd_4868745 < baseStart_4868745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868810 : List Nat := [3, 1, 2, 1, 4, 3, 2, 1, 2, 2, 2]
def baseStart_4868810 : Nat := 118140960795 + 4868810 * 2 ^ 59
def prefixEnd_4868810 : Nat := 4983230072969 + 3 ^ 40 * 4868810 * 2
def baseEnd_4868810 : Nat := 2500039745417200992183757

theorem tailTrace_4868810 : CollatzResearch.WordTrace tailWord_4868810 prefixEnd_4868810 2500039745417200992183757 := by
  unfold tailWord_4868810
  simp only [CollatzResearch.WordTrace]
  refine ⟨44395022372785092847974971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118386726327426914261266589 44395022372785092847974971)
  ·
    refine ⟨66592533559177639271962457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44395022372785092847974971 66592533559177639271962457)
    ·
      refine ⟨49944400169383229453971843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66592533559177639271962457 49944400169383229453971843)
      ·
        refine ⟨74916600254074844180957765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49944400169383229453971843 74916600254074844180957765)
        ·
          refine ⟨14046862547639033283929581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74916600254074844180957765 14046862547639033283929581)
          ·
            refine ⟨5267573455364637481473593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14046862547639033283929581 5267573455364637481473593)
            ·
              refine ⟨3950680091523478111105195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5267573455364637481473593 3950680091523478111105195)
              ·
                refine ⟨5926020137285217166657793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3950680091523478111105195 5926020137285217166657793)
                ·
                  refine ⟨4444515102963912874993345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5926020137285217166657793 4444515102963912874993345)
                  ·
                    refine ⟨3333386327222934656245009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4444515102963912874993345 3333386327222934656245009)
                    ·
                      refine ⟨2500039745417200992183757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3333386327222934656245009 2500039745417200992183757)
                      ·
                        rfl

theorem cell23_4868810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_4868810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868810 prefixEnd_4868810 := by exact prefixLift 4868810
  have htrace : WordTrace (prefixWord ++ tailWord_4868810) baseStart_4868810 baseEnd_4868810 := by
    simpa [prefixWord, tailWord_4868810, baseEnd_4868810] using wordTrace_append hprefix tailTrace_4868810
  have hstable : (prefixWord ++ tailWord_4868810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868810).length < 2 ^ (prefixWord ++ tailWord_4868810).sum := by decide
  have hdescent : baseEnd_4868810 < baseStart_4868810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868849 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 2, 4, 2]
def baseStart_4868849 : Nat := 118140960795 + 4868849 * 2 ^ 59
def prefixEnd_4868849 : Nat := 4983230072969 + 3 ^ 40 * 4868849 * 2
def baseEnd_4868849 : Nat := 2500059771162726339596077

theorem tailTrace_4868849 : CollatzResearch.WordTrace tailWord_4868849 prefixEnd_4868849 2500059771162726339596077 := by
  unfold tailWord_4868849
  simp only [CollatzResearch.WordTrace]
  refine ⟨177581511937999081052569601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118387674625332720701713067 177581511937999081052569601)
  ·
    refine ⟨133186133953499310789427201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177581511937999081052569601 133186133953499310789427201)
    ·
      refine ⟨99889600465124483092070401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133186133953499310789427201 99889600465124483092070401)
      ·
        refine ⟨74917200348843362319052801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99889600465124483092070401 74917200348843362319052801)
        ·
          refine ⟨56187900261632521739289601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74917200348843362319052801 56187900261632521739289601)
          ·
            refine ⟨42140925196224391304467201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56187900261632521739289601 42140925196224391304467201)
            ·
              refine ⟨31605693897168293478350401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42140925196224391304467201 31605693897168293478350401)
              ·
                refine ⟨23704270422876220108762801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31605693897168293478350401 23704270422876220108762801)
                ·
                  refine ⟨17778202817157165081572101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23704270422876220108762801 17778202817157165081572101)
                  ·
                    refine ⟨3333413028216968452794769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17778202817157165081572101 3333413028216968452794769)
                    ·
                      refine ⟨2500059771162726339596077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3333413028216968452794769 2500059771162726339596077)
                      ·
                        rfl

theorem cell23_4868849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_4868849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868849 prefixEnd_4868849 := by exact prefixLift 4868849
  have htrace : WordTrace (prefixWord ++ tailWord_4868849) baseStart_4868849 baseEnd_4868849 := by
    simpa [prefixWord, tailWord_4868849, baseEnd_4868849] using wordTrace_append hprefix tailTrace_4868849
  have hstable : (prefixWord ++ tailWord_4868849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868849).length < 2 ^ (prefixWord ++ tailWord_4868849).sum := by decide
  have hdescent : baseEnd_4868849 < baseStart_4868849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868866 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_4868866 : Nat := 118140960795 + 4868866 * 2 ^ 59
def prefixEnd_4868866 : Nat := 4983230072969 + 3 ^ 40 * 4868866 * 2
def baseEnd_4868866 : Nat := 2500068500333852773083499

theorem tailTrace_4868866 : CollatzResearch.WordTrace tailWord_4868866 prefixEnd_4868866 2500068500333852773083499 := by
  unfold tailWord_4868866
  simp only [CollatzResearch.WordTrace]
  refine ⟨44395532994734373238984613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118388087985958328637292301 44395532994734373238984613)
  ·
    refine ⟨8324162436512694982309615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44395532994734373238984613 8324162436512694982309615)
    ·
      refine ⟨12486243654769042473464423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8324162436512694982309615 12486243654769042473464423)
      ·
        refine ⟨18729365482153563710196635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12486243654769042473464423 18729365482153563710196635)
        ·
          refine ⟨28094048223230345565294953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18729365482153563710196635 28094048223230345565294953)
          ·
            refine ⟨21070536167422759173971215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28094048223230345565294953 21070536167422759173971215)
            ·
              refine ⟨31605804251134138760956823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21070536167422759173971215 31605804251134138760956823)
              ·
                refine ⟨47408706376701208141435235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31605804251134138760956823 47408706376701208141435235)
                ·
                  refine ⟨71113059565051812212152853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47408706376701208141435235 71113059565051812212152853)
                  ·
                    refine ⟨3333424667111803697444665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71113059565051812212152853 3333424667111803697444665)
                    ·
                      refine ⟨2500068500333852773083499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3333424667111803697444665 2500068500333852773083499)
                      ·
                        rfl

theorem cell23_4868866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_4868866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868866 prefixEnd_4868866 := by exact prefixLift 4868866
  have htrace : WordTrace (prefixWord ++ tailWord_4868866) baseStart_4868866 baseEnd_4868866 := by
    simpa [prefixWord, tailWord_4868866, baseEnd_4868866] using wordTrace_append hprefix tailTrace_4868866
  have hstable : (prefixWord ++ tailWord_4868866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868866).length < 2 ^ (prefixWord ++ tailWord_4868866).sum := by decide
  have hdescent : baseEnd_4868866 < baseStart_4868866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868899 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 7, 1, 3]
def baseStart_4868899 : Nat := 118140960795 + 4868899 * 2 ^ 59
def prefixEnd_4868899 : Nat := 4983230072969 + 3 ^ 40 * 4868899 * 2
def baseEnd_4868899 : Nat := 2500085445195451143970847

theorem tailTrace_4868899 : CollatzResearch.WordTrace tailWord_4868899 prefixEnd_4868899 2500085445195451143970847 := by
  unfold tailWord_4868899
  simp only [CollatzResearch.WordTrace]
  refine ⟨177583335587817939591889751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118388890391878626394593167 177583335587817939591889751)
  ·
    refine ⟨266375003381726909387834627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177583335587817939591889751 266375003381726909387834627)
    ·
      refine ⟨399562505072590364081751941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266375003381726909387834627 399562505072590364081751941)
      ·
        refine ⟨74917969701110693265328489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 399562505072590364081751941 74917969701110693265328489)
        ·
          refine ⟨56188477275833019948996367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74917969701110693265328489 56188477275833019948996367)
          ·
            refine ⟨84282715913749529923494551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56188477275833019948996367 84282715913749529923494551)
            ·
              refine ⟨126424073870624294885241827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84282715913749529923494551 126424073870624294885241827)
              ·
                refine ⟨189636110805936442327862741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126424073870624294885241827 189636110805936442327862741)
                ·
                  refine ⟨4444596347014135367059283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 189636110805936442327862741 4444596347014135367059283)
                  ·
                    refine ⟨6666894520521203050588925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4444596347014135367059283 6666894520521203050588925)
                    ·
                      refine ⟨2500085445195451143970847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6666894520521203050588925 2500085445195451143970847)
                      ·
                        rfl

theorem cell23_4868899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_4868899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868899 prefixEnd_4868899 := by exact prefixLift 4868899
  have htrace : WordTrace (prefixWord ++ tailWord_4868899) baseStart_4868899 baseEnd_4868899 := by
    simpa [prefixWord, tailWord_4868899, baseEnd_4868899] using wordTrace_append hprefix tailTrace_4868899
  have hstable : (prefixWord ++ tailWord_4868899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868899).length < 2 ^ (prefixWord ++ tailWord_4868899).sum := by decide
  have hdescent : baseEnd_4868899 < baseStart_4868899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868906 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 8]
def baseStart_4868906 : Nat := 118140960795 + 4868906 * 2 ^ 59
def prefixEnd_4868906 : Nat := 4983230072969 + 3 ^ 40 * 4868906 * 2
def baseEnd_4868906 : Nat := 277787671062225846287035

theorem tailTrace_4868906 : CollatzResearch.WordTrace tailWord_4868906 prefixEnd_4868906 277787671062225846287035 := by
  unfold tailWord_4868906
  simp only [CollatzResearch.WordTrace]
  refine ⟨44395897724698144946848643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118389060599195053191596381 44395897724698144946848643)
  ·
    refine ⟨66593846587047217420272965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44395897724698144946848643 66593846587047217420272965)
    ·
      refine ⟨12486346235071353266301181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66593846587047217420272965 12486346235071353266301181)
      ·
        refine ⟨4682379838151757474862943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12486346235071353266301181 4682379838151757474862943)
        ·
          refine ⟨7023569757227636212294415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4682379838151757474862943 7023569757227636212294415)
          ·
            refine ⟨10535354635841454318441623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7023569757227636212294415 10535354635841454318441623)
            ·
              refine ⟨15803031953762181477662435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10535354635841454318441623 15803031953762181477662435)
              ·
                refine ⟨23704547930643272216493653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15803031953762181477662435 23704547930643272216493653)
                ·
                  refine ⟨277787671062225846287035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23704547930643272216493653 277787671062225846287035)
                  ·
                    rfl

theorem cell23_4868906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 8].length) (baseStart_4868906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868906 prefixEnd_4868906 := by exact prefixLift 4868906
  have htrace : WordTrace (prefixWord ++ tailWord_4868906) baseStart_4868906 baseEnd_4868906 := by
    simpa [prefixWord, tailWord_4868906, baseEnd_4868906] using wordTrace_append hprefix tailTrace_4868906
  have hstable : (prefixWord ++ tailWord_4868906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868906).length < 2 ^ (prefixWord ++ tailWord_4868906).sum := by decide
  have hdescent : baseEnd_4868906 < baseStart_4868906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868949 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 6, 4]
def baseStart_4868949 : Nat := 118140960795 + 4868949 * 2 ^ 59
def prefixEnd_4868949 : Nat := 4983230072969 + 3 ^ 40 * 4868949 * 2
def baseEnd_4868949 : Nat := 833370373076058649448539

theorem tailTrace_4868949 : CollatzResearch.WordTrace tailWord_4868949 prefixEnd_4868949 833370373076058649448539 := by
  unfold tailWord_4868949
  simp only [CollatzResearch.WordTrace]
  refine ⟨177585159237636798131209901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118390106158424532087473267 177585159237636798131209901)
  ·
    refine ⟨66594434714113799299203713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177585159237636798131209901 66594434714113799299203713)
    ·
      refine ⟨49945826035585349474402785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66594434714113799299203713 49945826035585349474402785)
      ·
        refine ⟨37459369526689012105802089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49945826035585349474402785 37459369526689012105802089)
        ·
          refine ⟨28094527145016759079351567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37459369526689012105802089 28094527145016759079351567)
          ·
            refine ⟨42141790717525138619027351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28094527145016759079351567 42141790717525138619027351)
            ·
              refine ⟨63212686076287707928541027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42141790717525138619027351 63212686076287707928541027)
              ·
                refine ⟨94819029114431561892811541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63212686076287707928541027 94819029114431561892811541)
                ·
                  refine ⟨4444641989738979463725541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94819029114431561892811541 4444641989738979463725541)
                  ·
                    refine ⟨833370373076058649448539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4444641989738979463725541 833370373076058649448539)
                    ·
                      rfl

theorem cell23_4868949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_4868949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868949 prefixEnd_4868949 := by exact prefixLift 4868949
  have htrace : WordTrace (prefixWord ++ tailWord_4868949) baseStart_4868949 baseEnd_4868949 := by
    simpa [prefixWord, tailWord_4868949, baseEnd_4868949] using wordTrace_append hprefix tailTrace_4868949
  have hstable : (prefixWord ++ tailWord_4868949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868949).length < 2 ^ (prefixWord ++ tailWord_4868949).sum := by decide
  have hdescent : baseEnd_4868949 < baseStart_4868949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868959 : List Nat := [1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 5]
def baseStart_4868959 : Nat := 118140960795 + 4868959 * 2 ^ 59
def prefixEnd_4868959 : Nat := 4983230072969 + 3 ^ 40 * 4868959 * 2
def baseEnd_4868959 : Nat := 2500116254034720909220571

theorem tailTrace_4868959 : CollatzResearch.WordTrace tailWord_4868959 prefixEnd_4868959 2500116254034720909220571 := by
  unfold tailWord_4868959
  simp only [CollatzResearch.WordTrace]
  refine ⟨177585523967600569839073931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118390349311733713226049287 177585523967600569839073931)
  ·
    refine ⟨266378285951400854758610897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177585523967600569839073931 266378285951400854758610897)
    ·
      refine ⟨199783714463550641068958173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266378285951400854758610897 199783714463550641068958173)
      ·
        refine ⟨74918892923831490400859315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199783714463550641068958173 74918892923831490400859315)
        ·
          refine ⟨112378339385747235601288973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74918892923831490400859315 112378339385747235601288973)
          ·
            refine ⟨42141877269655213350483365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112378339385747235601288973 42141877269655213350483365)
            ·
              refine ⟨7901601988060352503215631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42141877269655213350483365 7901601988060352503215631)
              ·
                refine ⟨11852402982090528754823447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7901601988060352503215631 11852402982090528754823447)
                ·
                  refine ⟨17778604473135793132235171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11852402982090528754823447 17778604473135793132235171)
                  ·
                    refine ⟨26667906709703689698352757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17778604473135793132235171 26667906709703689698352757)
                    ·
                      refine ⟨2500116254034720909220571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26667906709703689698352757 2500116254034720909220571)
                      ·
                        rfl

theorem cell23_4868959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_4868959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868959 prefixEnd_4868959 := by exact prefixLift 4868959
  have htrace : WordTrace (prefixWord ++ tailWord_4868959) baseStart_4868959 baseEnd_4868959 := by
    simpa [prefixWord, tailWord_4868959, baseEnd_4868959] using wordTrace_append hprefix tailTrace_4868959
  have hstable : (prefixWord ++ tailWord_4868959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868959).length < 2 ^ (prefixWord ++ tailWord_4868959).sum := by decide
  have hdescent : baseEnd_4868959 < baseStart_4868959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4868992 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 4, 7]
def baseStart_4868992 : Nat := 118140960795 + 4868992 * 2 ^ 59
def prefixEnd_4868992 : Nat := 4983230072969 + 3 ^ 40 * 4868992 * 2
def baseEnd_4868992 : Nat := 833377732965439760035973

theorem tailTrace_4868992 : CollatzResearch.WordTrace tailWord_4868992 prefixEnd_4868992 833377732965439760035973 := by
  unfold tailWord_4868992
  simp only [CollatzResearch.WordTrace]
  refine ⟨88793363788240508237512615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118391151717654010983350153 88793363788240508237512615)
  ·
    refine ⟨133190045682360762356268923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88793363788240508237512615 133190045682360762356268923)
    ·
      refine ⟨199785068523541143534403385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133190045682360762356268923 199785068523541143534403385)
      ·
        refine ⟨149838801392655857650802539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199785068523541143534403385 149838801392655857650802539)
        ·
          refine ⟨224758202088983786476203809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149838801392655857650802539 224758202088983786476203809)
          ·
            refine ⟨168568651566737839857152857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224758202088983786476203809 168568651566737839857152857)
            ·
              refine ⟨126426488675053379892864643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168568651566737839857152857 126426488675053379892864643)
              ·
                refine ⟨189639733012580069839296965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126426488675053379892864643 189639733012580069839296965)
                ·
                  refine ⟨35557449939858763094868181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 189639733012580069839296965 35557449939858763094868181)
                  ·
                    refine ⟨833377732965439760035973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35557449939858763094868181 833377732965439760035973)
                    ·
                      rfl

theorem cell23_4868992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 4, 7].length) (baseStart_4868992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4868992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4868992 prefixEnd_4868992 := by exact prefixLift 4868992
  have htrace : WordTrace (prefixWord ++ tailWord_4868992) baseStart_4868992 baseEnd_4868992 := by
    simpa [prefixWord, tailWord_4868992, baseEnd_4868992] using wordTrace_append hprefix tailTrace_4868992
  have hstable : (prefixWord ++ tailWord_4868992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4868992).length < 2 ^ (prefixWord ++ tailWord_4868992).sum := by decide
  have hdescent : baseEnd_4868992 < baseStart_4868992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4868992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869010 : List Nat := [3, 2, 3, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_4869010 : Nat := 118140960795 + 4869010 * 2 ^ 59
def prefixEnd_4869010 : Nat := 4983230072969 + 3 ^ 40 * 4869010 * 2
def baseEnd_4869010 : Nat := 2500142441548100209682837

theorem tailTrace_4869010 : CollatzResearch.WordTrace tailWord_4869010 prefixEnd_4869010 2500142441548100209682837 := by
  unfold tailWord_4869010
  simp only [CollatzResearch.WordTrace]
  refine ⟨44396846022603951387295121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118391589393610537032786989 44396846022603951387295121)
  ·
    refine ⟨33297634516952963540471341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44396846022603951387295121 33297634516952963540471341)
    ·
      refine ⟨12486612943857361327676753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33297634516952963540471341 12486612943857361327676753)
      ·
        refine ⟨9364959707893020995757565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12486612943857361327676753 9364959707893020995757565)
        ·
          refine ⟨3511859890459882873409087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9364959707893020995757565 3511859890459882873409087)
          ·
            refine ⟨5267789835689824310113631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3511859890459882873409087 5267789835689824310113631)
            ·
              refine ⟨7901684753534736465170447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5267789835689824310113631 7901684753534736465170447)
              ·
                refine ⟨11852527130302104697755671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7901684753534736465170447 11852527130302104697755671)
                ·
                  refine ⟨17778790695453157046633507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11852527130302104697755671 17778790695453157046633507)
                  ·
                    refine ⟨26668186043179735569950261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17778790695453157046633507 26668186043179735569950261)
                    ·
                      refine ⟨2500142441548100209682837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26668186043179735569950261 2500142441548100209682837)
                      ·
                        rfl

theorem cell23_4869010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_4869010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869010 prefixEnd_4869010 := by exact prefixLift 4869010
  have htrace : WordTrace (prefixWord ++ tailWord_4869010) baseStart_4869010 baseEnd_4869010 := by
    simpa [prefixWord, tailWord_4869010, baseEnd_4869010] using wordTrace_append hprefix tailTrace_4869010
  have hstable : (prefixWord ++ tailWord_4869010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869010).length < 2 ^ (prefixWord ++ tailWord_4869010).sum := by decide
  have hdescent : baseEnd_4869010 < baseStart_4869010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869023 : List Nat := [1, 1, 2, 5, 2, 1, 1, 4, 2, 1, 3]
def baseStart_4869023 : Nat := 118140960795 + 4869023 * 2 ^ 59
def prefixEnd_4869023 : Nat := 4983230072969 + 3 ^ 40 * 4869023 * 2
def baseEnd_4869023 : Nat := 2500149116796608658820277

theorem tailTrace_4869023 : CollatzResearch.WordTrace tailWord_4869023 prefixEnd_4869023 2500149116796608658820277 := by
  unfold tailWord_4869023
  simp only [CollatzResearch.WordTrace]
  refine ⟨177587858239368708769403723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118391905492912472512935815 177587858239368708769403723)
  ·
    refine ⟨266381787359053063154105585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177587858239368708769403723 266381787359053063154105585)
    ·
      refine ⟨199786340519289797365579189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266381787359053063154105585 199786340519289797365579189)
      ·
        refine ⟨18729969423683418503023049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 199786340519289797365579189 18729969423683418503023049)
        ·
          refine ⟨14047477067762563877267287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18729969423683418503023049 14047477067762563877267287)
          ·
            refine ⟨21071215601643845815900931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14047477067762563877267287 21071215601643845815900931)
            ·
              refine ⟨31606823402465768723851397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21071215601643845815900931 31606823402465768723851397)
              ·
                refine ⟨5926279387962331635722137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31606823402465768723851397 5926279387962331635722137)
                ·
                  refine ⟨4444709540971748726791603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5926279387962331635722137 4444709540971748726791603)
                  ·
                    refine ⟨6667064311457623090187405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4444709540971748726791603 6667064311457623090187405)
                    ·
                      refine ⟨2500149116796608658820277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6667064311457623090187405 2500149116796608658820277)
                      ·
                        rfl

theorem cell23_4869023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_4869023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869023 prefixEnd_4869023 := by exact prefixLift 4869023
  have htrace : WordTrace (prefixWord ++ tailWord_4869023) baseStart_4869023 baseEnd_4869023 := by
    simpa [prefixWord, tailWord_4869023, baseEnd_4869023] using wordTrace_append hprefix tailTrace_4869023
  have hstable : (prefixWord ++ tailWord_4869023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869023).length < 2 ^ (prefixWord ++ tailWord_4869023).sum := by decide
  have hdescent : baseEnd_4869023 < baseStart_4869023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869076 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_4869076 : Nat := 118140960795 + 4869076 * 2 ^ 59
def prefixEnd_4869076 : Nat := 4983230072969 + 3 ^ 40 * 4869076 * 2
def baseEnd_4869076 : Nat := 2500176331271296951457533

theorem tailTrace_4869076 : CollatzResearch.WordTrace tailWord_4869076 prefixEnd_4869076 2500176331271296951457533 := by
  unfold tailWord_4869076
  simp only [CollatzResearch.WordTrace]
  refine ⟨88794895654088349410541541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118393194205451132547388721 88794895654088349410541541)
  ·
    refine ⟨16649042935141565514476539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88794895654088349410541541 16649042935141565514476539)
    ·
      refine ⟨24973564402712348271714809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16649042935141565514476539 24973564402712348271714809)
      ·
        refine ⟨18730173302034261203786107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24973564402712348271714809 18730173302034261203786107)
        ·
          refine ⟨28095259953051391805679161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18730173302034261203786107 28095259953051391805679161)
          ·
            refine ⟨21071444964788543854259371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28095259953051391805679161 21071444964788543854259371)
            ·
              refine ⟨31607167447182815781389057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21071444964788543854259371 31607167447182815781389057)
              ·
                refine ⟨23705375585387111836041793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31607167447182815781389057 23705375585387111836041793)
                ·
                  refine ⟨17779031689040333877031345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23705375585387111836041793 17779031689040333877031345)
                  ·
                    refine ⟨13334273766780250407773509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17779031689040333877031345 13334273766780250407773509)
                    ·
                      refine ⟨2500176331271296951457533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13334273766780250407773509 2500176331271296951457533)
                      ·
                        rfl

theorem cell23_4869076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_4869076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869076 prefixEnd_4869076 := by exact prefixLift 4869076
  have htrace : WordTrace (prefixWord ++ tailWord_4869076) baseStart_4869076 baseEnd_4869076 := by
    simpa [prefixWord, tailWord_4869076, baseEnd_4869076] using wordTrace_append hprefix tailTrace_4869076
  have hstable : (prefixWord ++ tailWord_4869076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869076).length < 2 ^ (prefixWord ++ tailWord_4869076).sum := by decide
  have hdescent : baseEnd_4869076 < baseStart_4869076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869080 : List Nat := [2, 1, 2, 2, 2, 3, 3, 2, 2, 2, 2]
def baseStart_4869080 : Nat := 118140960795 + 4869080 * 2 ^ 59
def prefixEnd_4869080 : Nat := 4983230072969 + 3 ^ 40 * 4869080 * 2
def baseEnd_4869080 : Nat := 2500178385193914935807515

theorem tailTrace_4869080 : CollatzResearch.WordTrace tailWord_4869080 prefixEnd_4869080 2500178385193914935807515 := by
  unfold tailWord_4869080
  simp only [CollatzResearch.WordTrace]
  refine ⟨88794968600081103752114347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118393291466774805002819129 88794968600081103752114347)
  ·
    refine ⟨133192452900121655628171521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88794968600081103752114347 133192452900121655628171521)
    ·
      refine ⟨99894339675091241721128641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133192452900121655628171521 99894339675091241721128641)
      ·
        refine ⟨74920754756318431290846481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99894339675091241721128641 74920754756318431290846481)
        ·
          refine ⟨56190566067238823468134861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74920754756318431290846481 56190566067238823468134861)
          ·
            refine ⟨21071462275214558800550573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56190566067238823468134861 21071462275214558800550573)
            ·
              refine ⟨7901798353205459550206465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21071462275214558800550573 7901798353205459550206465)
              ·
                refine ⟨5926348764904094662654849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7901798353205459550206465 5926348764904094662654849)
                ·
                  refine ⟨4444761573678070996991137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5926348764904094662654849 4444761573678070996991137)
                  ·
                    refine ⟨3333571180258553247743353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4444761573678070996991137 3333571180258553247743353)
                    ·
                      refine ⟨2500178385193914935807515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3333571180258553247743353 2500178385193914935807515)
                      ·
                        rfl

theorem cell23_4869080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 2, 2, 2, 2].length) (baseStart_4869080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869080 prefixEnd_4869080 := by exact prefixLift 4869080
  have htrace : WordTrace (prefixWord ++ tailWord_4869080) baseStart_4869080 baseEnd_4869080 := by
    simpa [prefixWord, tailWord_4869080, baseEnd_4869080] using wordTrace_append hprefix tailTrace_4869080
  have hstable : (prefixWord ++ tailWord_4869080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869080).length < 2 ^ (prefixWord ++ tailWord_4869080).sum := by decide
  have hdescent : baseEnd_4869080 < baseStart_4869080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
