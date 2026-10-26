import V185TrunkScan20Chunk082

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_504639 : List Nat := [1, 1, 2, 2, 5, 9]
def baseStart_504639 : Nat := 118140960795 + 504639 * 2 ^ 59
def prefixEnd_504639 : Nat := 4983230072969 + 3 ^ 40 * 504639 * 2
def baseEnd_504639 : Nat := 8530777415781278396435

theorem tailTrace_504639 : CollatzResearch.WordTrace tailWord_504639 prefixEnd_504639 8530777415781278396435 := by
  unfold tailWord_504639
  simp only [CollatzResearch.WordTrace]
  refine ⟨18405696418786563324732971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12270464279191042216488647 18405696418786563324732971)
  ·
    refine ⟨27608544628179844987099457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18405696418786563324732971 27608544628179844987099457)
    ·
      refine ⟨20706408471134883740324593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27608544628179844987099457 20706408471134883740324593)
      ·
        refine ⟨15529806353351162805243445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20706408471134883740324593 15529806353351162805243445)
        ·
          refine ⟨1455919345626671512991573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15529806353351162805243445 1455919345626671512991573)
          ·
            refine ⟨8530777415781278396435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1455919345626671512991573 8530777415781278396435)
            ·
              rfl

theorem cell20_504639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 9].length) (baseStart_504639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504639 prefixEnd_504639 := by exact prefixLift 504639
  have htrace : WordTrace (prefixWord ++ tailWord_504639) baseStart_504639 baseEnd_504639 := by
    simpa [prefixWord, tailWord_504639, baseEnd_504639] using wordTrace_append hprefix tailTrace_504639
  have hstable : (prefixWord ++ tailWord_504639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504639).length < 2 ^ (prefixWord ++ tailWord_504639).sum := by decide
  have hdescent : baseEnd_504639 < baseStart_504639 := by decide
  rcases family_descends (prefixWord ++ tailWord_504639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504641 : List Nat := [1, 2, 5, 3, 1, 2, 2, 2, 2]
def baseStart_504641 : Nat := 118140960795 + 504641 * 2 ^ 59
def prefixEnd_504641 : Nat := 4983230072969 + 3 ^ 40 * 504641 * 2
def baseEnd_504641 : Nat := 230331903080591398637071

theorem tailTrace_504641 : CollatzResearch.WordTrace tailWord_504641 prefixEnd_504641 230331903080591398637071 := by
  unfold tailWord_504641
  simp only [CollatzResearch.WordTrace]
  refine ⟨18405769364779317666305777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12270512909852878444203851 18405769364779317666305777)
  ·
    refine ⟨13804327023584488249729333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18405769364779317666305777 13804327023584488249729333)
    ·
      refine ⟨1294155658461045773412125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13804327023584488249729333 1294155658461045773412125)
      ·
        refine ⟨485308371922892165029547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1294155658461045773412125 485308371922892165029547)
        ·
          refine ⟨727962557884338247544321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485308371922892165029547 727962557884338247544321)
          ·
            refine ⟨545971918413253685658241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 727962557884338247544321 545971918413253685658241)
            ·
              refine ⟨409478938809940264243681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545971918413253685658241 409478938809940264243681)
              ·
                refine ⟨307109204107455198182761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409478938809940264243681 307109204107455198182761)
                ·
                  refine ⟨230331903080591398637071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307109204107455198182761 230331903080591398637071)
                  ·
                    rfl

theorem cell20_504641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 2].length) (baseStart_504641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504641 prefixEnd_504641 := by exact prefixLift 504641
  have htrace : WordTrace (prefixWord ++ tailWord_504641) baseStart_504641 baseEnd_504641 := by
    simpa [prefixWord, tailWord_504641, baseEnd_504641] using wordTrace_append hprefix tailTrace_504641
  have hstable : (prefixWord ++ tailWord_504641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504641).length < 2 ^ (prefixWord ++ tailWord_504641).sum := by decide
  have hdescent : baseEnd_504641 < baseStart_504641 := by decide
  rcases family_descends (prefixWord ++ tailWord_504641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504677 : List Nat := [1, 3, 1, 3, 1, 1, 2, 8]
def baseStart_504677 : Nat := 118140960795 + 504677 * 2 ^ 59
def prefixEnd_504677 : Nat := 4983230072969 + 3 ^ 40 * 504677 * 2
def baseEnd_504677 : Nat := 76782778153845091145641

theorem tailTrace_504677 : CollatzResearch.WordTrace tailWord_504677 prefixEnd_504677 76782778153845091145641 := by
  unfold tailWord_504677
  simp only [CollatzResearch.WordTrace]
  refine ⟨18407082392648895814616285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12271388261765930543077523 18407082392648895814616285)
  ·
    refine ⟨6902655897243335930481107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18407082392648895814616285 6902655897243335930481107)
    ·
      refine ⟨10353983845865003895721661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6902655897243335930481107 10353983845865003895721661)
      ·
        refine ⟨3882743942199376460895623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10353983845865003895721661 3882743942199376460895623)
        ·
          refine ⟨5824115913299064691343435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3882743942199376460895623 5824115913299064691343435)
          ·
            refine ⟨8736173869948597037015153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5824115913299064691343435 8736173869948597037015153)
            ·
              refine ⟨6552130402461447777761365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8736173869948597037015153 6552130402461447777761365)
              ·
                refine ⟨76782778153845091145641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6552130402461447777761365 76782778153845091145641)
                ·
                  rfl

theorem cell20_504677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 8].length) (baseStart_504677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504677 prefixEnd_504677 := by exact prefixLift 504677
  have htrace : WordTrace (prefixWord ++ tailWord_504677) baseStart_504677 baseEnd_504677 := by
    simpa [prefixWord, tailWord_504677, baseEnd_504677] using wordTrace_append hprefix tailTrace_504677
  have hstable : (prefixWord ++ tailWord_504677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504677).length < 2 ^ (prefixWord ++ tailWord_504677).sum := by decide
  have hdescent : baseEnd_504677 < baseStart_504677 := by decide
  rcases family_descends (prefixWord ++ tailWord_504677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504801 : List Nat := [1, 2, 3, 1, 2, 1, 1, 7, 2]
def baseStart_504801 : Nat := 118140960795 + 504801 * 2 ^ 59
def prefixEnd_504801 : Nat := 4983230072969 + 3 ^ 40 * 504801 * 2
def baseEnd_504801 : Nat := 230404931440341953303083

theorem tailTrace_504801 : CollatzResearch.WordTrace tailWord_504801 prefixEnd_504801 230404931440341953303083 := by
  unfold tailWord_504801
  simp only [CollatzResearch.WordTrace]
  refine ⟨18411605044199664992130257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12274403362799776661420171 18411605044199664992130257)
  ·
    refine ⟨13808703783149748744097693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18411605044199664992130257 13808703783149748744097693)
    ·
      refine ⟨5178263918681155779036635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13808703783149748744097693 5178263918681155779036635)
      ·
        refine ⟨7767395878021733668554953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5178263918681155779036635 7767395878021733668554953)
        ·
          refine ⟨5825546908516300251416215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7767395878021733668554953 5825546908516300251416215)
          ·
            refine ⟨8738320362774450377124323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5825546908516300251416215 8738320362774450377124323)
            ·
              refine ⟨13107480544161675565686485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8738320362774450377124323 13107480544161675565686485)
              ·
                refine ⟨307206575253789271070777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13107480544161675565686485 307206575253789271070777)
                ·
                  refine ⟨230404931440341953303083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307206575253789271070777 230404931440341953303083)
                  ·
                    rfl

theorem cell20_504801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 2].length) (baseStart_504801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504801 prefixEnd_504801 := by exact prefixLift 504801
  have htrace : WordTrace (prefixWord ++ tailWord_504801) baseStart_504801 baseEnd_504801 := by
    simpa [prefixWord, tailWord_504801, baseEnd_504801] using wordTrace_append hprefix tailTrace_504801
  have hstable : (prefixWord ++ tailWord_504801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504801).length < 2 ^ (prefixWord ++ tailWord_504801).sum := by decide
  have hdescent : baseEnd_504801 < baseStart_504801 := by decide
  rcases family_descends (prefixWord ++ tailWord_504801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504814 : List Nat := [4, 1, 2, 1, 4, 2, 2, 2, 2]
def baseStart_504814 : Nat := 118140960795 + 504814 * 2 ^ 59
def prefixEnd_504814 : Nat := 4983230072969 + 3 ^ 40 * 504814 * 2
def baseEnd_504814 : Nat := 230410864994571685869697

theorem tailTrace_504814 : CollatzResearch.WordTrace tailWord_504814 prefixEnd_504814 230410864994571685869697 := by
  unfold tailWord_504814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2301509899144071026544187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12274719462101712141568997 2301509899144071026544187)
  ·
    refine ⟨3452264848716106539816281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2301509899144071026544187 3452264848716106539816281)
    ·
      refine ⟨2589198636537079904862211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3452264848716106539816281 2589198636537079904862211)
      ·
        refine ⟨3883797954805619857293317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2589198636537079904862211 3883797954805619857293317)
        ·
          refine ⟨728212116526053723242497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3883797954805619857293317 728212116526053723242497)
          ·
            refine ⟨546159087394540292431873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 728212116526053723242497 546159087394540292431873)
            ·
              refine ⟨409619315545905219323905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546159087394540292431873 409619315545905219323905)
              ·
                refine ⟨307214486659428914492929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409619315545905219323905 307214486659428914492929)
                ·
                  refine ⟨230410864994571685869697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307214486659428914492929 230410864994571685869697)
                  ·
                    rfl

theorem cell20_504814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_504814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504814 prefixEnd_504814 := by exact prefixLift 504814
  have htrace : WordTrace (prefixWord ++ tailWord_504814) baseStart_504814 baseEnd_504814 := by
    simpa [prefixWord, tailWord_504814, baseEnd_504814] using wordTrace_append hprefix tailTrace_504814
  have hstable : (prefixWord ++ tailWord_504814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504814).length < 2 ^ (prefixWord ++ tailWord_504814).sum := by decide
  have hdescent : baseEnd_504814 < baseStart_504814 := by decide
  rcases family_descends (prefixWord ++ tailWord_504814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504815 : List Nat := [1, 1, 2, 1, 4, 3, 1, 4, 3]
def baseStart_504815 : Nat := 118140960795 + 504815 * 2 ^ 59
def prefixEnd_504815 : Nat := 4983230072969 + 3 ^ 40 * 504815 * 2
def baseEnd_504815 : Nat := 230411321421820126836359

theorem tailTrace_504815 : CollatzResearch.WordTrace tailWord_504815 prefixEnd_504815 230411321421820126836359 := by
  unfold tailWord_504815
  simp only [CollatzResearch.WordTrace]
  refine ⟨18412115666148945383139899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12274743777432630255426599 18412115666148945383139899)
  ·
    refine ⟨27618173499223418074709849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18412115666148945383139899 27618173499223418074709849)
    ·
      refine ⟨20713630124417563556032387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27618173499223418074709849 20713630124417563556032387)
      ·
        refine ⟨31070445186626345334048581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20713630124417563556032387 31070445186626345334048581)
        ·
          refine ⟨5825708472492439750134109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31070445186626345334048581 5825708472492439750134109)
          ·
            refine ⟨2184640677184664906300291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5825708472492439750134109 2184640677184664906300291)
            ·
              refine ⟨3276961015776997359450437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2184640677184664906300291 3276961015776997359450437)
              ·
                refine ⟨614430190458187004896957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3276961015776997359450437 614430190458187004896957)
                ·
                  refine ⟨230411321421820126836359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 614430190458187004896957 230411321421820126836359)
                  ·
                    rfl

theorem cell20_504815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 3].length) (baseStart_504815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504815 prefixEnd_504815 := by exact prefixLift 504815
  have htrace : WordTrace (prefixWord ++ tailWord_504815) baseStart_504815 baseEnd_504815 := by
    simpa [prefixWord, tailWord_504815, baseEnd_504815] using wordTrace_append hprefix tailTrace_504815
  have hstable : (prefixWord ++ tailWord_504815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504815).length < 2 ^ (prefixWord ++ tailWord_504815).sum := by decide
  have hdescent : baseEnd_504815 < baseStart_504815 := by decide
  rcases family_descends (prefixWord ++ tailWord_504815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504821 : List Nat := [1, 3, 5, 2, 2, 1, 1, 5]
def baseStart_504821 : Nat := 118140960795 + 504821 * 2 ^ 59
def prefixEnd_504821 : Nat := 4983230072969 + 3 ^ 40 * 504821 * 2
def baseEnd_504821 : Nat := 76804686661770257545445

theorem tailTrace_504821 : CollatzResearch.WordTrace tailWord_504821 prefixEnd_504821 76804686661770257545445 := by
  unfold tailWord_504821
  simp only [CollatzResearch.WordTrace]
  refine ⟨18412334504127208407858317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12274889669418138938572211 18412334504127208407858317)
  ·
    refine ⟨6904625439047703152946869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18412334504127208407858317 6904625439047703152946869)
    ·
      refine ⟨647308634910722170588769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6904625439047703152946869 647308634910722170588769)
      ·
        refine ⟨485481476183041627941577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 647308634910722170588769 485481476183041627941577)
        ·
          refine ⟨364111107137281220956183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485481476183041627941577 364111107137281220956183)
          ·
            refine ⟨546166660705921831434275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364111107137281220956183 546166660705921831434275)
            ·
              refine ⟨819249991058882747151413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546166660705921831434275 819249991058882747151413)
              ·
                refine ⟨76804686661770257545445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 819249991058882747151413 76804686661770257545445)
                ·
                  rfl

theorem cell20_504821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 5].length) (baseStart_504821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504821 prefixEnd_504821 := by exact prefixLift 504821
  have htrace : WordTrace (prefixWord ++ tailWord_504821) baseStart_504821 baseEnd_504821 := by
    simpa [prefixWord, tailWord_504821, baseEnd_504821] using wordTrace_append hprefix tailTrace_504821
  have hstable : (prefixWord ++ tailWord_504821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504821).length < 2 ^ (prefixWord ++ tailWord_504821).sum := by decide
  have hdescent : baseEnd_504821 < baseStart_504821 := by decide
  rcases family_descends (prefixWord ++ tailWord_504821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504856 : List Nat := [2, 1, 2, 3, 2, 3, 2, 3, 2]
def baseStart_504856 : Nat := 118140960795 + 504856 * 2 ^ 59
def prefixEnd_504856 : Nat := 4983230072969 + 3 ^ 40 * 504856 * 2
def baseEnd_504856 : Nat := 230430034939006206469525

theorem tailTrace_504856 : CollatzResearch.WordTrace tailWord_504856 prefixEnd_504856 230430034939006206469525 := by
  unfold tailWord_504856
  simp only [CollatzResearch.WordTrace]
  refine ⟨9206805529500204692691211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12275740706000272923588281 9206805529500204692691211)
  ·
    refine ⟨13810208294250307039036817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9206805529500204692691211 13810208294250307039036817)
    ·
      refine ⟨10357656220687730279277613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13810208294250307039036817 10357656220687730279277613)
      ·
        refine ⟨3884121082757898854729105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10357656220687730279277613 3884121082757898854729105)
        ·
          refine ⟨2913090812068424141046829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3884121082757898854729105 2913090812068424141046829)
          ·
            refine ⟨1092409054525659052892561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2913090812068424141046829 1092409054525659052892561)
            ·
              refine ⟨819306790894244289669421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1092409054525659052892561 819306790894244289669421)
              ·
                refine ⟨307240046585341608626033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 819306790894244289669421 307240046585341608626033)
                ·
                  refine ⟨230430034939006206469525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307240046585341608626033 230430034939006206469525)
                  ·
                    rfl

theorem cell20_504856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 2].length) (baseStart_504856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504856 prefixEnd_504856 := by exact prefixLift 504856
  have htrace : WordTrace (prefixWord ++ tailWord_504856) baseStart_504856 baseEnd_504856 := by
    simpa [prefixWord, tailWord_504856, baseEnd_504856] using wordTrace_append hprefix tailTrace_504856
  have hstable : (prefixWord ++ tailWord_504856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504856).length < 2 ^ (prefixWord ++ tailWord_504856).sum := by decide
  have hdescent : baseEnd_504856 < baseStart_504856 := by decide
  rcases family_descends (prefixWord ++ tailWord_504856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504867 : List Nat := [1, 1, 1, 4, 3, 3, 7]
def baseStart_504867 : Nat := 118140960795 + 504867 * 2 ^ 59
def prefixEnd_504867 : Nat := 4983230072969 + 3 ^ 40 * 504867 * 2
def baseEnd_504867 : Nat := 25603895070971006344757

theorem tailTrace_504867 : CollatzResearch.WordTrace tailWord_504867 prefixEnd_504867 25603895070971006344757 := by
  unfold tailWord_504867
  simp only [CollatzResearch.WordTrace]
  refine ⟨18414012261960558264032855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12276008174640372176021903 18414012261960558264032855)
  ·
    refine ⟨27621018392940837396049283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18414012261960558264032855 27621018392940837396049283)
    ·
      refine ⟨41431527589411256094073925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27621018392940837396049283 41431527589411256094073925)
      ·
        refine ⟨7768411423014610517638861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41431527589411256094073925 7768411423014610517638861)
        ·
          refine ⟨2913154283630478944114573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7768411423014610517638861 2913154283630478944114573)
          ·
            refine ⟨1092432856361429604042965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2913154283630478944114573 1092432856361429604042965)
            ·
              refine ⟨25603895070971006344757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1092432856361429604042965 25603895070971006344757)
              ·
                rfl

theorem cell20_504867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 7].length) (baseStart_504867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504867 prefixEnd_504867 := by exact prefixLift 504867
  have htrace : WordTrace (prefixWord ++ tailWord_504867) baseStart_504867 baseEnd_504867 := by
    simpa [prefixWord, tailWord_504867, baseEnd_504867] using wordTrace_append hprefix tailTrace_504867
  have hstable : (prefixWord ++ tailWord_504867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504867).length < 2 ^ (prefixWord ++ tailWord_504867).sum := by decide
  have hdescent : baseEnd_504867 < baseStart_504867 := by decide
  rcases family_descends (prefixWord ++ tailWord_504867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504918 : List Nat := [5, 2, 2, 1, 2, 2, 6]
def baseStart_504918 : Nat := 118140960795 + 504918 * 2 ^ 59
def prefixEnd_504918 : Nat := 4983230072969 + 3 ^ 40 * 504918 * 2
def baseEnd_504918 : Nat := 25606481492045505155845

theorem tailTrace_504918 : CollatzResearch.WordTrace tailWord_504918 prefixEnd_504918 25606481492045505155845 := by
  unfold tailWord_504918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1150992024048487123383713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12277248256517195982759605 1150992024048487123383713)
  ·
    refine ⟨863244018036365342537785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1150992024048487123383713 863244018036365342537785)
    ·
      refine ⟨647433013527274006903339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 863244018036365342537785 647433013527274006903339)
      ·
        refine ⟨971149520290911010355009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647433013527274006903339 971149520290911010355009)
        ·
          refine ⟨728362140218183257766257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 971149520290911010355009 728362140218183257766257)
          ·
            refine ⟨546271605163637443324693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 728362140218183257766257 546271605163637443324693)
            ·
              refine ⟨25606481492045505155845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 546271605163637443324693 25606481492045505155845)
              ·
                rfl

theorem cell20_504918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 6].length) (baseStart_504918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504918 prefixEnd_504918 := by exact prefixLift 504918
  have htrace : WordTrace (prefixWord ++ tailWord_504918) baseStart_504918 baseEnd_504918 := by
    simpa [prefixWord, tailWord_504918, baseEnd_504918] using wordTrace_append hprefix tailTrace_504918
  have hstable : (prefixWord ++ tailWord_504918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504918).length < 2 ^ (prefixWord ++ tailWord_504918).sum := by decide
  have hdescent : baseEnd_504918 < baseStart_504918 := by decide
  rcases family_descends (prefixWord ++ tailWord_504918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504943 : List Nat := [1, 1, 2, 1, 3, 3, 4, 5]
def baseStart_504943 : Nat := 118140960795 + 504943 * 2 ^ 59
def prefixEnd_504943 : Nat := 4983230072969 + 3 ^ 40 * 504943 * 2
def baseEnd_504943 : Nat := 76823248036540190189723

theorem tailTrace_504943 : CollatzResearch.WordTrace tailWord_504943 prefixEnd_504943 76823248036540190189723 := by
  unfold tailWord_504943
  simp only [CollatzResearch.WordTrace]
  refine ⟨18416784209685223243799483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12277856139790148829199655 18416784209685223243799483)
  ·
    refine ⟨27625176314527834865699225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18416784209685223243799483 27625176314527834865699225)
    ·
      refine ⟨20718882235895876149274419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27625176314527834865699225 20718882235895876149274419)
      ·
        refine ⟨31078323353843814223911629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20718882235895876149274419 31078323353843814223911629)
        ·
          refine ⟨11654371257691430333966861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31078323353843814223911629 11654371257691430333966861)
          ·
            refine ⟨4370389221634286375237573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11654371257691430333966861 4370389221634286375237573)
            ·
              refine ⟨819447979056428695357045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4370389221634286375237573 819447979056428695357045)
              ·
                refine ⟨76823248036540190189723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 819447979056428695357045 76823248036540190189723)
                ·
                  rfl

theorem cell20_504943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 5].length) (baseStart_504943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504943 prefixEnd_504943 := by exact prefixLift 504943
  have htrace : WordTrace (prefixWord ++ tailWord_504943) baseStart_504943 baseEnd_504943 := by
    simpa [prefixWord, tailWord_504943, baseEnd_504943] using wordTrace_append hprefix tailTrace_504943
  have hstable : (prefixWord ++ tailWord_504943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504943).length < 2 ^ (prefixWord ++ tailWord_504943).sum := by decide
  have hdescent : baseEnd_504943 < baseStart_504943 := by decide
  rcases family_descends (prefixWord ++ tailWord_504943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504984 : List Nat := [2, 1, 2, 4, 2, 2, 2, 2, 3]
def baseStart_504984 : Nat := 118140960795 + 504984 * 2 ^ 59
def prefixEnd_504984 : Nat := 4983230072969 + 3 ^ 40 * 504984 * 2
def baseEnd_504984 : Nat := 230488457626806650202335

theorem tailTrace_504984 : CollatzResearch.WordTrace tailWord_504984 prefixEnd_504984 230488457626806650202335 := by
  unfold tailWord_504984
  simp only [CollatzResearch.WordTrace]
  refine ⟨9209139801268343623021003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12278853068357791497361337 9209139801268343623021003)
  ·
    refine ⟨13813709701902515434531505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9209139801268343623021003 13813709701902515434531505)
    ·
      refine ⟨10360282276426886575898629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13813709701902515434531505 10360282276426886575898629)
      ·
        refine ⟨1942552926830041232980993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10360282276426886575898629 1942552926830041232980993)
        ·
          refine ⟨1456914695122530924735745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1942552926830041232980993 1456914695122530924735745)
          ·
            refine ⟨1092686021341898193551809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1456914695122530924735745 1092686021341898193551809)
            ·
              refine ⟨819514516006423645163857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1092686021341898193551809 819514516006423645163857)
              ·
                refine ⟨614635887004817733872893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 819514516006423645163857 614635887004817733872893)
                ·
                  refine ⟨230488457626806650202335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 614635887004817733872893 230488457626806650202335)
                  ·
                    rfl

theorem cell20_504984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_504984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504984 prefixEnd_504984 := by exact prefixLift 504984
  have htrace : WordTrace (prefixWord ++ tailWord_504984) baseStart_504984 baseEnd_504984 := by
    simpa [prefixWord, tailWord_504984, baseEnd_504984] using wordTrace_append hprefix tailTrace_504984
  have hstable : (prefixWord ++ tailWord_504984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504984).length < 2 ^ (prefixWord ++ tailWord_504984).sum := by decide
  have hdescent : baseEnd_504984 < baseStart_504984 := by decide
  rcases family_descends (prefixWord ++ tailWord_504984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504994 : List Nat := [3, 3, 1, 3, 3, 1, 1, 5]
def baseStart_504994 : Nat := 118140960795 + 504994 * 2 ^ 59
def prefixEnd_504994 : Nat := 4983230072969 + 3 ^ 40 * 504994 * 2
def baseEnd_504994 : Nat := 76831007299763686622987

theorem tailTrace_504994 : CollatzResearch.WordTrace tailWord_504994 prefixEnd_504994 76831007299763686622987 := by
  unfold tailWord_504994
  simp only [CollatzResearch.WordTrace]
  refine ⟨4604661083125114738476509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12279096221666972635937357 4604661083125114738476509)
  ·
    refine ⟨1726747906171918026928691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4604661083125114738476509 1726747906171918026928691)
    ·
      refine ⟨2590121859257877040393037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1726747906171918026928691 2590121859257877040393037)
      ·
        refine ⟨971295697221703890147389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2590121859257877040393037 971295697221703890147389)
        ·
          refine ⟨364235886458138958805271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 971295697221703890147389 364235886458138958805271)
          ·
            refine ⟨546353829687208438207907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364235886458138958805271 546353829687208438207907)
            ·
              refine ⟨819530744530812657311861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546353829687208438207907 819530744530812657311861)
              ·
                refine ⟨76831007299763686622987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 819530744530812657311861 76831007299763686622987)
                ·
                  rfl

theorem cell20_504994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_504994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504994 prefixEnd_504994 := by exact prefixLift 504994
  have htrace : WordTrace (prefixWord ++ tailWord_504994) baseStart_504994 baseEnd_504994 := by
    simpa [prefixWord, tailWord_504994, baseEnd_504994] using wordTrace_append hprefix tailTrace_504994
  have hstable : (prefixWord ++ tailWord_504994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504994).length < 2 ^ (prefixWord ++ tailWord_504994).sum := by decide
  have hdescent : baseEnd_504994 < baseStart_504994 := by decide
  rcases family_descends (prefixWord ++ tailWord_504994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504995 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 8]
def baseStart_504995 : Nat := 118140960795 + 504995 * 2 ^ 59
def prefixEnd_504995 : Nat := 4983230072969 + 3 ^ 40 * 504995 * 2
def baseEnd_504995 : Nat := 230493478326539500835623

theorem tailTrace_504995 : CollatzResearch.WordTrace tailWord_504995 prefixEnd_504995 230493478326539500835623 := by
  unfold tailWord_504995
  simp only [CollatzResearch.WordTrace]
  refine ⟨18418680805496836124692439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12279120536997890749794959 18418680805496836124692439)
  ·
    refine ⟨27628021208245254187038659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18418680805496836124692439 27628021208245254187038659)
    ·
      refine ⟨41442031812367881280557989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27628021208245254187038659 41442031812367881280557989)
      ·
        refine ⟨7770380964818977740104623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41442031812367881280557989 7770380964818977740104623)
        ·
          refine ⟨11655571447228466610156935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7770380964818977740104623 11655571447228466610156935)
          ·
            refine ⟨17483357170842699915235403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11655571447228466610156935 17483357170842699915235403)
            ·
              refine ⟨26225035756264049872853105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17483357170842699915235403 26225035756264049872853105)
              ·
                refine ⟨19668776817198037404639829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26225035756264049872853105 19668776817198037404639829)
                ·
                  refine ⟨230493478326539500835623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19668776817198037404639829 230493478326539500835623)
                  ·
                    rfl

theorem cell20_504995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_504995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_504995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_504995 prefixEnd_504995 := by exact prefixLift 504995
  have htrace : WordTrace (prefixWord ++ tailWord_504995) baseStart_504995 baseEnd_504995 := by
    simpa [prefixWord, tailWord_504995, baseEnd_504995] using wordTrace_append hprefix tailTrace_504995
  have hstable : (prefixWord ++ tailWord_504995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504995).length < 2 ^ (prefixWord ++ tailWord_504995).sum := by decide
  have hdescent : baseEnd_504995 < baseStart_504995 := by decide
  rcases family_descends (prefixWord ++ tailWord_504995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505025 : List Nat := [1, 2, 6, 1, 1, 2, 2, 3, 2]
def baseStart_505025 : Nat := 118140960795 + 505025 * 2 ^ 59
def prefixEnd_505025 : Nat := 4983230072969 + 3 ^ 40 * 505025 * 2
def baseEnd_505025 : Nat := 230507171143992729835501

theorem tailTrace_505025 : CollatzResearch.WordTrace tailWord_505025 prefixEnd_505025 230507171143992729835501 := by
  unfold tailWord_505025
  simp only [CollatzResearch.WordTrace]
  refine ⟨18419774995388151248284529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12279849996925434165523019 18419774995388151248284529)
  ·
    refine ⟨13814831246541113436213397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18419774995388151248284529 13814831246541113436213397)
    ·
      refine ⟨647570214681614692322503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13814831246541113436213397 647570214681614692322503)
      ·
        refine ⟨971355322022422038483755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647570214681614692322503 971355322022422038483755)
        ·
          refine ⟨1457032983033633057725633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971355322022422038483755 1457032983033633057725633)
          ·
            refine ⟨1092774737275224793294225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1457032983033633057725633 1092774737275224793294225)
            ·
              refine ⟨819581052956418594970669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1092774737275224793294225 819581052956418594970669)
              ·
                refine ⟨307342894858656973114001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 819581052956418594970669 307342894858656973114001)
                ·
                  refine ⟨230507171143992729835501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307342894858656973114001 230507171143992729835501)
                  ·
                    rfl

theorem cell20_505025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 2].length) (baseStart_505025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505025 prefixEnd_505025 := by exact prefixLift 505025
  have htrace : WordTrace (prefixWord ++ tailWord_505025) baseStart_505025 baseEnd_505025 := by
    simpa [prefixWord, tailWord_505025, baseEnd_505025] using wordTrace_append hprefix tailTrace_505025
  have hstable : (prefixWord ++ tailWord_505025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505025).length < 2 ^ (prefixWord ++ tailWord_505025).sum := by decide
  have hdescent : baseEnd_505025 < baseStart_505025 := by decide
  rcases family_descends (prefixWord ++ tailWord_505025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505074 : List Nat := [3, 2, 1, 3, 3, 1, 1, 6]
def baseStart_505074 : Nat := 118140960795 + 505074 * 2 ^ 59
def prefixEnd_505074 : Nat := 4983230072969 + 3 ^ 40 * 505074 * 2
def baseEnd_505074 : Nat := 76843178693055445733989

theorem tailTrace_505074 : CollatzResearch.WordTrace tailWord_505074 prefixEnd_505074 76843178693055445733989 := by
  unfold tailWord_505074
  simp only [CollatzResearch.WordTrace]
  refine ⟨4605390543052658154204569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12281041448140421744545517 4605390543052658154204569)
  ·
    refine ⟨3454042907289493615653427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4605390543052658154204569 3454042907289493615653427)
    ·
      refine ⟨5181064360934240423480141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3454042907289493615653427 5181064360934240423480141)
      ·
        refine ⟨1942899135350340158805053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5181064360934240423480141 1942899135350340158805053)
        ·
          refine ⟨728587175756377559551895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1942899135350340158805053 728587175756377559551895)
          ·
            refine ⟨1092880763634566339327843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728587175756377559551895 1092880763634566339327843)
            ·
              refine ⟨1639321145451849508991765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092880763634566339327843 1639321145451849508991765)
              ·
                refine ⟨76843178693055445733989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1639321145451849508991765 76843178693055445733989)
                ·
                  rfl

theorem cell20_505074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_505074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505074 prefixEnd_505074 := by exact prefixLift 505074
  have htrace : WordTrace (prefixWord ++ tailWord_505074) baseStart_505074 baseEnd_505074 := by
    simpa [prefixWord, tailWord_505074, baseEnd_505074] using wordTrace_append hprefix tailTrace_505074
  have hstable : (prefixWord ++ tailWord_505074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505074).length < 2 ^ (prefixWord ++ tailWord_505074).sum := by decide
  have hdescent : baseEnd_505074 < baseStart_505074 := by decide
  rcases family_descends (prefixWord ++ tailWord_505074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505076 : List Nat := [2, 6, 1, 2, 2, 1, 1, 3, 2]
def baseStart_505076 : Nat := 118140960795 + 505076 * 2 ^ 59
def prefixEnd_505076 : Nat := 4983230072969 + 3 ^ 40 * 505076 * 2
def baseEnd_505076 : Nat := 230530448933663219135293

theorem tailTrace_505076 : CollatzResearch.WordTrace tailWord_505076 prefixEnd_505076 230530448933663219135293 := by
  unfold tailWord_505076
  simp only [CollatzResearch.WordTrace]
  refine ⟨9210817559101693479195541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12281090078802257972260721 9210817559101693479195541)
  ·
    refine ⟨431757073082891881837291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9210817559101693479195541 431757073082891881837291)
    ·
      refine ⟨647635609624337822755937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 431757073082891881837291 647635609624337822755937)
      ·
        refine ⟨485726707218253367066953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 647635609624337822755937 485726707218253367066953)
        ·
          refine ⟨364295030413690025300215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485726707218253367066953 364295030413690025300215)
          ·
            refine ⟨546442545620535037950323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364295030413690025300215 546442545620535037950323)
            ·
              refine ⟨819663818430802556925485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546442545620535037950323 819663818430802556925485)
              ·
                refine ⟨307373931911550958847057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 819663818430802556925485 307373931911550958847057)
                ·
                  refine ⟨230530448933663219135293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307373931911550958847057 230530448933663219135293)
                  ·
                    rfl

theorem cell20_505076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_505076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505076 prefixEnd_505076 := by exact prefixLift 505076
  have htrace : WordTrace (prefixWord ++ tailWord_505076) baseStart_505076 baseEnd_505076 := by
    simpa [prefixWord, tailWord_505076, baseEnd_505076] using wordTrace_append hprefix tailTrace_505076
  have hstable : (prefixWord ++ tailWord_505076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505076).length < 2 ^ (prefixWord ++ tailWord_505076).sum := by decide
  have hdescent : baseEnd_505076 < baseStart_505076 := by decide
  rcases family_descends (prefixWord ++ tailWord_505076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505154 : List Nat := [3, 17]
def baseStart_505154 : Nat := 118140960795 + 505154 * 2 ^ 59
def prefixEnd_505154 : Nat := 4983230072969 + 3 ^ 40 * 505154 * 2
def baseEnd_505154 : Nat := 105425720283055150679

theorem tailTrace_505154 : CollatzResearch.WordTrace tailWord_505154 prefixEnd_505154 105425720283055150679 := by
  unfold tailWord_505154
  simp only [CollatzResearch.WordTrace]
  refine ⟨4606120002980201569932629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12282986674613870853153677 4606120002980201569932629)
  ·
    refine ⟨105425720283055150679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 17 4606120002980201569932629 105425720283055150679)
    ·
      rfl

theorem cell20_505154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 17].length) (baseStart_505154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505154 prefixEnd_505154 := by exact prefixLift 505154
  have htrace : WordTrace (prefixWord ++ tailWord_505154) baseStart_505154 baseEnd_505154 := by
    simpa [prefixWord, tailWord_505154, baseEnd_505154] using wordTrace_append hprefix tailTrace_505154
  have hstable : (prefixWord ++ tailWord_505154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505154).length < 2 ^ (prefixWord ++ tailWord_505154).sum := by decide
  have hdescent : baseEnd_505154 < baseStart_505154 := by decide
  rcases family_descends (prefixWord ++ tailWord_505154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505156 : List Nat := [2, 3, 4, 1, 1, 3, 2, 2, 2]
def baseStart_505156 : Nat := 118140960795 + 505156 * 2 ^ 59
def prefixEnd_505156 : Nat := 4983230072969 + 3 ^ 40 * 505156 * 2
def baseEnd_505156 : Nat := 230566963113538496468299

theorem tailTrace_505156 : CollatzResearch.WordTrace tailWord_505156 prefixEnd_505156 230566963113538496468299 := by
  unfold tailWord_505156
  simp only [CollatzResearch.WordTrace]
  refine ⟨9212276478956780310651661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12283035305275707080868881 9212276478956780310651661)
  ·
    refine ⟨3454603679608792616494373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9212276478956780310651661 3454603679608792616494373)
    ·
      refine ⟨647738189926648615592695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3454603679608792616494373 647738189926648615592695)
      ·
        refine ⟨971607284889972923389043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647738189926648615592695 971607284889972923389043)
        ·
          refine ⟨1457410927334959385083565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971607284889972923389043 1457410927334959385083565)
          ·
            refine ⟨546529097750609769406337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1457410927334959385083565 546529097750609769406337)
            ·
              refine ⟨409896823312957327054753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546529097750609769406337 409896823312957327054753)
              ·
                refine ⟨307422617484717995291065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409896823312957327054753 307422617484717995291065)
                ·
                  refine ⟨230566963113538496468299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307422617484717995291065 230566963113538496468299)
                  ·
                    rfl

theorem cell20_505156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_505156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505156 prefixEnd_505156 := by exact prefixLift 505156
  have htrace : WordTrace (prefixWord ++ tailWord_505156) baseStart_505156 baseEnd_505156 := by
    simpa [prefixWord, tailWord_505156, baseEnd_505156] using wordTrace_append hprefix tailTrace_505156
  have hstable : (prefixWord ++ tailWord_505156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505156).length < 2 ^ (prefixWord ++ tailWord_505156).sum := by decide
  have hdescent : baseEnd_505156 < baseStart_505156 := by decide
  rcases family_descends (prefixWord ++ tailWord_505156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505188 : List Nat := [2, 3, 1, 1, 3, 3, 3, 4]
def baseStart_505188 : Nat := 118140960795 + 505188 * 2 ^ 59
def prefixEnd_505188 : Nat := 4983230072969 + 3 ^ 40 * 505188 * 2
def baseEnd_505188 : Nat := 76860522928496202467167

theorem tailTrace_505188 : CollatzResearch.WordTrace tailWord_505188 prefixEnd_505188 76860522928496202467167 := by
  unfold tailWord_505188
  simp only [CollatzResearch.WordTrace]
  refine ⟨9212860046898815043234109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12283813395865086724312145 9212860046898815043234109)
  ·
    refine ⟨3454822517587055641212791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9212860046898815043234109 3454822517587055641212791)
    ·
      refine ⟨5182233776380583461819187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3454822517587055641212791 5182233776380583461819187)
      ·
        refine ⟨7773350664570875192728781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5182233776380583461819187 7773350664570875192728781)
        ·
          refine ⟨2915006499214078197273293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7773350664570875192728781 2915006499214078197273293)
          ·
            refine ⟨1093127437205279323977485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2915006499214078197273293 1093127437205279323977485)
            ·
              refine ⟨409922788951979746491557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1093127437205279323977485 409922788951979746491557)
              ·
                refine ⟨76860522928496202467167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 409922788951979746491557 76860522928496202467167)
                ·
                  rfl

theorem cell20_505188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 3, 4].length) (baseStart_505188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505188 prefixEnd_505188 := by exact prefixLift 505188
  have htrace : WordTrace (prefixWord ++ tailWord_505188) baseStart_505188 baseEnd_505188 := by
    simpa [prefixWord, tailWord_505188, baseEnd_505188] using wordTrace_append hprefix tailTrace_505188
  have hstable : (prefixWord ++ tailWord_505188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505188).length < 2 ^ (prefixWord ++ tailWord_505188).sum := by decide
  have hdescent : baseEnd_505188 < baseStart_505188 := by decide
  rcases family_descends (prefixWord ++ tailWord_505188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505219 : List Nat := [1, 1, 1, 3, 5, 1, 2, 4, 2]
def baseStart_505219 : Nat := 118140960795 + 505219 * 2 ^ 59
def prefixEnd_505219 : Nat := 4983230072969 + 3 ^ 40 * 505219 * 2
def baseEnd_505219 : Nat := 230595718030190277368041

theorem tailTrace_505219 : CollatzResearch.WordTrace tailWord_505219 prefixEnd_505219 230595718030190277368041 := by
  unfold tailWord_505219
  simp only [CollatzResearch.WordTrace]
  refine ⟨18426850756685322380846711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12284567171123548253897807 18426850756685322380846711)
  ·
    refine ⟨27640276135027983571270067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18426850756685322380846711 27640276135027983571270067)
    ·
      refine ⟨41460414202541975356905101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27640276135027983571270067 41460414202541975356905101)
      ·
        refine ⟨15547655325953240758839413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41460414202541975356905101 15547655325953240758839413)
        ·
          refine ⟨1457592686808116321141195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15547655325953240758839413 1457592686808116321141195)
          ·
            refine ⟨2186389030212174481711793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457592686808116321141195 2186389030212174481711793)
            ·
              refine ⟨1639791772659130861283845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2186389030212174481711793 1639791772659130861283845)
              ·
                refine ⟨307460957373587036490721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1639791772659130861283845 307460957373587036490721)
                ·
                  refine ⟨230595718030190277368041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307460957373587036490721 230595718030190277368041)
                  ·
                    rfl

theorem cell20_505219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 2].length) (baseStart_505219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505219 prefixEnd_505219 := by exact prefixLift 505219
  have htrace : WordTrace (prefixWord ++ tailWord_505219) baseStart_505219 baseEnd_505219 := by
    simpa [prefixWord, tailWord_505219, baseEnd_505219] using wordTrace_append hprefix tailTrace_505219
  have hstable : (prefixWord ++ tailWord_505219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505219).length < 2 ^ (prefixWord ++ tailWord_505219).sum := by decide
  have hdescent : baseEnd_505219 < baseStart_505219 := by decide
  rcases family_descends (prefixWord ++ tailWord_505219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505247 : List Nat := [1, 1, 2, 5, 1, 3, 1, 6]
def baseStart_505247 : Nat := 118140960795 + 505247 * 2 ^ 59
def prefixEnd_505247 : Nat := 4983230072969 + 3 ^ 40 * 505247 * 2
def baseEnd_505247 : Nat := 76869499331048874811531

theorem tailTrace_505247 : CollatzResearch.WordTrace tailWord_505247 prefixEnd_505247 76869499331048874811531 := by
  unfold tailWord_505247
  simp only [CollatzResearch.WordTrace]
  refine ⟨18427872000583883162865995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12285248000389255441910663 18427872000583883162865995)
  ·
    refine ⟨27641808000875824744298993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18427872000583883162865995 27641808000875824744298993)
    ·
      refine ⟨20731356000656868558224245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27641808000875824744298993 20731356000656868558224245)
      ·
        refine ⟨1943564625061581427333523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20731356000656868558224245 1943564625061581427333523)
        ·
          refine ⟨2915346937592372141000285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1943564625061581427333523 2915346937592372141000285)
          ·
            refine ⟨1093255101597139552875107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2915346937592372141000285 1093255101597139552875107)
            ·
              refine ⟨1639882652395709329312661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093255101597139552875107 1639882652395709329312661)
              ·
                refine ⟨76869499331048874811531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1639882652395709329312661 76869499331048874811531)
                ·
                  rfl

theorem cell20_505247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 6].length) (baseStart_505247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505247 prefixEnd_505247 := by exact prefixLift 505247
  have htrace : WordTrace (prefixWord ++ tailWord_505247) baseStart_505247 baseEnd_505247 := by
    simpa [prefixWord, tailWord_505247, baseEnd_505247] using wordTrace_append hprefix tailTrace_505247
  have hstable : (prefixWord ++ tailWord_505247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505247).length < 2 ^ (prefixWord ++ tailWord_505247).sum := by decide
  have hdescent : baseEnd_505247 < baseStart_505247 := by decide
  rcases family_descends (prefixWord ++ tailWord_505247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505302 : List Nat := [5, 2, 1, 1, 1, 2, 2, 6]
def baseStart_505302 : Nat := 118140960795 + 505302 * 2 ^ 59
def prefixEnd_505302 : Nat := 4983230072969 + 3 ^ 40 * 505302 * 2
def baseEnd_505302 : Nat := 76877867163936959200345

theorem tailTrace_505302 : CollatzResearch.WordTrace tailWord_505302 prefixEnd_505302 76877867163936959200345 := by
  unfold tailWord_505302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1151867375961539222257385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12286585343589751704078773 1151867375961539222257385)
  ·
    refine ⟨863900531971154416693039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1151867375961539222257385 863900531971154416693039)
    ·
      refine ⟨1295850797956731625039559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 863900531971154416693039 1295850797956731625039559)
      ·
        refine ⟨1943776196935097437559339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1295850797956731625039559 1943776196935097437559339)
        ·
          refine ⟨2915664295402646156339009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1943776196935097437559339 2915664295402646156339009)
          ·
            refine ⟨2186748221551984617254257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2915664295402646156339009 2186748221551984617254257)
            ·
              refine ⟨1640061166163988462940693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2186748221551984617254257 1640061166163988462940693)
              ·
                refine ⟨76877867163936959200345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1640061166163988462940693 76877867163936959200345)
                ·
                  rfl

theorem cell20_505302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_505302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505302 prefixEnd_505302 := by exact prefixLift 505302
  have htrace : WordTrace (prefixWord ++ tailWord_505302) baseStart_505302 baseEnd_505302 := by
    simpa [prefixWord, tailWord_505302, baseEnd_505302] using wordTrace_append hprefix tailTrace_505302
  have hstable : (prefixWord ++ tailWord_505302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505302).length < 2 ^ (prefixWord ++ tailWord_505302).sum := by decide
  have hdescent : baseEnd_505302 < baseStart_505302 := by decide
  rcases family_descends (prefixWord ++ tailWord_505302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505337 : List Nat := [1, 2, 1, 3, 1, 2, 1, 5, 4]
def baseStart_505337 : Nat := 118140960795 + 505337 * 2 ^ 59
def prefixEnd_505337 : Nat := 4983230072969 + 3 ^ 40 * 505337 * 2
def baseEnd_505337 : Nat := 230649576445506311434225

theorem tailTrace_505337 : CollatzResearch.WordTrace tailWord_505337 prefixEnd_505337 230649576445506311434225 := by
  unfold tailWord_505337
  simp only [CollatzResearch.WordTrace]
  refine ⟨18431154570257828533642265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12287436380171885689094843 18431154570257828533642265)
  ·
    refine ⟨13823365927693371400231699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18431154570257828533642265 13823365927693371400231699)
    ·
      refine ⟨20735048891540057100347549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13823365927693371400231699 20735048891540057100347549)
      ·
        refine ⟨7775643334327521412630331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20735048891540057100347549 7775643334327521412630331)
        ·
          refine ⟨11663465001491282118945497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7775643334327521412630331 11663465001491282118945497)
          ·
            refine ⟨8747598751118461589209123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11663465001491282118945497 8747598751118461589209123)
            ·
              refine ⟨13121398126677692383813685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8747598751118461589209123 13121398126677692383813685)
              ·
                refine ⟨1230131074376033660982533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13121398126677692383813685 1230131074376033660982533)
                ·
                  refine ⟨230649576445506311434225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1230131074376033660982533 230649576445506311434225)
                  ·
                    rfl

theorem cell20_505337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_505337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505337 prefixEnd_505337 := by exact prefixLift 505337
  have htrace : WordTrace (prefixWord ++ tailWord_505337) baseStart_505337 baseEnd_505337 := by
    simpa [prefixWord, tailWord_505337, baseEnd_505337] using wordTrace_append hprefix tailTrace_505337
  have hstable : (prefixWord ++ tailWord_505337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505337).length < 2 ^ (prefixWord ++ tailWord_505337).sum := by decide
  have hdescent : baseEnd_505337 < baseStart_505337 := by decide
  rcases family_descends (prefixWord ++ tailWord_505337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505354 : List Nat := [3, 1, 2, 2, 2, 3, 1, 2, 4]
def baseStart_505354 : Nat := 118140960795 + 505354 * 2 ^ 59
def prefixEnd_505354 : Nat := 4983230072969 + 3 ^ 40 * 505354 * 2
def baseEnd_505354 : Nat := 230657335708729807867489

theorem tailTrace_505354 : CollatzResearch.WordTrace tailWord_505354 prefixEnd_505354 230657335708729807867489 := by
  unfold tailWord_505354
  simp only [CollatzResearch.WordTrace]
  refine ⟨4607943652799060109252779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12287849740797493624674077 4607943652799060109252779)
  ·
    refine ⟨6911915479198590163879169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4607943652799060109252779 6911915479198590163879169)
    ·
      refine ⟨5183936609398942622909377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6911915479198590163879169 5183936609398942622909377)
      ·
        refine ⟨3887952457049206967182033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5183936609398942622909377 3887952457049206967182033)
        ·
          refine ⟨2915964342786905225386525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3887952457049206967182033 2915964342786905225386525)
          ·
            refine ⟨1093486628545089459519947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2915964342786905225386525 1093486628545089459519947)
            ·
              refine ⟨1640229942817634189279921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093486628545089459519947 1640229942817634189279921)
              ·
                refine ⟨1230172457113225641959941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1640229942817634189279921 1230172457113225641959941)
                ·
                  refine ⟨230657335708729807867489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1230172457113225641959941 230657335708729807867489)
                  ·
                    rfl

theorem cell20_505354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_505354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505354 prefixEnd_505354 := by exact prefixLift 505354
  have htrace : WordTrace (prefixWord ++ tailWord_505354) baseStart_505354 baseEnd_505354 := by
    simpa [prefixWord, tailWord_505354, baseEnd_505354] using wordTrace_append hprefix tailTrace_505354
  have hstable : (prefixWord ++ tailWord_505354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505354).length < 2 ^ (prefixWord ++ tailWord_505354).sum := by decide
  have hdescent : baseEnd_505354 < baseStart_505354 := by decide
  rcases family_descends (prefixWord ++ tailWord_505354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505361 : List Nat := [1, 2, 2, 1, 1, 2, 7, 4]
def baseStart_505361 : Nat := 118140960795 + 505361 * 2 ^ 59
def prefixEnd_505361 : Nat := 4983230072969 + 3 ^ 40 * 505361 * 2
def baseEnd_505361 : Nat := 76886843566489631544709

theorem tailTrace_505361 : CollatzResearch.WordTrace tailWord_505361 prefixEnd_505361 76886843566489631544709 := by
  unfold tailWord_505361
  simp only [CollatzResearch.WordTrace]
  refine ⟨18432029922170880632515937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12288019948113920421677291 18432029922170880632515937)
  ·
    refine ⟨13824022441628160474386953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18432029922170880632515937 13824022441628160474386953)
    ·
      refine ⟨10368016831221120355790215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13824022441628160474386953 10368016831221120355790215)
      ·
        refine ⟨15552025246831680533685323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10368016831221120355790215 15552025246831680533685323)
        ·
          refine ⟨23328037870247520800527985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15552025246831680533685323 23328037870247520800527985)
          ·
            refine ⟨17496028402685640600395989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23328037870247520800527985 17496028402685640600395989)
            ·
              refine ⟨410063165687944701571781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 17496028402685640600395989 410063165687944701571781)
              ·
                refine ⟨76886843566489631544709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 410063165687944701571781 76886843566489631544709)
                ·
                  rfl

theorem cell20_505361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 7, 4].length) (baseStart_505361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505361 prefixEnd_505361 := by exact prefixLift 505361
  have htrace : WordTrace (prefixWord ++ tailWord_505361) baseStart_505361 baseEnd_505361 := by
    simpa [prefixWord, tailWord_505361, baseEnd_505361] using wordTrace_append hprefix tailTrace_505361
  have hstable : (prefixWord ++ tailWord_505361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505361).length < 2 ^ (prefixWord ++ tailWord_505361).sum := by decide
  have hdescent : baseEnd_505361 < baseStart_505361 := by decide
  rcases family_descends (prefixWord ++ tailWord_505361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505374 : List Nat := [4, 3, 3, 1, 1, 1, 7]
def baseStart_505374 : Nat := 118140960795 + 505374 * 2 ^ 59
def prefixEnd_505374 : Nat := 4983230072969 + 3 ^ 40 * 505374 * 2
def baseEnd_505374 : Nat := 25629607139299847466749

theorem tailTrace_505374 : CollatzResearch.WordTrace tailWord_505374 prefixEnd_505374 25629607139299847466749 := by
  unfold tailWord_505374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2304063008890472981592397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12288336047415855901826117 2304063008890472981592397)
  ·
    refine ⟨864023628333927368097149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2304063008890472981592397 864023628333927368097149)
    ·
      refine ⟨324008860625222763036431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 864023628333927368097149 324008860625222763036431)
      ·
        refine ⟨486013290937834144554647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324008860625222763036431 486013290937834144554647)
        ·
          refine ⟨729019936406751216831971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486013290937834144554647 729019936406751216831971)
          ·
            refine ⟨1093529904610126825247957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729019936406751216831971 1093529904610126825247957)
            ·
              refine ⟨25629607139299847466749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1093529904610126825247957 25629607139299847466749)
              ·
                rfl

theorem cell20_505374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 7].length) (baseStart_505374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505374 prefixEnd_505374 := by exact prefixLift 505374
  have htrace : WordTrace (prefixWord ++ tailWord_505374) baseStart_505374 baseEnd_505374 := by
    simpa [prefixWord, tailWord_505374, baseEnd_505374] using wordTrace_append hprefix tailTrace_505374
  have hstable : (prefixWord ++ tailWord_505374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505374).length < 2 ^ (prefixWord ++ tailWord_505374).sum := by decide
  have hdescent : baseEnd_505374 < baseStart_505374 := by decide
  rcases family_descends (prefixWord ++ tailWord_505374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505413 : List Nat := [1, 3, 1, 1, 1, 4, 1, 4, 4]
def baseStart_505413 : Nat := 118140960795 + 505413 * 2 ^ 59
def prefixEnd_505413 : Nat := 4983230072969 + 3 ^ 40 * 505413 * 2
def baseEnd_505413 : Nat := 230684264916387824900581

theorem tailTrace_505413 : CollatzResearch.WordTrace tailWord_505413 prefixEnd_505413 230684264916387824900581 := by
  unfold tailWord_505413
  simp only [CollatzResearch.WordTrace]
  refine ⟨18433926517982493513408893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12289284345321662342272595 18433926517982493513408893)
  ·
    refine ⟨6912722444243435067528335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18433926517982493513408893 6912722444243435067528335)
    ·
      refine ⟨10369083666365152601292503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6912722444243435067528335 10369083666365152601292503)
      ·
        refine ⟨15553625499547728901938755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10369083666365152601292503 15553625499547728901938755)
        ·
          refine ⟨23330438249321593352908133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15553625499547728901938755 23330438249321593352908133)
          ·
            refine ⟨4374457171747798753670275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23330438249321593352908133 4374457171747798753670275)
            ·
              refine ⟨6561685757621698130505413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4374457171747798753670275 6561685757621698130505413)
              ·
                refine ⟨1230316079554068399469765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6561685757621698130505413 1230316079554068399469765)
                ·
                  refine ⟨230684264916387824900581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1230316079554068399469765 230684264916387824900581)
                  ·
                    rfl

theorem cell20_505413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_505413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505413 prefixEnd_505413 := by exact prefixLift 505413
  have htrace : WordTrace (prefixWord ++ tailWord_505413) baseStart_505413 baseEnd_505413 := by
    simpa [prefixWord, tailWord_505413, baseEnd_505413] using wordTrace_append hprefix tailTrace_505413
  have hstable : (prefixWord ++ tailWord_505413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505413).length < 2 ^ (prefixWord ++ tailWord_505413).sum := by decide
  have hdescent : baseEnd_505413 < baseStart_505413 := by decide
  rcases family_descends (prefixWord ++ tailWord_505413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505426 : List Nat := [3, 2, 2, 1, 2, 4, 1, 3, 2]
def baseStart_505426 : Nat := 118140960795 + 505426 * 2 ^ 59
def prefixEnd_505426 : Nat := 4983230072969 + 3 ^ 40 * 505426 * 2
def baseEnd_505426 : Nat := 230690198470617557467195

theorem tailTrace_505426 : CollatzResearch.WordTrace tailWord_505426 prefixEnd_505426 230690198470617557467195 := by
  unfold tailWord_505426
  simp only [CollatzResearch.WordTrace]
  refine ⟨4608600166733849183408033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12289600444623597822421421 4608600166733849183408033)
  ·
    refine ⟨3456450125050386887556025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4608600166733849183408033 3456450125050386887556025)
    ·
      refine ⟨2592337593787790165667019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3456450125050386887556025 2592337593787790165667019)
      ·
        refine ⟨3888506390681685248500529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2592337593787790165667019 3888506390681685248500529)
        ·
          refine ⟨2916379793011263936375397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3888506390681685248500529 2916379793011263936375397)
          ·
            refine ⟨546821211189611988070387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2916379793011263936375397 546821211189611988070387)
            ·
              refine ⟨820231816784417982105581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546821211189611988070387 820231816784417982105581)
              ·
                refine ⟨307586931294156743289593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 820231816784417982105581 307586931294156743289593)
                ·
                  refine ⟨230690198470617557467195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307586931294156743289593 230690198470617557467195)
                  ·
                    rfl

theorem cell20_505426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_505426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505426 prefixEnd_505426 := by exact prefixLift 505426
  have htrace : WordTrace (prefixWord ++ tailWord_505426) baseStart_505426 baseEnd_505426 := by
    simpa [prefixWord, tailWord_505426, baseEnd_505426] using wordTrace_append hprefix tailTrace_505426
  have hstable : (prefixWord ++ tailWord_505426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505426).length < 2 ^ (prefixWord ++ tailWord_505426).sum := by decide
  have hdescent : baseEnd_505426 < baseStart_505426 := by decide
  rcases family_descends (prefixWord ++ tailWord_505426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505444 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 5]
def baseStart_505444 : Nat := 118140960795 + 505444 * 2 ^ 59
def prefixEnd_505444 : Nat := 4983230072969 + 3 ^ 40 * 505444 * 2
def baseEnd_505444 : Nat := 230698414161089494867121

theorem tailTrace_505444 : CollatzResearch.WordTrace tailWord_505444 prefixEnd_505444 230698414161089494867121 := by
  unfold tailWord_505444
  simp only [CollatzResearch.WordTrace]
  refine ⟨9217528590435092903893693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12290038120580123871858257 9217528590435092903893693)
  ·
    refine ⟨3456573221413159838960135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9217528590435092903893693 3456573221413159838960135)
    ·
      refine ⟨5184859832119739758440203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3456573221413159838960135 5184859832119739758440203)
      ·
        refine ⟨7777289748179609637660305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5184859832119739758440203 7777289748179609637660305)
        ·
          refine ⟨5832967311134707228245229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7777289748179609637660305 5832967311134707228245229)
          ·
            refine ⟨2187362741675515210591961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5832967311134707228245229 2187362741675515210591961)
            ·
              refine ⟨1640522056256636407943971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2187362741675515210591961 1640522056256636407943971)
              ·
                refine ⟨2460783084384954611915957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640522056256636407943971 2460783084384954611915957)
                ·
                  refine ⟨230698414161089494867121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2460783084384954611915957 230698414161089494867121)
                  ·
                    rfl

theorem cell20_505444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_505444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505444 prefixEnd_505444 := by exact prefixLift 505444
  have htrace : WordTrace (prefixWord ++ tailWord_505444) baseStart_505444 baseEnd_505444 := by
    simpa [prefixWord, tailWord_505444, baseEnd_505444] using wordTrace_append hprefix tailTrace_505444
  have hstable : (prefixWord ++ tailWord_505444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505444).length < 2 ^ (prefixWord ++ tailWord_505444).sum := by decide
  have hdescent : baseEnd_505444 < baseStart_505444 := by decide
  rcases family_descends (prefixWord ++ tailWord_505444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505454 : List Nat := [4, 1, 2, 2, 3, 1, 2, 5]
def baseStart_505454 : Nat := 118140960795 + 505454 * 2 ^ 59
def prefixEnd_505454 : Nat := 4983230072969 + 3 ^ 40 * 505454 * 2
def baseEnd_505454 : Nat := 76900992811191301511249

theorem tailTrace_505454 : CollatzResearch.WordTrace tailWord_505454 prefixEnd_505454 76900992811191301511249 := by
  unfold tailWord_505454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2304427738854244689456427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12290281273889305010434277 2304427738854244689456427)
  ·
    refine ⟨3456641608281367034184641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2304427738854244689456427 3456641608281367034184641)
    ·
      refine ⟨2592481206211025275638481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3456641608281367034184641 2592481206211025275638481)
      ·
        refine ⟨1944360904658268956728861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2592481206211025275638481 1944360904658268956728861)
        ·
          refine ⟨729135339246850858773323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1944360904658268956728861 729135339246850858773323)
          ·
            refine ⟨1093703008870276288159985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729135339246850858773323 1093703008870276288159985)
            ·
              refine ⟨820277256652707216119989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1093703008870276288159985 820277256652707216119989)
              ·
                refine ⟨76900992811191301511249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 820277256652707216119989 76900992811191301511249)
                ·
                  rfl

theorem cell20_505454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_505454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505454 prefixEnd_505454 := by exact prefixLift 505454
  have htrace : WordTrace (prefixWord ++ tailWord_505454) baseStart_505454 baseEnd_505454 := by
    simpa [prefixWord, tailWord_505454, baseEnd_505454] using wordTrace_append hprefix tailTrace_505454
  have hstable : (prefixWord ++ tailWord_505454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505454).length < 2 ^ (prefixWord ++ tailWord_505454).sum := by decide
  have hdescent : baseEnd_505454 < baseStart_505454 := by decide
  rcases family_descends (prefixWord ++ tailWord_505454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505492 : List Nat := [2, 4, 2, 2, 3, 7]
def baseStart_505492 : Nat := 118140960795 + 505492 * 2 ^ 59
def prefixEnd_505492 : Nat := 4983230072969 + 3 ^ 40 * 505492 * 2
def baseEnd_505492 : Nat := 8545197135889431898775

theorem tailTrace_505492 : CollatzResearch.WordTrace tailWord_505492 prefixEnd_505492 8545197135889431898775 := by
  unfold tailWord_505492
  simp only [CollatzResearch.WordTrace]
  refine ⟨9218403942348145002767365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12291205256464193337023153 9218403942348145002767365)
  ·
    refine ⟨1728450739190277188018881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9218403942348145002767365 1728450739190277188018881)
    ·
      refine ⟨1296338054392707891014161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1728450739190277188018881 1296338054392707891014161)
      ·
        refine ⟨972253540794530918260621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1296338054392707891014161 972253540794530918260621)
        ·
          refine ⟨364595077797949094347733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 972253540794530918260621 364595077797949094347733)
          ·
            refine ⟨8545197135889431898775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 364595077797949094347733 8545197135889431898775)
            ·
              rfl

theorem cell20_505492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 7].length) (baseStart_505492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505492 prefixEnd_505492 := by exact prefixLift 505492
  have htrace : WordTrace (prefixWord ++ tailWord_505492) baseStart_505492 baseEnd_505492 := by
    simpa [prefixWord, tailWord_505492, baseEnd_505492] using wordTrace_append hprefix tailTrace_505492
  have hstable : (prefixWord ++ tailWord_505492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505492).length < 2 ^ (prefixWord ++ tailWord_505492).sum := by decide
  have hdescent : baseEnd_505492 < baseStart_505492 := by decide
  rcases family_descends (prefixWord ++ tailWord_505492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505496 : List Nat := [2, 1, 2, 4, 1, 10]
def baseStart_505496 : Nat := 118140960795 + 505496 * 2 ^ 59
def prefixEnd_505496 : Nat := 4983230072969 + 3 ^ 40 * 505496 * 2
def baseEnd_505496 : Nat := 8545264754741052782725

theorem tailTrace_505496 : CollatzResearch.WordTrace tailWord_505496 prefixEnd_505496 8545264754741052782725 := by
  unfold tailWord_505496
  simp only [CollatzResearch.WordTrace]
  refine ⟨9218476888340899344340171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12291302517787865792453561 9218476888340899344340171)
  ·
    refine ⟨13827715332511349016510257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9218476888340899344340171 13827715332511349016510257)
    ·
      refine ⟨10370786499383511762382693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13827715332511349016510257 10370786499383511762382693)
      ·
        refine ⟨1944522468634408455446755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10370786499383511762382693 1944522468634408455446755)
        ·
          refine ⟨2916783702951612683170133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1944522468634408455446755 2916783702951612683170133)
          ·
            refine ⟨8545264754741052782725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2916783702951612683170133 8545264754741052782725)
            ·
              rfl

theorem cell20_505496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 10].length) (baseStart_505496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505496 prefixEnd_505496 := by exact prefixLift 505496
  have htrace : WordTrace (prefixWord ++ tailWord_505496) baseStart_505496 baseEnd_505496 := by
    simpa [prefixWord, tailWord_505496, baseEnd_505496] using wordTrace_append hprefix tailTrace_505496
  have hstable : (prefixWord ++ tailWord_505496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505496).length < 2 ^ (prefixWord ++ tailWord_505496).sum := by decide
  have hdescent : baseEnd_505496 < baseStart_505496 := by decide
  rcases family_descends (prefixWord ++ tailWord_505496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505502 : List Nat := [4, 3, 1, 1, 1, 3, 1, 4, 2]
def baseStart_505502 : Nat := 118140960795 + 505502 * 2 ^ 59
def prefixEnd_505502 : Nat := 4983230072969 + 3 ^ 40 * 505502 * 2
def baseEnd_505502 : Nat := 230724886941499070933551

theorem tailTrace_505502 : CollatzResearch.WordTrace tailWord_505502 prefixEnd_505502 230724886941499070933551 := by
  unfold tailWord_505502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2304646576832507714174845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12291448409773374475599173 2304646576832507714174845)
  ·
    refine ⟨864242466312190392815567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2304646576832507714174845 864242466312190392815567)
    ·
      refine ⟨1296363699468285589223351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 864242466312190392815567 1296363699468285589223351)
      ·
        refine ⟨1944545549202428383835027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1296363699468285589223351 1944545549202428383835027)
        ·
          refine ⟨2916818323803642575752541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1944545549202428383835027 2916818323803642575752541)
          ·
            refine ⟨1093806871426365965907203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2916818323803642575752541 1093806871426365965907203)
            ·
              refine ⟨1640710307139548948860805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093806871426365965907203 1640710307139548948860805)
              ·
                refine ⟨307633182588665427911401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1640710307139548948860805 307633182588665427911401)
                ·
                  refine ⟨230724886941499070933551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307633182588665427911401 230724886941499070933551)
                  ·
                    rfl

theorem cell20_505502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_505502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505502 prefixEnd_505502 := by exact prefixLift 505502
  have htrace : WordTrace (prefixWord ++ tailWord_505502) baseStart_505502 baseEnd_505502 := by
    simpa [prefixWord, tailWord_505502, baseEnd_505502] using wordTrace_append hprefix tailTrace_505502
  have hstable : (prefixWord ++ tailWord_505502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505502).length < 2 ^ (prefixWord ++ tailWord_505502).sum := by decide
  have hdescent : baseEnd_505502 < baseStart_505502 := by decide
  rcases family_descends (prefixWord ++ tailWord_505502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505520 : List Nat := [2, 1, 1, 1, 2, 1, 6, 3, 3]
def baseStart_505520 : Nat := 118140960795 + 505520 * 2 ^ 59
def prefixEnd_505520 : Nat := 4983230072969 + 3 ^ 40 * 505520 * 2
def baseEnd_505520 : Nat := 230733102631971008333477

theorem tailTrace_505520 : CollatzResearch.WordTrace tailWord_505520 prefixEnd_505520 230733102631971008333477 := by
  unfold tailWord_505520
  simp only [CollatzResearch.WordTrace]
  refine ⟨9218914564297425393777007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12291886085729900525036009 9218914564297425393777007)
  ·
    refine ⟨13828371846446138090665511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9218914564297425393777007 13828371846446138090665511)
    ·
      refine ⟨20742557769669207135998267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13828371846446138090665511 20742557769669207135998267)
      ·
        refine ⟨31113836654503810703997401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20742557769669207135998267 31113836654503810703997401)
        ·
          refine ⟨23335377490877858027998051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31113836654503810703997401 23335377490877858027998051)
          ·
            refine ⟨35003066236316787041997077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23335377490877858027998051 35003066236316787041997077)
            ·
              refine ⟨1640768729827349392593613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35003066236316787041997077 1640768729827349392593613)
              ·
                refine ⟨615288273685256022222605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1640768729827349392593613 615288273685256022222605)
                ·
                  refine ⟨230733102631971008333477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615288273685256022222605 230733102631971008333477)
                  ·
                    rfl

theorem cell20_505520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_505520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505520 prefixEnd_505520 := by exact prefixLift 505520
  have htrace : WordTrace (prefixWord ++ tailWord_505520) baseStart_505520 baseEnd_505520 := by
    simpa [prefixWord, tailWord_505520, baseEnd_505520] using wordTrace_append hprefix tailTrace_505520
  have hstable : (prefixWord ++ tailWord_505520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505520).length < 2 ^ (prefixWord ++ tailWord_505520).sum := by decide
  have hdescent : baseEnd_505520 < baseStart_505520 := by decide
  rcases family_descends (prefixWord ++ tailWord_505520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505527 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 6]
def baseStart_505527 : Nat := 118140960795 + 505527 * 2 ^ 59
def prefixEnd_505527 : Nat := 4983230072969 + 3 ^ 40 * 505527 * 2
def baseEnd_505527 : Nat := 230736297622710095100115

theorem tailTrace_505527 : CollatzResearch.WordTrace tailWord_505527 prefixEnd_505527 230736297622710095100115 := by
  unfold tailWord_505527
  simp only [CollatzResearch.WordTrace]
  refine ⟨18438084439569490983058835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12292056293046327322039223 18438084439569490983058835)
  ·
    refine ⟨27657126659354236474588253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18438084439569490983058835 27657126659354236474588253)
    ·
      refine ⟨10371422497257838677970595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27657126659354236474588253 10371422497257838677970595)
      ·
        refine ⟨15557133745886758016955893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10371422497257838677970595 15557133745886758016955893)
        ·
          refine ⟨1458481288676883564089615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15557133745886758016955893 1458481288676883564089615)
          ·
            refine ⟨2187721933015325346134423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1458481288676883564089615 2187721933015325346134423)
            ·
              refine ⟨3281582899522988019201635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2187721933015325346134423 3281582899522988019201635)
              ·
                refine ⟨4922374349284482028802453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3281582899522988019201635 4922374349284482028802453)
                ·
                  refine ⟨230736297622710095100115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4922374349284482028802453 230736297622710095100115)
                  ·
                    rfl

theorem cell20_505527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 6].length) (baseStart_505527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505527 prefixEnd_505527 := by exact prefixLift 505527
  have htrace : WordTrace (prefixWord ++ tailWord_505527) baseStart_505527 baseEnd_505527 := by
    simpa [prefixWord, tailWord_505527, baseEnd_505527] using wordTrace_append hprefix tailTrace_505527
  have hstable : (prefixWord ++ tailWord_505527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505527).length < 2 ^ (prefixWord ++ tailWord_505527).sum := by decide
  have hdescent : baseEnd_505527 < baseStart_505527 := by decide
  rcases family_descends (prefixWord ++ tailWord_505527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505541 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 7]
def baseStart_505541 : Nat := 118140960795 + 505541 * 2 ^ 59
def prefixEnd_505541 : Nat := 4983230072969 + 3 ^ 40 * 505541 * 2
def baseEnd_505541 : Nat := 230742687604188268633391

theorem tailTrace_505541 : CollatzResearch.WordTrace tailWord_505541 prefixEnd_505541 230742687604188268633391 := by
  unfold tailWord_505541
  simp only [CollatzResearch.WordTrace]
  refine ⟨18438595061518771374068477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12292396707679180916045651 18438595061518771374068477)
  ·
    refine ⟨6914473148069539265275679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18438595061518771374068477 6914473148069539265275679)
    ·
      refine ⟨10371709722104308897913519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6914473148069539265275679 10371709722104308897913519)
      ·
        refine ⟨15557564583156463346870279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10371709722104308897913519 15557564583156463346870279)
        ·
          refine ⟨23336346874734695020305419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15557564583156463346870279 23336346874734695020305419)
          ·
            refine ⟨35004520312102042530458129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23336346874734695020305419 35004520312102042530458129)
            ·
              refine ⟨26253390234076531897843597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35004520312102042530458129 26253390234076531897843597)
              ·
                refine ⟨9845021337778699461691349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26253390234076531897843597 9845021337778699461691349)
                ·
                  refine ⟨230742687604188268633391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9845021337778699461691349 230742687604188268633391)
                  ·
                    rfl

theorem cell20_505541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_505541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505541 prefixEnd_505541 := by exact prefixLift 505541
  have htrace : WordTrace (prefixWord ++ tailWord_505541) baseStart_505541 baseEnd_505541 := by
    simpa [prefixWord, tailWord_505541, baseEnd_505541] using wordTrace_append hprefix tailTrace_505541
  have hstable : (prefixWord ++ tailWord_505541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505541).length < 2 ^ (prefixWord ++ tailWord_505541).sum := by decide
  have hdescent : baseEnd_505541 < baseStart_505541 := by decide
  rcases family_descends (prefixWord ++ tailWord_505541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505554 : List Nat := [3, 2, 2, 2, 2, 3, 1, 2, 3]
def baseStart_505554 : Nat := 118140960795 + 505554 * 2 ^ 59
def prefixEnd_505554 : Nat := 4983230072969 + 3 ^ 40 * 505554 * 2
def baseEnd_505554 : Nat := 230748621158418001200005

theorem tailTrace_505554 : CollatzResearch.WordTrace tailWord_505554 prefixEnd_505554 230748621158418001200005 := by
  unfold tailWord_505554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4609767302617918648572929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12292712806981116396194477 4609767302617918648572929)
  ·
    refine ⟨3457325476963438986429697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4609767302617918648572929 3457325476963438986429697)
    ·
      refine ⟨2592994107722579239822273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3457325476963438986429697 2592994107722579239822273)
      ·
        refine ⟨1944745580791934429866705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2592994107722579239822273 1944745580791934429866705)
        ·
          refine ⟨1458559185593950822400029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1944745580791934429866705 1458559185593950822400029)
          ·
            refine ⟨546959694597731558400011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1458559185593950822400029 546959694597731558400011)
            ·
              refine ⟨820439541896597337600017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546959694597731558400011 820439541896597337600017)
              ·
                refine ⟨615329656422448003200013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 820439541896597337600017 615329656422448003200013)
                ·
                  refine ⟨230748621158418001200005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615329656422448003200013 230748621158418001200005)
                  ·
                    rfl

theorem cell20_505554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_505554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505554 prefixEnd_505554 := by exact prefixLift 505554
  have htrace : WordTrace (prefixWord ++ tailWord_505554) baseStart_505554 baseEnd_505554 := by
    simpa [prefixWord, tailWord_505554, baseEnd_505554] using wordTrace_append hprefix tailTrace_505554
  have hstable : (prefixWord ++ tailWord_505554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505554).length < 2 ^ (prefixWord ++ tailWord_505554).sum := by decide
  have hdescent : baseEnd_505554 < baseStart_505554 := by decide
  rcases family_descends (prefixWord ++ tailWord_505554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505572 : List Nat := [2, 3, 1, 1, 1, 3, 2, 7]
def baseStart_505572 : Nat := 118140960795 + 505572 * 2 ^ 59
def prefixEnd_505572 : Nat := 4983230072969 + 3 ^ 40 * 505572 * 2
def baseEnd_505572 : Nat := 76918945616296646199977

theorem tailTrace_505572 : CollatzResearch.WordTrace tailWord_505572 prefixEnd_505572 76918945616296646199977 := by
  unfold tailWord_505572
  simp only [CollatzResearch.WordTrace]
  refine ⟨9219862862203231834223485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12293150482937642445631313 9219862862203231834223485)
  ·
    refine ⟨3457448573326211937833807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9219862862203231834223485 3457448573326211937833807)
    ·
      refine ⟨5186172859989317906750711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3457448573326211937833807 5186172859989317906750711)
      ·
        refine ⟨7779259289983976860126067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5186172859989317906750711 7779259289983976860126067)
        ·
          refine ⟨11668888934975965290189101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7779259289983976860126067 11668888934975965290189101)
          ·
            refine ⟨4375833350615986983820913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11668888934975965290189101 4375833350615986983820913)
            ·
              refine ⟨3281875012961990237865685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4375833350615986983820913 3281875012961990237865685)
              ·
                refine ⟨76918945616296646199977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3281875012961990237865685 76918945616296646199977)
                ·
                  rfl

theorem cell20_505572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_505572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505572 prefixEnd_505572 := by exact prefixLift 505572
  have htrace : WordTrace (prefixWord ++ tailWord_505572) baseStart_505572 baseEnd_505572 := by
    simpa [prefixWord, tailWord_505572, baseEnd_505572] using wordTrace_append hprefix tailTrace_505572
  have hstable : (prefixWord ++ tailWord_505572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505572).length < 2 ^ (prefixWord ++ tailWord_505572).sum := by decide
  have hdescent : baseEnd_505572 < baseStart_505572 := by decide
  rcases family_descends (prefixWord ++ tailWord_505572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505610 : List Nat := [3, 1, 2, 2, 1, 3, 8]
def baseStart_505610 : Nat := 118140960795 + 505610 * 2 ^ 59
def prefixEnd_505610 : Nat := 4983230072969 + 3 ^ 40 * 505610 * 2
def baseEnd_505610 : Nat := 25641575676036743925901

theorem tailTrace_505610 : CollatzResearch.WordTrace tailWord_505610 prefixEnd_505610 25641575676036743925901 := by
  unfold tailWord_505610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4610277924567199039582571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12294074465512530772220189 4610277924567199039582571)
  ·
    refine ⟨6915416886850798559373857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4610277924567199039582571 6915416886850798559373857)
    ·
      refine ⟨5186562665138098919530393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6915416886850798559373857 5186562665138098919530393)
      ·
        refine ⟨3889921998853574189647795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5186562665138098919530393 3889921998853574189647795)
        ·
          refine ⟨5834882998280361284471693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3889921998853574189647795 5834882998280361284471693)
          ·
            refine ⟨2188081124355135481676885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5834882998280361284471693 2188081124355135481676885)
            ·
              refine ⟨25641575676036743925901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2188081124355135481676885 25641575676036743925901)
              ·
                rfl

theorem cell20_505610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 8].length) (baseStart_505610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505610 prefixEnd_505610 := by exact prefixLift 505610
  have htrace : WordTrace (prefixWord ++ tailWord_505610) baseStart_505610 baseEnd_505610 := by
    simpa [prefixWord, tailWord_505610, baseEnd_505610] using wordTrace_append hprefix tailTrace_505610
  have hstable : (prefixWord ++ tailWord_505610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505610).length < 2 ^ (prefixWord ++ tailWord_505610).sum := by decide
  have hdescent : baseEnd_505610 < baseStart_505610 := by decide
  rcases family_descends (prefixWord ++ tailWord_505610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505655 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 5]
def baseStart_505655 : Nat := 118140960795 + 505655 * 2 ^ 59
def prefixEnd_505655 : Nat := 4983230072969 + 3 ^ 40 * 505655 * 2
def baseEnd_505655 : Nat := 230794720310510538832925

theorem tailTrace_505655 : CollatzResearch.WordTrace tailWord_505655 prefixEnd_505655 230794720310510538832925 := by
  unfold tailWord_505655
  simp only [CollatzResearch.WordTrace]
  refine ⟨18442752983105768843718419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12295168655403845895812279 18442752983105768843718419)
  ·
    refine ⟨27664129474658653265577629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18442752983105768843718419 27664129474658653265577629)
    ·
      refine ⟨10374048552996994974591611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27664129474658653265577629 10374048552996994974591611)
      ·
        refine ⟨15561072829495492461887417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10374048552996994974591611 15561072829495492461887417)
        ·
          refine ⟨11670804622121619346415563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15561072829495492461887417 11670804622121619346415563)
          ·
            refine ⟨17506206933182429019623345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11670804622121619346415563 17506206933182429019623345)
            ·
              refine ⟨13129655199886821764717509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17506206933182429019623345 13129655199886821764717509)
              ·
                refine ⟨2461810349978779080884533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13129655199886821764717509 2461810349978779080884533)
                ·
                  refine ⟨230794720310510538832925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2461810349978779080884533 230794720310510538832925)
                  ·
                    rfl

theorem cell20_505655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_505655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505655 prefixEnd_505655 := by exact prefixLift 505655
  have htrace : WordTrace (prefixWord ++ tailWord_505655) baseStart_505655 baseEnd_505655 := by
    simpa [prefixWord, tailWord_505655, baseEnd_505655] using wordTrace_append hprefix tailTrace_505655
  have hstable : (prefixWord ++ tailWord_505655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505655).length < 2 ^ (prefixWord ++ tailWord_505655).sum := by decide
  have hdescent : baseEnd_505655 < baseStart_505655 := by decide
  rcases family_descends (prefixWord ++ tailWord_505655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505672 : List Nat := [2, 1, 3, 1, 1, 4, 1, 4, 3]
def baseStart_505672 : Nat := 118140960795 + 505672 * 2 ^ 59
def prefixEnd_505672 : Nat := 4983230072969 + 3 ^ 40 * 505672 * 2
def baseEnd_505672 : Nat := 230802479573734035266189

theorem tailTrace_505672 : CollatzResearch.WordTrace tailWord_505672 prefixEnd_505672 230802479573734035266189 := by
  unfold tailWord_505672
  simp only [CollatzResearch.WordTrace]
  refine ⟨9221686512022090373543635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12295582016029453831391513 9221686512022090373543635)
  ·
    refine ⟨13832529768033135560315453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9221686512022090373543635 13832529768033135560315453)
    ·
      refine ⟨5187198663012425835118295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13832529768033135560315453 5187198663012425835118295)
      ·
        refine ⟨7780797994518638752677443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5187198663012425835118295 7780797994518638752677443)
        ·
          refine ⟨11671196991777958129016165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7780797994518638752677443 11671196991777958129016165)
          ·
            refine ⟨2188349435958367149190531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11671196991777958129016165 2188349435958367149190531)
            ·
              refine ⟨3282524153937550723785797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2188349435958367149190531 3282524153937550723785797)
              ·
                refine ⟨615473278863290760709837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3282524153937550723785797 615473278863290760709837)
                ·
                  refine ⟨230802479573734035266189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615473278863290760709837 230802479573734035266189)
                  ·
                    rfl

theorem cell20_505672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_505672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505672 prefixEnd_505672 := by exact prefixLift 505672
  have htrace : WordTrace (prefixWord ++ tailWord_505672) baseStart_505672 baseEnd_505672 := by
    simpa [prefixWord, tailWord_505672, baseEnd_505672] using wordTrace_append hprefix tailTrace_505672
  have hstable : (prefixWord ++ tailWord_505672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505672).length < 2 ^ (prefixWord ++ tailWord_505672).sum := by decide
  have hdescent : baseEnd_505672 < baseStart_505672 := by decide
  rcases family_descends (prefixWord ++ tailWord_505672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505703 : List Nat := [1, 1, 5, 1, 2, 1, 5, 4]
def baseStart_505703 : Nat := 118140960795 + 505703 * 2 ^ 59
def prefixEnd_505703 : Nat := 4983230072969 + 3 ^ 40 * 505703 * 2
def baseEnd_505703 : Nat := 76938876272811901744243

theorem tailTrace_505703 : CollatzResearch.WordTrace tailWord_505703 prefixEnd_505703 76938876272811901744243 := by
  unfold tailWord_505703
  simp only [CollatzResearch.WordTrace]
  refine ⟨18444503686931873041465763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12296335791287915360977175 18444503686931873041465763)
  ·
    refine ⟨27666755530397809562198645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18444503686931873041465763 27666755530397809562198645)
    ·
      refine ⟨2593758330974794646456123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27666755530397809562198645 2593758330974794646456123)
      ·
        refine ⟨3890637496462191969684185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2593758330974794646456123 3890637496462191969684185)
        ·
          refine ⟨2917978122346643977263139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3890637496462191969684185 2917978122346643977263139)
          ·
            refine ⟨4376967183519965965894709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2917978122346643977263139 4376967183519965965894709)
            ·
              refine ⟨410340673454996809302629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4376967183519965965894709 410340673454996809302629)
              ·
                refine ⟨76938876272811901744243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 410340673454996809302629 76938876272811901744243)
                ·
                  rfl

theorem cell20_505703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 4].length) (baseStart_505703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505703 prefixEnd_505703 := by exact prefixLift 505703
  have htrace : WordTrace (prefixWord ++ tailWord_505703) baseStart_505703 baseEnd_505703 := by
    simpa [prefixWord, tailWord_505703, baseEnd_505703] using wordTrace_append hprefix tailTrace_505703
  have hstable : (prefixWord ++ tailWord_505703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505703).length < 2 ^ (prefixWord ++ tailWord_505703).sum := by decide
  have hdescent : baseEnd_505703 < baseStart_505703 := by decide
  rcases family_descends (prefixWord ++ tailWord_505703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505717 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 6]
def baseStart_505717 : Nat := 118140960795 + 505717 * 2 ^ 59
def prefixEnd_505717 : Nat := 4983230072969 + 3 ^ 40 * 505717 * 2
def baseEnd_505717 : Nat := 230823018799913878766005

theorem tailTrace_505717 : CollatzResearch.WordTrace tailWord_505717 prefixEnd_505717 230823018799913878766005 := by
  unfold tailWord_505717
  simp only [CollatzResearch.WordTrace]
  refine ⟨18445014308881153432475405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12296676205920768954983603 18445014308881153432475405)
  ·
    refine ⟨6916880365830432537178277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18445014308881153432475405 6916880365830432537178277)
    ·
      refine ⟨1296915068593206100720927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6916880365830432537178277 1296915068593206100720927)
      ·
        refine ⟨1945372602889809151081391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1296915068593206100720927 1945372602889809151081391)
        ·
          refine ⟨2918058904334713726622087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1945372602889809151081391 2918058904334713726622087)
          ·
            refine ⟨4377088356502070589933131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2918058904334713726622087 4377088356502070589933131)
            ·
              refine ⟨6565632534753105884899697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4377088356502070589933131 6565632534753105884899697)
              ·
                refine ⟨4924224401064829413674773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6565632534753105884899697 4924224401064829413674773)
                ·
                  refine ⟨230823018799913878766005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4924224401064829413674773 230823018799913878766005)
                  ·
                    rfl

theorem cell20_505717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_505717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505717 prefixEnd_505717 := by exact prefixLift 505717
  have htrace : WordTrace (prefixWord ++ tailWord_505717) baseStart_505717 baseEnd_505717 := by
    simpa [prefixWord, tailWord_505717, baseEnd_505717] using wordTrace_append hprefix tailTrace_505717
  have hstable : (prefixWord ++ tailWord_505717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505717).length < 2 ^ (prefixWord ++ tailWord_505717).sum := by decide
  have hdescent : baseEnd_505717 < baseStart_505717 := by decide
  rcases family_descends (prefixWord ++ tailWord_505717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505800 : List Nat := [2, 1, 3, 1, 4, 1, 1, 7]
def baseStart_505800 : Nat := 118140960795 + 505800 * 2 ^ 59
def prefixEnd_505800 : Nat := 4983230072969 + 3 ^ 40 * 505800 * 2
def baseEnd_505800 : Nat := 76953634087178159666333

theorem tailTrace_505800 : CollatzResearch.WordTrace tailWord_505800 prefixEnd_505800 76953634087178159666333 := by
  unfold tailWord_505800
  simp only [CollatzResearch.WordTrace]
  refine ⟨9224020783790229303873427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12298694378386972405164569 9224020783790229303873427)
  ·
    refine ⟨13836031175685343955810141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9224020783790229303873427 13836031175685343955810141)
    ·
      refine ⟨5188511690882003983428803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13836031175685343955810141 5188511690882003983428803)
      ·
        refine ⟨7782767536323005975143205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5188511690882003983428803 7782767536323005975143205)
        ·
          refine ⟨1459268913060563620339351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7782767536323005975143205 1459268913060563620339351)
          ·
            refine ⟨2188903369590845430509027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1459268913060563620339351 2188903369590845430509027)
            ·
              refine ⟨3283355054386268145763541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2188903369590845430509027 3283355054386268145763541)
              ·
                refine ⟨76953634087178159666333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3283355054386268145763541 76953634087178159666333)
                ·
                  rfl

theorem cell20_505800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_505800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505800 prefixEnd_505800 := by exact prefixLift 505800
  have htrace : WordTrace (prefixWord ++ tailWord_505800) baseStart_505800 baseEnd_505800 := by
    simpa [prefixWord, tailWord_505800, baseEnd_505800] using wordTrace_append hprefix tailTrace_505800
  have hstable : (prefixWord ++ tailWord_505800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505800).length < 2 ^ (prefixWord ++ tailWord_505800).sum := by decide
  have hdescent : baseEnd_505800 < baseStart_505800 := by decide
  rcases family_descends (prefixWord ++ tailWord_505800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505838 : List Nat := [4, 1, 2, 1, 3, 9]
def baseStart_505838 : Nat := 118140960795 + 505838 * 2 ^ 59
def prefixEnd_505838 : Nat := 4983230072969 + 3 ^ 40 * 505838 * 2
def baseEnd_505838 : Nat := 8551046166554638360451

theorem tailTrace_505838 : CollatzResearch.WordTrace tailWord_505838 prefixEnd_505838 8551046166554638360451 := by
  unfold tailWord_505838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2306178442680348887203771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12299618360961860731753445 2306178442680348887203771)
  ·
    refine ⟨3459267664020523330805657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2306178442680348887203771 3459267664020523330805657)
    ·
      refine ⟨2594450748015392498104243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3459267664020523330805657 2594450748015392498104243)
      ·
        refine ⟨3891676122023088747156365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2594450748015392498104243 3891676122023088747156365)
        ·
          refine ⟨1459378545758658280183637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3891676122023088747156365 1459378545758658280183637)
          ·
            refine ⟨8551046166554638360451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1459378545758658280183637 8551046166554638360451)
            ·
              rfl

theorem cell20_505838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 9].length) (baseStart_505838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505838 prefixEnd_505838 := by exact prefixLift 505838
  have htrace : WordTrace (prefixWord ++ tailWord_505838) baseStart_505838 baseEnd_505838 := by
    simpa [prefixWord, tailWord_505838, baseEnd_505838] using wordTrace_append hprefix tailTrace_505838
  have hstable : (prefixWord ++ tailWord_505838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505838).length < 2 ^ (prefixWord ++ tailWord_505838).sum := by decide
  have hdescent : baseEnd_505838 < baseStart_505838 := by decide
  rcases family_descends (prefixWord ++ tailWord_505838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505841 : List Nat := [1, 2, 2, 2, 5, 1, 2, 2, 3]
def baseStart_505841 : Nat := 118140960795 + 505841 * 2 ^ 59
def prefixEnd_505841 : Nat := 4983230072969 + 3 ^ 40 * 505841 * 2
def baseEnd_505841 : Nat := 230879615778720558632165

theorem tailTrace_505841 : CollatzResearch.WordTrace tailWord_505841 prefixEnd_505841 230879615778720558632165 := by
  unfold tailWord_505841
  simp only [CollatzResearch.WordTrace]
  refine ⟨18449536960431922609989377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12299691306954615073326251 18449536960431922609989377)
  ·
    refine ⟨13837152720323941957492033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18449536960431922609989377 13837152720323941957492033)
    ·
      refine ⟨10377864540242956468119025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13837152720323941957492033 10377864540242956468119025)
      ·
        refine ⟨7783398405182217351089269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10377864540242956468119025 7783398405182217351089269)
        ·
          refine ⟨729693600485832876664619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7783398405182217351089269 729693600485832876664619)
          ·
            refine ⟨1094540400728749314996929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729693600485832876664619 1094540400728749314996929)
            ·
              refine ⟨820905300546561986247697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1094540400728749314996929 820905300546561986247697)
              ·
                refine ⟨615678975409921489685773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 820905300546561986247697 615678975409921489685773)
                ·
                  refine ⟨230879615778720558632165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615678975409921489685773 230879615778720558632165)
                  ·
                    rfl

theorem cell20_505841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_505841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505841 prefixEnd_505841 := by exact prefixLift 505841
  have htrace : WordTrace (prefixWord ++ tailWord_505841) baseStart_505841 baseEnd_505841 := by
    simpa [prefixWord, tailWord_505841, baseEnd_505841] using wordTrace_append hprefix tailTrace_505841
  have hstable : (prefixWord ++ tailWord_505841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505841).length < 2 ^ (prefixWord ++ tailWord_505841).sum := by decide
  have hdescent : baseEnd_505841 < baseStart_505841 := by decide
  rcases family_descends (prefixWord ++ tailWord_505841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505917 : List Nat := [1, 4, 1, 3, 1, 1, 5, 1, 3]
def baseStart_505917 : Nat := 118140960795 + 505917 * 2 ^ 59
def prefixEnd_505917 : Nat := 4983230072969 + 3 ^ 40 * 505917 * 2
def baseEnd_505917 : Nat := 230914304249602072098521

theorem tailTrace_505917 : CollatzResearch.WordTrace tailWord_505917 prefixEnd_505917 230914304249602072098521 := by
  unfold tailWord_505917
  simp only [CollatzResearch.WordTrace]
  refine ⟨18452308908156587589756005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12301539272104391726504003 18452308908156587589756005)
  ·
    refine ⟨3459807920279360173079251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18452308908156587589756005 3459807920279360173079251)
    ·
      refine ⟨5189711880419040259618877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3459807920279360173079251 5189711880419040259618877)
      ·
        refine ⟨1946141955157140097357079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5189711880419040259618877 1946141955157140097357079)
        ·
          refine ⟨2919212932735710146035619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1946141955157140097357079 2919212932735710146035619)
          ·
            refine ⟨4378819399103565219053429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2919212932735710146035619 4378819399103565219053429)
            ·
              refine ⟨410514318665959239286259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4378819399103565219053429 410514318665959239286259)
              ·
                refine ⟨615771477998938858929389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410514318665959239286259 615771477998938858929389)
                ·
                  refine ⟨230914304249602072098521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615771477998938858929389 230914304249602072098521)
                  ·
                    rfl

theorem cell20_505917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_505917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505917 prefixEnd_505917 := by exact prefixLift 505917
  have htrace : WordTrace (prefixWord ++ tailWord_505917) baseStart_505917 baseEnd_505917 := by
    simpa [prefixWord, tailWord_505917, baseEnd_505917] using wordTrace_append hprefix tailTrace_505917
  have hstable : (prefixWord ++ tailWord_505917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505917).length < 2 ^ (prefixWord ++ tailWord_505917).sum := by decide
  have hdescent : baseEnd_505917 < baseStart_505917 := by decide
  rcases family_descends (prefixWord ++ tailWord_505917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505928 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 6]
def baseStart_505928 : Nat := 118140960795 + 505928 * 2 ^ 59
def prefixEnd_505928 : Nat := 4983230072969 + 3 ^ 40 * 505928 * 2
def baseEnd_505928 : Nat := 230919324949334922731809

theorem tailTrace_505928 : CollatzResearch.WordTrace tailWord_505928 prefixEnd_505928 230919324949334922731809 := by
  unfold tailWord_505928
  simp only [CollatzResearch.WordTrace]
  refine ⟨9226355055558368234203219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12301806740744490978937625 9226355055558368234203219)
  ·
    refine ⟨13839532583337552351304829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9226355055558368234203219 13839532583337552351304829)
    ·
      refine ⟨5189824718751582131739311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13839532583337552351304829 5189824718751582131739311)
      ·
        refine ⟨7784737078127373197608967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5189824718751582131739311 7784737078127373197608967)
        ·
          refine ⟨11677105617191059796413451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7784737078127373197608967 11677105617191059796413451)
          ·
            refine ⟨17515658425786589694620177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11677105617191059796413451 17515658425786589694620177)
            ·
              refine ⟨13136743819339942270965133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17515658425786589694620177 13136743819339942270965133)
              ·
                refine ⟨4926278932252478351611925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13136743819339942270965133 4926278932252478351611925)
                ·
                  refine ⟨230919324949334922731809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4926278932252478351611925 230919324949334922731809)
                  ·
                    rfl

theorem cell20_505928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_505928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505928 prefixEnd_505928 := by exact prefixLift 505928
  have htrace : WordTrace (prefixWord ++ tailWord_505928) baseStart_505928 baseEnd_505928 := by
    simpa [prefixWord, tailWord_505928, baseEnd_505928] using wordTrace_append hprefix tailTrace_505928
  have hstable : (prefixWord ++ tailWord_505928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505928).length < 2 ^ (prefixWord ++ tailWord_505928).sum := by decide
  have hdescent : baseEnd_505928 < baseStart_505928 := by decide
  rcases family_descends (prefixWord ++ tailWord_505928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505935 : List Nat := [1, 1, 2, 1, 1, 2, 2, 10]
def baseStart_505935 : Nat := 118140960795 + 505935 * 2 ^ 59
def prefixEnd_505935 : Nat := 4983230072969 + 3 ^ 40 * 505935 * 2
def baseEnd_505935 : Nat := 76974173313358003166149

theorem tailTrace_505935 : CollatzResearch.WordTrace tailWord_505935 prefixEnd_505935 76974173313358003166149 := by
  unfold tailWord_505935
  simp only [CollatzResearch.WordTrace]
  refine ⟨18452965422091376663911259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12301976948060917775940839 18452965422091376663911259)
  ·
    refine ⟨27679448133137064995866889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18452965422091376663911259 27679448133137064995866889)
    ·
      refine ⟨20759586099852798746900167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27679448133137064995866889 20759586099852798746900167)
      ·
        refine ⟨31139379149779198120350251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20759586099852798746900167 31139379149779198120350251)
        ·
          refine ⟨46709068724668797180525377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31139379149779198120350251 46709068724668797180525377)
          ·
            refine ⟨35031801543501597885394033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46709068724668797180525377 35031801543501597885394033)
            ·
              refine ⟨26273851157626198414045525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35031801543501597885394033 26273851157626198414045525)
              ·
                refine ⟨76974173313358003166149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26273851157626198414045525 76974173313358003166149)
                ·
                  rfl

theorem cell20_505935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 10].length) (baseStart_505935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505935 prefixEnd_505935 := by exact prefixLift 505935
  have htrace : WordTrace (prefixWord ++ tailWord_505935) baseStart_505935 baseEnd_505935 := by
    simpa [prefixWord, tailWord_505935, baseEnd_505935] using wordTrace_append hprefix tailTrace_505935
  have hstable : (prefixWord ++ tailWord_505935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505935).length < 2 ^ (prefixWord ++ tailWord_505935).sum := by decide
  have hdescent : baseEnd_505935 < baseStart_505935 := by decide
  rcases family_descends (prefixWord ++ tailWord_505935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505941 : List Nat := [1, 3, 2, 2, 1, 5, 1, 3, 2]
def baseStart_505941 : Nat := 118140960795 + 505941 * 2 ^ 59
def prefixEnd_505941 : Nat := 4983230072969 + 3 ^ 40 * 505941 * 2
def baseEnd_505941 : Nat := 230925258503564655298423

theorem tailTrace_505941 : CollatzResearch.WordTrace tailWord_505941 prefixEnd_505941 230925258503564655298423 := by
  unfold tailWord_505941
  simp only [CollatzResearch.WordTrace]
  refine ⟨18453184260069639688629677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12302122840046426459086451 18453184260069639688629677)
  ·
    refine ⟨6919944097526114883236129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18453184260069639688629677 6919944097526114883236129)
    ·
      refine ⟨5189958073144586162427097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6919944097526114883236129 5189958073144586162427097)
      ·
        refine ⟨3892468554858439621820323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5189958073144586162427097 3892468554858439621820323)
        ·
          refine ⟨5838702832287659432730485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3892468554858439621820323 5838702832287659432730485)
          ·
            refine ⟨547378390526968071818483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5838702832287659432730485 547378390526968071818483)
            ·
              refine ⟨821067585790452107727725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547378390526968071818483 821067585790452107727725)
              ·
                refine ⟨307900344671419540397897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 821067585790452107727725 307900344671419540397897)
                ·
                  refine ⟨230925258503564655298423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307900344671419540397897 230925258503564655298423)
                  ·
                    rfl

theorem cell20_505941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_505941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505941 prefixEnd_505941 := by exact prefixLift 505941
  have htrace : WordTrace (prefixWord ++ tailWord_505941) baseStart_505941 baseEnd_505941 := by
    simpa [prefixWord, tailWord_505941, baseEnd_505941] using wordTrace_append hprefix tailTrace_505941
  have hstable : (prefixWord ++ tailWord_505941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505941).length < 2 ^ (prefixWord ++ tailWord_505941).sum := by decide
  have hdescent : baseEnd_505941 < baseStart_505941 := by decide
  rcases family_descends (prefixWord ++ tailWord_505941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505952 : List Nat := [2, 1, 1, 3, 2, 5, 6]
def baseStart_505952 : Nat := 118140960795 + 505952 * 2 ^ 59
def prefixEnd_505952 : Nat := 4983230072969 + 3 ^ 40 * 505952 * 2
def baseEnd_505952 : Nat := 25658919911477500659079

theorem tailTrace_505952 : CollatzResearch.WordTrace tailWord_505952 prefixEnd_505952 25658919911477500659079 := by
  unfold tailWord_505952
  simp only [CollatzResearch.WordTrace]
  refine ⟨9226792731514894283640055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12302390308686525711520073 9226792731514894283640055)
  ·
    refine ⟨13840189097272341425460083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9226792731514894283640055 13840189097272341425460083)
    ·
      refine ⟨20760283645908512138190125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13840189097272341425460083 20760283645908512138190125)
      ·
        refine ⟨7785106367215692051821297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20760283645908512138190125 7785106367215692051821297)
        ·
          refine ⟨5838829775411769038865973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7785106367215692051821297 5838829775411769038865973)
          ·
            refine ⟨547390291444853347393685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5838829775411769038865973 547390291444853347393685)
            ·
              refine ⟨25658919911477500659079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 547390291444853347393685 25658919911477500659079)
              ·
                rfl

theorem cell20_505952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 6].length) (baseStart_505952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505952 prefixEnd_505952 := by exact prefixLift 505952
  have htrace : WordTrace (prefixWord ++ tailWord_505952) baseStart_505952 baseEnd_505952 := by
    simpa [prefixWord, tailWord_505952, baseEnd_505952] using wordTrace_append hprefix tailTrace_505952
  have hstable : (prefixWord ++ tailWord_505952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505952).length < 2 ^ (prefixWord ++ tailWord_505952).sum := by decide
  have hdescent : baseEnd_505952 < baseStart_505952 := by decide
  rcases family_descends (prefixWord ++ tailWord_505952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505959 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 5]
def baseStart_505959 : Nat := 118140960795 + 505959 * 2 ^ 59
def prefixEnd_505959 : Nat := 4983230072969 + 3 ^ 40 * 505959 * 2
def baseEnd_505959 : Nat := 230933474194036592698349

theorem tailTrace_505959 : CollatzResearch.WordTrace tailWord_505959 prefixEnd_505959 230933474194036592698349 := by
  unfold tailWord_505959
  simp only [CollatzResearch.WordTrace]
  refine ⟨18453840774004428762784931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12302560516002952508523287 18453840774004428762784931)
  ·
    refine ⟨27680761161006643144177397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18453840774004428762784931 27680761161006643144177397)
    ·
      refine ⟨2595071358844372794766631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27680761161006643144177397 2595071358844372794766631)
      ·
        refine ⟨3892607038266559192149947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2595071358844372794766631 3892607038266559192149947)
        ·
          refine ⟨5838910557399838788224921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3892607038266559192149947 5838910557399838788224921)
          ·
            refine ⟨4379182918049879091168691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5838910557399838788224921 4379182918049879091168691)
            ·
              refine ⟨6568774377074818636753037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4379182918049879091168691 6568774377074818636753037)
              ·
                refine ⟨2463290391403056988782389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6568774377074818636753037 2463290391403056988782389)
                ·
                  refine ⟨230933474194036592698349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2463290391403056988782389 230933474194036592698349)
                  ·
                    rfl

theorem cell20_505959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_505959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_505959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_505959 prefixEnd_505959 := by exact prefixLift 505959
  have htrace : WordTrace (prefixWord ++ tailWord_505959) baseStart_505959 baseEnd_505959 := by
    simpa [prefixWord, tailWord_505959, baseEnd_505959] using wordTrace_append hprefix tailTrace_505959
  have hstable : (prefixWord ++ tailWord_505959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505959).length < 2 ^ (prefixWord ++ tailWord_505959).sum := by decide
  have hdescent : baseEnd_505959 < baseStart_505959 := by decide
  rcases family_descends (prefixWord ++ tailWord_505959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506017 : List Nat := [1, 2, 3, 3, 1, 2, 4, 2, 2]
def baseStart_506017 : Nat := 118140960795 + 506017 * 2 ^ 59
def prefixEnd_506017 : Nat := 4983230072969 + 3 ^ 40 * 506017 * 2
def baseEnd_506017 : Nat := 230959946974446168764779

theorem tailTrace_506017 : CollatzResearch.WordTrace tailWord_506017 prefixEnd_506017 230959946974446168764779 := by
  unfold tailWord_506017
  simp only [CollatzResearch.WordTrace]
  refine ⟨18455956207794304668396305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12303970805196203112264203 18455956207794304668396305)
  ·
    refine ⟨13841967155845728501297229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18455956207794304668396305 13841967155845728501297229)
    ·
      refine ⟨5190737683442148187986461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13841967155845728501297229 5190737683442148187986461)
      ·
        refine ⟨1946526631290805570494923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5190737683442148187986461 1946526631290805570494923)
        ·
          refine ⟨2919789946936208355742385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1946526631290805570494923 2919789946936208355742385)
          ·
            refine ⟨2189842460202156266806789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2919789946936208355742385 2189842460202156266806789)
            ·
              refine ⟨410595461287904300026273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2189842460202156266806789 410595461287904300026273)
              ·
                refine ⟨307946595965928225019705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410595461287904300026273 307946595965928225019705)
                ·
                  refine ⟨230959946974446168764779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307946595965928225019705 230959946974446168764779)
                  ·
                    rfl

theorem cell20_506017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 2].length) (baseStart_506017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506017 prefixEnd_506017 := by exact prefixLift 506017
  have htrace : WordTrace (prefixWord ++ tailWord_506017) baseStart_506017 baseEnd_506017 := by
    simpa [prefixWord, tailWord_506017, baseEnd_506017] using wordTrace_append hprefix tailTrace_506017
  have hstable : (prefixWord ++ tailWord_506017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506017).length < 2 ^ (prefixWord ++ tailWord_506017).sum := by decide
  have hdescent : baseEnd_506017 < baseStart_506017 := by decide
  rcases family_descends (prefixWord ++ tailWord_506017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506042 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 6]
def baseStart_506042 : Nat := 118140960795 + 506042 * 2 ^ 59
def prefixEnd_506042 : Nat := 4983230072969 + 3 ^ 40 * 506042 * 2
def baseEnd_506042 : Nat := 230971357655657192931343

theorem tailTrace_506042 : CollatzResearch.WordTrace tailWord_506042 prefixEnd_506042 230971357655657192931343 := by
  unfold tailWord_506042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4614217008175933484514095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12304578688469155958704253 4614217008175933484514095)
  ·
    refine ⟨6921325512263900226771143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4614217008175933484514095 6921325512263900226771143)
    ·
      refine ⟨10381988268395850340156715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6921325512263900226771143 10381988268395850340156715)
      ·
        refine ⟨15572982402593775510235073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10381988268395850340156715 15572982402593775510235073)
        ·
          refine ⟨11679736801945331632676305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15572982402593775510235073 11679736801945331632676305)
          ·
            refine ⟨8759802601458998724507229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11679736801945331632676305 8759802601458998724507229)
            ·
              refine ⟨3284925975547124521690211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8759802601458998724507229 3284925975547124521690211)
              ·
                refine ⟨4927388963320686782535317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3284925975547124521690211 4927388963320686782535317)
                ·
                  refine ⟨230971357655657192931343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4927388963320686782535317 230971357655657192931343)
                  ·
                    rfl

theorem cell20_506042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_506042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506042 prefixEnd_506042 := by exact prefixLift 506042
  have htrace : WordTrace (prefixWord ++ tailWord_506042) baseStart_506042 baseEnd_506042 := by
    simpa [prefixWord, tailWord_506042, baseEnd_506042] using wordTrace_append hprefix tailTrace_506042
  have hstable : (prefixWord ++ tailWord_506042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506042).length < 2 ^ (prefixWord ++ tailWord_506042).sum := by decide
  have hdescent : baseEnd_506042 < baseStart_506042 := by decide
  rcases family_descends (prefixWord ++ tailWord_506042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506066 : List Nat := [3, 2, 2, 2, 1, 3, 7]
def baseStart_506066 : Nat := 118140960795 + 506066 * 2 ^ 59
def prefixEnd_506066 : Nat := 4983230072969 + 3 ^ 40 * 506066 * 2
def baseEnd_506066 : Nat := 25664701323291086236805

theorem tailTrace_506066 : CollatzResearch.WordTrace tailWord_506066 prefixEnd_506066 25664701323291086236805 := by
  unfold tailWord_506066
  simp only [CollatzResearch.WordTrace]
  refine ⟨4614435846154196509232513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12305162256411190691286701 4614435846154196509232513)
  ·
    refine ⟨3460826884615647381924385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4614435846154196509232513 3460826884615647381924385)
    ·
      refine ⟨2595620163461735536443289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3460826884615647381924385 2595620163461735536443289)
      ·
        refine ⟨1946715122596301652332467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2595620163461735536443289 1946715122596301652332467)
        ·
          refine ⟨2920072683894452478498701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1946715122596301652332467 2920072683894452478498701)
          ·
            refine ⟨1095027256460419679437013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2920072683894452478498701 1095027256460419679437013)
            ·
              refine ⟨25664701323291086236805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1095027256460419679437013 25664701323291086236805)
              ·
                rfl

theorem cell20_506066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 7].length) (baseStart_506066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506066 prefixEnd_506066 := by exact prefixLift 506066
  have htrace : WordTrace (prefixWord ++ tailWord_506066) baseStart_506066 baseEnd_506066 := by
    simpa [prefixWord, tailWord_506066, baseEnd_506066] using wordTrace_append hprefix tailTrace_506066
  have hstable : (prefixWord ++ tailWord_506066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506066).length < 2 ^ (prefixWord ++ tailWord_506066).sum := by decide
  have hdescent : baseEnd_506066 < baseStart_506066 := by decide
  rcases family_descends (prefixWord ++ tailWord_506066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506082 : List Nat := [3, 3, 4, 1, 1, 1, 3, 1, 3]
def baseStart_506082 : Nat := 118140960795 + 506082 * 2 ^ 59
def prefixEnd_506082 : Nat := 4983230072969 + 3 ^ 40 * 506082 * 2
def baseEnd_506082 : Nat := 230989614745594831597847

theorem tailTrace_506082 : CollatzResearch.WordTrace tailWord_506082 prefixEnd_506082 230989614745594831597847 := by
  unfold tailWord_506082
  simp only [CollatzResearch.WordTrace]
  refine ⟨4614581738139705192378125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12305551301705880513008333 4614581738139705192378125)
  ·
    refine ⟨1730468151802389447141797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4614581738139705192378125 1730468151802389447141797)
    ·
      refine ⟨324462778462948021339087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1730468151802389447141797 324462778462948021339087)
      ·
        refine ⟨486694167694422032008631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324462778462948021339087 486694167694422032008631)
        ·
          refine ⟨730041251541633048012947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486694167694422032008631 730041251541633048012947)
          ·
            refine ⟨1095061877312449572019421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730041251541633048012947 1095061877312449572019421)
            ·
              refine ⟨410648203992168589507283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1095061877312449572019421 410648203992168589507283)
              ·
                refine ⟨615972305988252884260925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410648203992168589507283 615972305988252884260925)
                ·
                  refine ⟨230989614745594831597847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 615972305988252884260925 230989614745594831597847)
                  ·
                    rfl

theorem cell20_506082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_506082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506082 prefixEnd_506082 := by exact prefixLift 506082
  have htrace : WordTrace (prefixWord ++ tailWord_506082) baseStart_506082 baseEnd_506082 := by
    simpa [prefixWord, tailWord_506082, baseEnd_506082] using wordTrace_append hprefix tailTrace_506082
  have hstable : (prefixWord ++ tailWord_506082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506082).length < 2 ^ (prefixWord ++ tailWord_506082).sum := by decide
  have hdescent : baseEnd_506082 < baseStart_506082 := by decide
  rcases family_descends (prefixWord ++ tailWord_506082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506135 : List Nat := [1, 1, 3, 4, 1, 2, 3, 1, 4]
def baseStart_506135 : Nat := 118140960795 + 506135 * 2 ^ 59
def prefixEnd_506135 : Nat := 4983230072969 + 3 ^ 40 * 506135 * 2
def baseEnd_506135 : Nat := 231013805389762202830963

theorem tailTrace_506135 : CollatzResearch.WordTrace tailWord_506135 prefixEnd_506135 231013805389762202830963 := by
  unfold tailWord_506135
  simp only [CollatzResearch.WordTrace]
  refine ⟨18460260021366810821191859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12306840014244540547461239 18460260021366810821191859)
  ·
    refine ⟨27690390032050216231787789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18460260021366810821191859 27690390032050216231787789)
    ·
      refine ⟨10383896262018831086920421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27690390032050216231787789 10383896262018831086920421)
      ·
        refine ⟨1946980549128530828797579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10383896262018831086920421 1946980549128530828797579)
        ·
          refine ⟨2920470823692796243196369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1946980549128530828797579 2920470823692796243196369)
          ·
            refine ⟨2190353117769597182397277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2920470823692796243196369 2190353117769597182397277)
            ·
              refine ⟨821382419163598943398979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2190353117769597182397277 821382419163598943398979)
              ·
                refine ⟨1232073628745398415098469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821382419163598943398979 1232073628745398415098469)
                ·
                  refine ⟨231013805389762202830963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1232073628745398415098469 231013805389762202830963)
                  ·
                    rfl

theorem cell20_506135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 4].length) (baseStart_506135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506135 prefixEnd_506135 := by exact prefixLift 506135
  have htrace : WordTrace (prefixWord ++ tailWord_506135) baseStart_506135 baseEnd_506135 := by
    simpa [prefixWord, tailWord_506135, baseEnd_506135] using wordTrace_append hprefix tailTrace_506135
  have hstable : (prefixWord ++ tailWord_506135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506135).length < 2 ^ (prefixWord ++ tailWord_506135).sum := by decide
  have hdescent : baseEnd_506135 < baseStart_506135 := by decide
  rcases family_descends (prefixWord ++ tailWord_506135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506141 : List Nat := [1, 4, 2, 3, 3, 1, 2, 1, 3]
def baseStart_506141 : Nat := 118140960795 + 506141 * 2 ^ 59
def prefixEnd_506141 : Nat := 4983230072969 + 3 ^ 40 * 506141 * 2
def baseEnd_506141 : Nat := 231016543953252848630939

theorem tailTrace_506141 : CollatzResearch.WordTrace tailWord_506141 prefixEnd_506141 231016543953252848630939 := by
  unfold tailWord_506141
  simp only [CollatzResearch.WordTrace]
  refine ⟨18460478859345073845910277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12306985906230049230606851 18460478859345073845910277)
  ·
    refine ⟨3461339786127201346108177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18460478859345073845910277 3461339786127201346108177)
    ·
      refine ⟨2596004839595401009581133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3461339786127201346108177 2596004839595401009581133)
      ·
        refine ⟨973501814848275378592925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2596004839595401009581133 973501814848275378592925)
        ·
          refine ⟨365063180568103266972347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 973501814848275378592925 365063180568103266972347)
          ·
            refine ⟨547594770852154900458521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365063180568103266972347 547594770852154900458521)
            ·
              refine ⟨410696078139116175343891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547594770852154900458521 410696078139116175343891)
              ·
                refine ⟨616044117208674263015837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410696078139116175343891 616044117208674263015837)
                ·
                  refine ⟨231016543953252848630939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616044117208674263015837 231016543953252848630939)
                  ·
                    rfl

theorem cell20_506141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_506141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506141 prefixEnd_506141 := by exact prefixLift 506141
  have htrace : WordTrace (prefixWord ++ tailWord_506141) baseStart_506141 baseEnd_506141 := by
    simpa [prefixWord, tailWord_506141, baseEnd_506141] using wordTrace_append hprefix tailTrace_506141
  have hstable : (prefixWord ++ tailWord_506141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506141).length < 2 ^ (prefixWord ++ tailWord_506141).sum := by decide
  have hdescent : baseEnd_506141 < baseStart_506141 := by decide
  rcases family_descends (prefixWord ++ tailWord_506141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506156 : List Nat := [2, 2, 1, 1, 1, 3, 2, 4, 4]
def baseStart_506156 : Nat := 118140960795 + 506156 * 2 ^ 59
def prefixEnd_506156 : Nat := 4983230072969 + 3 ^ 40 * 506156 * 2
def baseEnd_506156 : Nat := 231023390361979463130877

theorem tailTrace_506156 : CollatzResearch.WordTrace tailWord_506156 prefixEnd_506156 231023390361979463130877 := by
  unfold tailWord_506156
  simp only [CollatzResearch.WordTrace]
  refine ⟨9230512977145365703853161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12307350636193820938470881 9230512977145365703853161)
  ·
    refine ⟨6922884732859024277889871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9230512977145365703853161 6922884732859024277889871)
    ·
      refine ⟨10384327099288536416834807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6922884732859024277889871 10384327099288536416834807)
      ·
        refine ⟨15576490648932804625252211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10384327099288536416834807 15576490648932804625252211)
        ·
          refine ⟨23364735973399206937878317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15576490648932804625252211 23364735973399206937878317)
          ·
            refine ⟨8761775990024702601704369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23364735973399206937878317 8761775990024702601704369)
            ·
              refine ⟨6571331992518526951278277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8761775990024702601704369 6571331992518526951278277)
              ·
                refine ⟨1232124748597223803364677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6571331992518526951278277 1232124748597223803364677)
                ·
                  refine ⟨231023390361979463130877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1232124748597223803364677 231023390361979463130877)
                  ·
                    rfl

theorem cell20_506156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_506156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506156 prefixEnd_506156 := by exact prefixLift 506156
  have htrace : WordTrace (prefixWord ++ tailWord_506156) baseStart_506156 baseEnd_506156 := by
    simpa [prefixWord, tailWord_506156, baseEnd_506156] using wordTrace_append hprefix tailTrace_506156
  have hstable : (prefixWord ++ tailWord_506156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506156).length < 2 ^ (prefixWord ++ tailWord_506156).sum := by decide
  have hdescent : baseEnd_506156 < baseStart_506156 := by decide
  rcases family_descends (prefixWord ++ tailWord_506156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506163 : List Nat := [1, 1, 1, 2, 5, 1, 1, 8]
def baseStart_506163 : Nat := 118140960795 + 506163 * 2 ^ 59
def prefixEnd_506163 : Nat := 4983230072969 + 3 ^ 40 * 506163 * 2
def baseEnd_506163 : Nat := 77008861784239516632505

theorem tailTrace_506163 : CollatzResearch.WordTrace tailWord_506163 prefixEnd_506163 77008861784239516632505 := by
  unfold tailWord_506163
  simp only [CollatzResearch.WordTrace]
  refine ⟨18461281265265371603211143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12307520843510247735474095 18461281265265371603211143)
  ·
    refine ⟨27691921897898057404816715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18461281265265371603211143 27691921897898057404816715)
    ·
      refine ⟨41537882846847086107225073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27691921897898057404816715 41537882846847086107225073)
      ·
        refine ⟨31153412135135314580418805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41537882846847086107225073 31153412135135314580418805)
        ·
          refine ⟨2920632387668935741914263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31153412135135314580418805 2920632387668935741914263)
          ·
            refine ⟨4380948581503403612871395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2920632387668935741914263 4380948581503403612871395)
            ·
              refine ⟨6571422872255105419307093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4380948581503403612871395 6571422872255105419307093)
              ·
                refine ⟨77008861784239516632505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6571422872255105419307093 77008861784239516632505)
                ·
                  rfl

theorem cell20_506163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 8].length) (baseStart_506163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506163 prefixEnd_506163 := by exact prefixLift 506163
  have htrace : WordTrace (prefixWord ++ tailWord_506163) baseStart_506163 baseEnd_506163 := by
    simpa [prefixWord, tailWord_506163, baseEnd_506163] using wordTrace_append hprefix tailTrace_506163
  have hstable : (prefixWord ++ tailWord_506163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506163).length < 2 ^ (prefixWord ++ tailWord_506163).sum := by decide
  have hdescent : baseEnd_506163 < baseStart_506163 := by decide
  rcases family_descends (prefixWord ++ tailWord_506163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506180 : List Nat := [2, 3, 4, 1, 10]
def baseStart_506180 : Nat := 118140960795 + 506180 * 2 ^ 59
def prefixEnd_506180 : Nat := 4983230072969 + 3 ^ 40 * 506180 * 2
def baseEnd_506180 : Nat := 2852275859456074646059

theorem tailTrace_506180 : CollatzResearch.WordTrace tailWord_506180 prefixEnd_506180 2852275859456074646059 := by
  unfold tailWord_506180
  simp only [CollatzResearch.WordTrace]
  refine ⟨9230950653101891753289997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12307934204135855671053329 9230950653101891753289997)
  ·
    refine ⟨3461606494913209407483749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9230950653101891753289997 3461606494913209407483749)
    ·
      refine ⟨649051217796226763903203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3461606494913209407483749 649051217796226763903203)
      ·
        refine ⟨973576826694340145854805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649051217796226763903203 973576826694340145854805)
        ·
          refine ⟨2852275859456074646059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 973576826694340145854805 2852275859456074646059)
          ·
            rfl

theorem cell20_506180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 10].length) (baseStart_506180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506180 prefixEnd_506180 := by exact prefixLift 506180
  have htrace : WordTrace (prefixWord ++ tailWord_506180) baseStart_506180 baseEnd_506180 := by
    simpa [prefixWord, tailWord_506180, baseEnd_506180] using wordTrace_append hprefix tailTrace_506180
  have hstable : (prefixWord ++ tailWord_506180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506180).length < 2 ^ (prefixWord ++ tailWord_506180).sum := by decide
  have hdescent : baseEnd_506180 < baseStart_506180 := by decide
  rcases family_descends (prefixWord ++ tailWord_506180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506197 : List Nat := [1, 3, 2, 2, 4, 2, 1, 5]
def baseStart_506197 : Nat := 118140960795 + 506197 * 2 ^ 59
def prefixEnd_506197 : Nat := 4983230072969 + 3 ^ 40 * 506197 * 2
def baseEnd_506197 : Nat := 77014034626388514254681

theorem tailTrace_506197 : CollatzResearch.WordTrace tailWord_506197 prefixEnd_506197 77014034626388514254681 := by
  unfold tailWord_506197
  simp only [CollatzResearch.WordTrace]
  refine ⟨18462521347142195409948845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12308347564761463606632563 18462521347142195409948845)
  ·
    refine ⟨6923445505178323278730817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18462521347142195409948845 6923445505178323278730817)
    ·
      refine ⟨5192584128883742459048113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6923445505178323278730817 5192584128883742459048113)
      ·
        refine ⟨3894438096662806844286085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5192584128883742459048113 3894438096662806844286085)
        ·
          refine ⟨730207143124276283303641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3894438096662806844286085 730207143124276283303641)
          ·
            refine ⟨547655357343207212477731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 730207143124276283303641 547655357343207212477731)
            ·
              refine ⟨821483036014810818716597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547655357343207212477731 821483036014810818716597)
              ·
                refine ⟨77014034626388514254681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 821483036014810818716597 77014034626388514254681)
                ·
                  rfl

theorem cell20_506197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 5].length) (baseStart_506197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506197 prefixEnd_506197 := by exact prefixLift 506197
  have htrace : WordTrace (prefixWord ++ tailWord_506197) baseStart_506197 baseEnd_506197 := by
    simpa [prefixWord, tailWord_506197, baseEnd_506197] using wordTrace_append hprefix tailTrace_506197
  have hstable : (prefixWord ++ tailWord_506197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506197).length < 2 ^ (prefixWord ++ tailWord_506197).sum := by decide
  have hdescent : baseEnd_506197 < baseStart_506197 := by decide
  rcases family_descends (prefixWord ++ tailWord_506197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506249 : List Nat := [1, 2, 1, 1, 6, 2, 2, 1, 4]
def baseStart_506249 : Nat := 118140960795 + 506249 * 2 ^ 59
def prefixEnd_506249 : Nat := 4983230072969 + 3 ^ 40 * 506249 * 2
def baseEnd_506249 : Nat := 231065838096084473030497

theorem tailTrace_506249 : CollatzResearch.WordTrace tailWord_506249 prefixEnd_506249 231065838096084473030497 := by
  unfold tailWord_506249
  simp only [CollatzResearch.WordTrace]
  refine ⟨18464417942953808290841801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12309611961969205527227867 18464417942953808290841801)
  ·
    refine ⟨13848313457215356218131351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18464417942953808290841801 13848313457215356218131351)
    ·
      refine ⟨20772470185823034327197027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13848313457215356218131351 20772470185823034327197027)
      ·
        refine ⟨31158705278734551490795541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20772470185823034327197027 31158705278734551490795541)
        ·
          refine ⟨1460564309940682101131041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31158705278734551490795541 1460564309940682101131041)
          ·
            refine ⟨1095423232455511575848281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1460564309940682101131041 1095423232455511575848281)
            ·
              refine ⟨821567424341633681886211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1095423232455511575848281 821567424341633681886211)
              ·
                refine ⟨1232351136512450522829317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821567424341633681886211 1232351136512450522829317)
                ·
                  refine ⟨231065838096084473030497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1232351136512450522829317 231065838096084473030497)
                  ·
                    rfl

theorem cell20_506249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_506249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506249 prefixEnd_506249 := by exact prefixLift 506249
  have htrace : WordTrace (prefixWord ++ tailWord_506249) baseStart_506249 baseEnd_506249 := by
    simpa [prefixWord, tailWord_506249, baseEnd_506249] using wordTrace_append hprefix tailTrace_506249
  have hstable : (prefixWord ++ tailWord_506249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506249).length < 2 ^ (prefixWord ++ tailWord_506249).sum := by decide
  have hdescent : baseEnd_506249 < baseStart_506249 := by decide
  rcases family_descends (prefixWord ++ tailWord_506249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506263 : List Nat := [1, 1, 3, 3, 1, 1, 2, 5, 3]
def baseStart_506263 : Nat := 118140960795 + 506263 * 2 ^ 59
def prefixEnd_506263 : Nat := 4983230072969 + 3 ^ 40 * 506263 * 2
def baseEnd_506263 : Nat := 231072228077562646563773

theorem tailTrace_506263 : CollatzResearch.WordTrace tailWord_506263 prefixEnd_506263 231072228077562646563773 := by
  unfold tailWord_506263
  simp only [CollatzResearch.WordTrace]
  refine ⟨18464928564903088681851443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12309952376602059121234295 18464928564903088681851443)
  ·
    refine ⟨27697392847354633022777165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18464928564903088681851443 27697392847354633022777165)
    ·
      refine ⟨10386522317757987383541437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27697392847354633022777165 10386522317757987383541437)
      ·
        refine ⟨3894945869159245268828039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10386522317757987383541437 3894945869159245268828039)
        ·
          refine ⟨5842418803738867903242059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3894945869159245268828039 5842418803738867903242059)
          ·
            refine ⟨8763628205608301854863089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5842418803738867903242059 8763628205608301854863089)
            ·
              refine ⟨6572721154206226391147317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8763628205608301854863089 6572721154206226391147317)
              ·
                refine ⟨616192608206833724170061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6572721154206226391147317 616192608206833724170061)
                ·
                  refine ⟨231072228077562646563773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616192608206833724170061 231072228077562646563773)
                  ·
                    rfl

theorem cell20_506263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 3].length) (baseStart_506263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506263 prefixEnd_506263 := by exact prefixLift 506263
  have htrace : WordTrace (prefixWord ++ tailWord_506263) baseStart_506263 baseEnd_506263 := by
    simpa [prefixWord, tailWord_506263, baseEnd_506263] using wordTrace_append hprefix tailTrace_506263
  have hstable : (prefixWord ++ tailWord_506263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506263).length < 2 ^ (prefixWord ++ tailWord_506263).sum := by decide
  have hdescent : baseEnd_506263 < baseStart_506263 := by decide
  rcases family_descends (prefixWord ++ tailWord_506263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506273 : List Nat := [1, 2, 3, 5, 1, 1, 1, 6]
def baseStart_506273 : Nat := 118140960795 + 506273 * 2 ^ 59
def prefixEnd_506273 : Nat := 4983230072969 + 3 ^ 40 * 506273 * 2
def baseEnd_506273 : Nat := 77025597450015685410133

theorem tailTrace_506273 : CollatzResearch.WordTrace tailWord_506273 prefixEnd_506273 77025597450015685410133 := by
  unfold tailWord_506273
  simp only [CollatzResearch.WordTrace]
  refine ⟨18465293294866860389715473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12310195529911240259810315 18465293294866860389715473)
  ·
    refine ⟨13848969971150145292286605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18465293294866860389715473 13848969971150145292286605)
    ·
      refine ⟨5193363739181304484607477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13848969971150145292286605 5193363739181304484607477)
      ·
        refine ⟨486877850548247295431951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5193363739181304484607477 486877850548247295431951)
        ·
          refine ⟨730316775822370943147927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486877850548247295431951 730316775822370943147927)
          ·
            refine ⟨1095475163733556414721891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730316775822370943147927 1095475163733556414721891)
            ·
              refine ⟨1643212745600334622082837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1095475163733556414721891 1643212745600334622082837)
              ·
                refine ⟨77025597450015685410133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1643212745600334622082837 77025597450015685410133)
                ·
                  rfl

theorem cell20_506273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 6].length) (baseStart_506273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506273 prefixEnd_506273 := by exact prefixLift 506273
  have htrace : WordTrace (prefixWord ++ tailWord_506273) baseStart_506273 baseEnd_506273 := by
    simpa [prefixWord, tailWord_506273, baseEnd_506273] using wordTrace_append hprefix tailTrace_506273
  have hstable : (prefixWord ++ tailWord_506273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506273).length < 2 ^ (prefixWord ++ tailWord_506273).sum := by decide
  have hdescent : baseEnd_506273 < baseStart_506273 := by decide
  rcases family_descends (prefixWord ++ tailWord_506273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506277 : List Nat := [1, 3, 1, 2, 1, 1, 5, 6]
def baseStart_506277 : Nat := 118140960795 + 506277 * 2 ^ 59
def prefixEnd_506277 : Nat := 4983230072969 + 3 ^ 40 * 506277 * 2
def baseEnd_506277 : Nat := 77026206019680273365683

theorem tailTrace_506277 : CollatzResearch.WordTrace tailWord_506277 prefixEnd_506277 77026206019680273365683 := by
  unfold tailWord_506277
  simp only [CollatzResearch.WordTrace]
  refine ⟨18465439186852369072861085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12310292791234912715240723 18465439186852369072861085)
  ·
    refine ⟨6924539695069638402322907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18465439186852369072861085 6924539695069638402322907)
    ·
      refine ⟨10386809542604457603484361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6924539695069638402322907 10386809542604457603484361)
      ·
        refine ⟨7790107156953343202613271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10386809542604457603484361 7790107156953343202613271)
        ·
          refine ⟨11685160735430014803919907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7790107156953343202613271 11685160735430014803919907)
          ·
            refine ⟨17527741103145022205879861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11685160735430014803919907 17527741103145022205879861)
            ·
              refine ⟨1643225728419845831801237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17527741103145022205879861 1643225728419845831801237)
              ·
                refine ⟨77026206019680273365683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1643225728419845831801237 77026206019680273365683)
                ·
                  rfl

theorem cell20_506277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 6].length) (baseStart_506277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506277 prefixEnd_506277 := by exact prefixLift 506277
  have htrace : WordTrace (prefixWord ++ tailWord_506277) baseStart_506277 baseEnd_506277 := by
    simpa [prefixWord, tailWord_506277, baseEnd_506277] using wordTrace_append hprefix tailTrace_506277
  have hstable : (prefixWord ++ tailWord_506277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506277).length < 2 ^ (prefixWord ++ tailWord_506277).sum := by decide
  have hdescent : baseEnd_506277 < baseStart_506277 := by decide
  rcases family_descends (prefixWord ++ tailWord_506277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506280 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 5]
def baseStart_506280 : Nat := 118140960795 + 506280 * 2 ^ 59
def prefixEnd_506280 : Nat := 4983230072969 + 3 ^ 40 * 506280 * 2
def baseEnd_506280 : Nat := 231079987340786142997037

theorem tailTrace_506280 : CollatzResearch.WordTrace tailWord_506280 prefixEnd_506280 231079987340786142997037 := by
  unfold tailWord_506280
  simp only [CollatzResearch.WordTrace]
  refine ⟨9232774302920750292610147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12310365737227667056813529 9232774302920750292610147)
  ·
    refine ⟨13849161454381125438915221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9232774302920750292610147 13849161454381125438915221)
    ·
      refine ⟨649179443174115254949151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13849161454381125438915221 649179443174115254949151)
      ·
        refine ⟨973769164761172882423727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649179443174115254949151 973769164761172882423727)
        ·
          refine ⟨1460653747141759323635591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973769164761172882423727 1460653747141759323635591)
          ·
            refine ⟨2190980620712638985453387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460653747141759323635591 2190980620712638985453387)
            ·
              refine ⟨3286470931068958478180081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2190980620712638985453387 3286470931068958478180081)
              ·
                refine ⟨2464853198301718858635061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3286470931068958478180081 2464853198301718858635061)
                ·
                  refine ⟨231079987340786142997037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2464853198301718858635061 231079987340786142997037)
                  ·
                    rfl

theorem cell20_506280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_506280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506280 prefixEnd_506280 := by exact prefixLift 506280
  have htrace : WordTrace (prefixWord ++ tailWord_506280) baseStart_506280 baseEnd_506280 := by
    simpa [prefixWord, tailWord_506280, baseEnd_506280] using wordTrace_append hprefix tailTrace_506280
  have hstable : (prefixWord ++ tailWord_506280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506280).length < 2 ^ (prefixWord ++ tailWord_506280).sum := by decide
  have hdescent : baseEnd_506280 < baseStart_506280 := by decide
  rcases family_descends (prefixWord ++ tailWord_506280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506301 : List Nat := [1, 4, 1, 2, 2, 2, 2, 1, 5]
def baseStart_506301 : Nat := 118140960795 + 506301 * 2 ^ 59
def prefixEnd_506301 : Nat := 4983230072969 + 3 ^ 40 * 506301 * 2
def baseEnd_506301 : Nat := 231089572313003403296951

theorem tailTrace_506301 : CollatzResearch.WordTrace tailWord_506301 prefixEnd_506301 231089572313003403296951 := by
  unfold tailWord_506301
  simp only [CollatzResearch.WordTrace]
  refine ⟨18466314538765421171734757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12310876359176947447823171 18466314538765421171734757)
  ·
    refine ⟨3462433976018516469700267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18466314538765421171734757 3462433976018516469700267)
    ·
      refine ⟨5193650964027774704550401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3462433976018516469700267 5193650964027774704550401)
      ·
        refine ⟨3895238223020831028412801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5193650964027774704550401 3895238223020831028412801)
        ·
          refine ⟨2921428667265623271309601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3895238223020831028412801 2921428667265623271309601)
          ·
            refine ⟨2191071500449217453482201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2921428667265623271309601 2191071500449217453482201)
            ·
              refine ⟨1643303625336913090111651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2191071500449217453482201 1643303625336913090111651)
              ·
                refine ⟨2464955438005369635167477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1643303625336913090111651 2464955438005369635167477)
                ·
                  refine ⟨231089572313003403296951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2464955438005369635167477 231089572313003403296951)
                  ·
                    rfl

theorem cell20_506301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_506301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506301 prefixEnd_506301 := by exact prefixLift 506301
  have htrace : WordTrace (prefixWord ++ tailWord_506301) baseStart_506301 baseEnd_506301 := by
    simpa [prefixWord, tailWord_506301, baseEnd_506301] using wordTrace_append hprefix tailTrace_506301
  have hstable : (prefixWord ++ tailWord_506301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506301).length < 2 ^ (prefixWord ++ tailWord_506301).sum := by decide
  have hdescent : baseEnd_506301 < baseStart_506301 := by decide
  rcases family_descends (prefixWord ++ tailWord_506301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506407 : List Nat := [1, 1, 7, 2, 2, 1, 1, 2, 3]
def baseStart_506407 : Nat := 118140960795 + 506407 * 2 ^ 59
def prefixEnd_506407 : Nat := 4983230072969 + 3 ^ 40 * 506407 * 2
def baseEnd_506407 : Nat := 231137953601338145763185

theorem tailTrace_506407 : CollatzResearch.WordTrace tailWord_506407 prefixEnd_506407 231137953601338145763185 := by
  unfold tailWord_506407
  simp only [CollatzResearch.WordTrace]
  refine ⟨18470180676381401275093475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12313453784254267516728983 18470180676381401275093475)
  ·
    refine ⟨27705271014572101912640213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18470180676381401275093475 27705271014572101912640213)
    ·
      refine ⟨649342289404033638577505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 27705271014572101912640213 649342289404033638577505)
      ·
        refine ⟨487006717053025228933129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 649342289404033638577505 487006717053025228933129)
        ·
          refine ⟨365255037789768921699847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 487006717053025228933129 365255037789768921699847)
          ·
            refine ⟨547882556684653382549771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365255037789768921699847 547882556684653382549771)
            ·
              refine ⟨821823835026980073824657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547882556684653382549771 821823835026980073824657)
              ·
                refine ⟨616367876270235055368493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 821823835026980073824657 616367876270235055368493)
                ·
                  refine ⟨231137953601338145763185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616367876270235055368493 231137953601338145763185)
                  ·
                    rfl

theorem cell20_506407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 3].length) (baseStart_506407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506407 prefixEnd_506407 := by exact prefixLift 506407
  have htrace : WordTrace (prefixWord ++ tailWord_506407) baseStart_506407 baseEnd_506407 := by
    simpa [prefixWord, tailWord_506407, baseEnd_506407] using wordTrace_append hprefix tailTrace_506407
  have hstable : (prefixWord ++ tailWord_506407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506407).length < 2 ^ (prefixWord ++ tailWord_506407).sum := by decide
  have hdescent : baseEnd_506407 < baseStart_506407 := by decide
  rcases family_descends (prefixWord ++ tailWord_506407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506408 : List Nat := [2, 1, 5, 2, 1, 2, 7]
def baseStart_506408 : Nat := 118140960795 + 506408 * 2 ^ 59
def prefixEnd_506408 : Nat := 4983230072969 + 3 ^ 40 * 506408 * 2
def baseEnd_506408 : Nat := 25682045558731842969983

theorem tailTrace_506408 : CollatzResearch.WordTrace tailWord_506408 prefixEnd_506408 25682045558731842969983 := by
  unfold tailWord_506408
  simp only [CollatzResearch.WordTrace]
  refine ⟨9235108574688889222939939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12313478099585185630586585 9235108574688889222939939)
  ·
    refine ⟨13852662862033333834409909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9235108574688889222939939 13852662862033333834409909)
    ·
      refine ⟨1298687143315625046975929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13852662862033333834409909 1298687143315625046975929)
      ·
        refine ⟨974015357486718785231947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1298687143315625046975929 974015357486718785231947)
        ·
          refine ⟨1461023036230078177847921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974015357486718785231947 1461023036230078177847921)
          ·
            refine ⟨1095767277172558633385941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1461023036230078177847921 1095767277172558633385941)
            ·
              refine ⟨25682045558731842969983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1095767277172558633385941 25682045558731842969983)
              ·
                rfl

theorem cell20_506408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 7].length) (baseStart_506408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506408 prefixEnd_506408 := by exact prefixLift 506408
  have htrace : WordTrace (prefixWord ++ tailWord_506408) baseStart_506408 baseEnd_506408 := by
    simpa [prefixWord, tailWord_506408, baseEnd_506408] using wordTrace_append hprefix tailTrace_506408
  have hstable : (prefixWord ++ tailWord_506408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506408).length < 2 ^ (prefixWord ++ tailWord_506408).sum := by decide
  have hdescent : baseEnd_506408 < baseStart_506408 := by decide
  rcases family_descends (prefixWord ++ tailWord_506408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506446 : List Nat := [4, 1, 1, 1, 1, 2, 6, 4]
def baseStart_506446 : Nat := 118140960795 + 506446 * 2 ^ 59
def prefixEnd_506446 : Nat := 4983230072969 + 3 ^ 40 * 506446 * 2
def baseEnd_506446 : Nat := 77051918088009114487675

theorem tailTrace_506446 : CollatzResearch.WordTrace tailWord_506446 prefixEnd_506446 77051918088009114487675 := by
  unfold tailWord_506446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2308950390405013866970399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12314402082160073957175461 2308950390405013866970399)
  ·
    refine ⟨3463425585607520800455599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2308950390405013866970399 3463425585607520800455599)
    ·
      refine ⟨5195138378411281200683399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3463425585607520800455599 5195138378411281200683399)
      ·
        refine ⟨7792707567616921801025099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5195138378411281200683399 7792707567616921801025099)
        ·
          refine ⟨11689061351425382701537649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7792707567616921801025099 11689061351425382701537649)
          ·
            refine ⟨8766796013569037026153237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11689061351425382701537649 8766796013569037026153237)
            ·
              refine ⟨410943563136048610600933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8766796013569037026153237 410943563136048610600933)
              ·
                refine ⟨77051918088009114487675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 410943563136048610600933 77051918088009114487675)
                ·
                  rfl

theorem cell20_506446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_506446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506446 prefixEnd_506446 := by exact prefixLift 506446
  have htrace : WordTrace (prefixWord ++ tailWord_506446) baseStart_506446 baseEnd_506446 := by
    simpa [prefixWord, tailWord_506446, baseEnd_506446] using wordTrace_append hprefix tailTrace_506446
  have hstable : (prefixWord ++ tailWord_506446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506446).length < 2 ^ (prefixWord ++ tailWord_506446).sum := by decide
  have hdescent : baseEnd_506446 < baseStart_506446 := by decide
  rcases family_descends (prefixWord ++ tailWord_506446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506477 : List Nat := [1, 5, 1, 1, 3, 1, 3, 1, 4]
def baseStart_506477 : Nat := 118140960795 + 506477 * 2 ^ 59
def prefixEnd_506477 : Nat := 4983230072969 + 3 ^ 40 * 506477 * 2
def baseEnd_506477 : Nat := 231169903508729013429565

theorem tailTrace_506477 : CollatzResearch.WordTrace tailWord_506477 prefixEnd_506477 231169903508729013429565 := by
  unfold tailWord_506477
  simp only [CollatzResearch.WordTrace]
  refine ⟨18472733786127803230141685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12315155857418535486761123 18472733786127803230141685)
  ·
    refine ⟨1731818792449481552825783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18472733786127803230141685 1731818792449481552825783)
    ·
      refine ⟨2597728188674222329238675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1731818792449481552825783 2597728188674222329238675)
      ·
        refine ⟨3896592283011333493858013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2597728188674222329238675 3896592283011333493858013)
        ·
          refine ⟨1461222106129250060196755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3896592283011333493858013 1461222106129250060196755)
          ·
            refine ⟨2191833159193875090295133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1461222106129250060196755 2191833159193875090295133)
            ·
              refine ⟨821937434697703158860675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2191833159193875090295133 821937434697703158860675)
              ·
                refine ⟨1232906152046554738291013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821937434697703158860675 1232906152046554738291013)
                ·
                  refine ⟨231169903508729013429565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1232906152046554738291013 231169903508729013429565)
                  ·
                    rfl

theorem cell20_506477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_506477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506477 prefixEnd_506477 := by exact prefixLift 506477
  have htrace : WordTrace (prefixWord ++ tailWord_506477) baseStart_506477 baseEnd_506477 := by
    simpa [prefixWord, tailWord_506477, baseEnd_506477] using wordTrace_append hprefix tailTrace_506477
  have hstable : (prefixWord ++ tailWord_506477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506477).length < 2 ^ (prefixWord ++ tailWord_506477).sum := by decide
  have hdescent : baseEnd_506477 < baseStart_506477 := by decide
  rcases family_descends (prefixWord ++ tailWord_506477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506522 : List Nat := [3, 1, 1, 6, 1, 8]
def baseStart_506522 : Nat := 118140960795 + 506522 * 2 ^ 59
def prefixEnd_506522 : Nat := 4983230072969 + 3 ^ 40 * 506522 * 2
def baseEnd_506522 : Nat := 8562608990181809515903

theorem tailTrace_506522 : CollatzResearch.WordTrace tailWord_506522 prefixEnd_506522 8562608990181809515903 := by
  unfold tailWord_506522
  simp only [CollatzResearch.WordTrace]
  refine ⟨4618593767741193978882455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12316250047309850610353213 4618593767741193978882455)
  ·
    refine ⟨6927890651611790968323683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4618593767741193978882455 6927890651611790968323683)
    ·
      refine ⟨10391835977417686452485525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6927890651611790968323683 10391835977417686452485525)
      ·
        refine ⟨487117311441454052460259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10391835977417686452485525 487117311441454052460259)
        ·
          refine ⟨730675967162181078690389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487117311441454052460259 730675967162181078690389)
          ·
            refine ⟨8562608990181809515903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 730675967162181078690389 8562608990181809515903)
            ·
              rfl

theorem cell20_506522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 8].length) (baseStart_506522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506522 prefixEnd_506522 := by exact prefixLift 506522
  have htrace : WordTrace (prefixWord ++ tailWord_506522) baseStart_506522 baseEnd_506522 := by
    simpa [prefixWord, tailWord_506522, baseEnd_506522] using wordTrace_append hprefix tailTrace_506522
  have hstable : (prefixWord ++ tailWord_506522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506522).length < 2 ^ (prefixWord ++ tailWord_506522).sum := by decide
  have hdescent : baseEnd_506522 < baseStart_506522 := by decide
  rcases family_descends (prefixWord ++ tailWord_506522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506528 : List Nat := [2, 1, 1, 4, 5, 1, 2, 2, 2]
def baseStart_506528 : Nat := 118140960795 + 506528 * 2 ^ 59
def prefixEnd_506528 : Nat := 4983230072969 + 3 ^ 40 * 506528 * 2
def baseEnd_506528 : Nat := 231193181298399502729357

theorem tailTrace_506528 : CollatzResearch.WordTrace tailWord_506528 prefixEnd_506528 231193181298399502729357 := by
  unfold tailWord_506528
  simp only [CollatzResearch.WordTrace]
  refine ⟨9237296954471519470124119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12316395939295359293498825 9237296954471519470124119)
  ·
    refine ⟨13855945431707279205186179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9237296954471519470124119 13855945431707279205186179)
    ·
      refine ⟨20783918147560918807779269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13855945431707279205186179 20783918147560918807779269)
      ·
        refine ⟨3896984652667672276458613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20783918147560918807779269 3896984652667672276458613)
        ·
          refine ⟨365342311187594275917995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3896984652667672276458613 365342311187594275917995)
          ·
            refine ⟨548013466781391413876993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365342311187594275917995 548013466781391413876993)
            ·
              refine ⟨411010100086043560407745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548013466781391413876993 411010100086043560407745)
              ·
                refine ⟨308257575064532670305809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411010100086043560407745 308257575064532670305809)
                ·
                  refine ⟨231193181298399502729357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308257575064532670305809 231193181298399502729357)
                  ·
                    rfl

theorem cell20_506528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 2, 2].length) (baseStart_506528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506528 prefixEnd_506528 := by exact prefixLift 506528
  have htrace : WordTrace (prefixWord ++ tailWord_506528) baseStart_506528 baseEnd_506528 := by
    simpa [prefixWord, tailWord_506528, baseEnd_506528] using wordTrace_append hprefix tailTrace_506528
  have hstable : (prefixWord ++ tailWord_506528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506528).length < 2 ^ (prefixWord ++ tailWord_506528).sum := by decide
  have hdescent : baseEnd_506528 < baseStart_506528 := by decide
  rcases family_descends (prefixWord ++ tailWord_506528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506543 : List Nat := [1, 1, 2, 1, 2, 5, 3, 5]
def baseStart_506543 : Nat := 118140960795 + 506543 * 2 ^ 59
def prefixEnd_506543 : Nat := 4983230072969 + 3 ^ 40 * 506543 * 2
def baseEnd_506543 : Nat := 77066675902375372409765

theorem tailTrace_506543 : CollatzResearch.WordTrace tailWord_506543 prefixEnd_506543 77066675902375372409765 := by
  unfold tailWord_506543
  simp only [CollatzResearch.WordTrace]
  refine ⟨18475141003888696502044283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12316760669259131001362855 18475141003888696502044283)
  ·
    refine ⟨27712711505833044753066425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18475141003888696502044283 27712711505833044753066425)
    ·
      refine ⟨20784533629374783564799819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27712711505833044753066425 20784533629374783564799819)
      ·
        refine ⟨31176800444062175347199729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20784533629374783564799819 31176800444062175347199729)
        ·
          refine ⟨23382600333046631510399797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31176800444062175347199729 23382600333046631510399797)
          ·
            refine ⟨2192118781223121704099981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23382600333046631510399797 2192118781223121704099981)
            ·
              refine ⟨822044542958670639037493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2192118781223121704099981 822044542958670639037493)
              ·
                refine ⟨77066675902375372409765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 822044542958670639037493 77066675902375372409765)
                ·
                  rfl

theorem cell20_506543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 5].length) (baseStart_506543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506543 prefixEnd_506543 := by exact prefixLift 506543
  have htrace : WordTrace (prefixWord ++ tailWord_506543) baseStart_506543 baseEnd_506543 := by
    simpa [prefixWord, tailWord_506543, baseEnd_506543] using wordTrace_append hprefix tailTrace_506543
  have hstable : (prefixWord ++ tailWord_506543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506543).length < 2 ^ (prefixWord ++ tailWord_506543).sum := by decide
  have hdescent : baseEnd_506543 < baseStart_506543 := by decide
  rcases family_descends (prefixWord ++ tailWord_506543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506560 : List Nat := [2, 1, 1, 2, 4, 3, 3, 4]
def baseStart_506560 : Nat := 118140960795 + 506560 * 2 ^ 59
def prefixEnd_506560 : Nat := 4983230072969 + 3 ^ 40 * 506560 * 2
def baseEnd_506560 : Nat := 77069262323449871220853

theorem tailTrace_506560 : CollatzResearch.WordTrace tailWord_506560 prefixEnd_506560 77069262323449871220853 := by
  unfold tailWord_506560
  simp only [CollatzResearch.WordTrace]
  refine ⟨9237880522413554202706567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12317174029884738936942089 9237880522413554202706567)
  ·
    refine ⟨13856820783620331304059851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9237880522413554202706567 13856820783620331304059851)
    ·
      refine ⟨20785231175430496956089777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13856820783620331304059851 20785231175430496956089777)
      ·
        refine ⟨15588923381572872717067333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20785231175430496956089777 15588923381572872717067333)
        ·
          refine ⟨2922923134044913634450125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15588923381572872717067333 2922923134044913634450125)
          ·
            refine ⟨1096096175266842612918797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2922923134044913634450125 1096096175266842612918797)
            ·
              refine ⟨411036065725065979844549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1096096175266842612918797 411036065725065979844549)
              ·
                refine ⟨77069262323449871220853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 411036065725065979844549 77069262323449871220853)
                ·
                  rfl

theorem cell20_506560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 3, 4].length) (baseStart_506560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506560 prefixEnd_506560 := by exact prefixLift 506560
  have htrace : WordTrace (prefixWord ++ tailWord_506560) baseStart_506560 baseEnd_506560 := by
    simpa [prefixWord, tailWord_506560, baseEnd_506560] using wordTrace_append hprefix tailTrace_506560
  have hstable : (prefixWord ++ tailWord_506560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506560).length < 2 ^ (prefixWord ++ tailWord_506560).sum := by decide
  have hdescent : baseEnd_506560 < baseStart_506560 := by decide
  rcases family_descends (prefixWord ++ tailWord_506560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506570 : List Nat := [3, 1, 2, 1, 4, 2, 2, 3, 2]
def baseStart_506570 : Nat := 118140960795 + 506570 * 2 ^ 59
def prefixEnd_506570 : Nat := 4983230072969 + 3 ^ 40 * 506570 * 2
def baseEnd_506570 : Nat := 231212351242834023329185

theorem tailTrace_506570 : CollatzResearch.WordTrace tailWord_506570 prefixEnd_506570 231212351242834023329185 := by
  unfold tailWord_506570
  simp only [CollatzResearch.WordTrace]
  refine ⟨4619031443697720028319291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12317417183193920075518109 4619031443697720028319291)
  ·
    refine ⟨6928547165546580042478937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4619031443697720028319291 6928547165546580042478937)
    ·
      refine ⟨5196410374159935031859203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6928547165546580042478937 5196410374159935031859203)
      ·
        refine ⟨7794615561239902547788805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5196410374159935031859203 7794615561239902547788805)
        ·
          refine ⟨1461490417732481727710401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7794615561239902547788805 1461490417732481727710401)
          ·
            refine ⟨1096117813299361295782801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1461490417732481727710401 1096117813299361295782801)
            ·
              refine ⟨822088359974520971837101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1096117813299361295782801 822088359974520971837101)
              ·
                refine ⟨308283134990445364438913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 822088359974520971837101 308283134990445364438913)
                ·
                  refine ⟨231212351242834023329185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308283134990445364438913 231212351242834023329185)
                  ·
                    rfl

theorem cell20_506570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_506570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506570 prefixEnd_506570 := by exact prefixLift 506570
  have htrace : WordTrace (prefixWord ++ tailWord_506570) baseStart_506570 baseEnd_506570 := by
    simpa [prefixWord, tailWord_506570, baseEnd_506570] using wordTrace_append hprefix tailTrace_506570
  have hstable : (prefixWord ++ tailWord_506570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506570).length < 2 ^ (prefixWord ++ tailWord_506570).sum := by decide
  have hdescent : baseEnd_506570 < baseStart_506570 := by decide
  rcases family_descends (prefixWord ++ tailWord_506570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506580 : List Nat := [2, 4, 1, 3, 3, 1, 1, 2, 3]
def baseStart_506580 : Nat := 118140960795 + 506580 * 2 ^ 59
def prefixEnd_506580 : Nat := 4983230072969 + 3 ^ 40 * 506580 * 2
def baseEnd_506580 : Nat := 231216915515318432995811

theorem tailTrace_506580 : CollatzResearch.WordTrace tailWord_506580 prefixEnd_506580 231216915515318432995811 := by
  unfold tailWord_506580
  simp only [CollatzResearch.WordTrace]
  refine ⟨9238245252377325910570597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12317660336503101214094129 9238245252377325910570597)
  ·
    refine ⟨1732170984820748608231987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9238245252377325910570597 1732170984820748608231987)
    ·
      refine ⟨2598256477231122912347981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1732170984820748608231987 2598256477231122912347981)
      ·
        refine ⟨974346178961671092130493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2598256477231122912347981 974346178961671092130493)
        ·
          refine ⟨365379817110626659548935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 974346178961671092130493 365379817110626659548935)
          ·
            refine ⟨548069725665939989323403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365379817110626659548935 548069725665939989323403)
            ·
              refine ⟨822104588498909983985105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548069725665939989323403 822104588498909983985105)
              ·
                refine ⟨616578441374182487988829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822104588498909983985105 616578441374182487988829)
                ·
                  refine ⟨231216915515318432995811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616578441374182487988829 231216915515318432995811)
                  ·
                    rfl

theorem cell20_506580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_506580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506580 prefixEnd_506580 := by exact prefixLift 506580
  have htrace : WordTrace (prefixWord ++ tailWord_506580) baseStart_506580 baseEnd_506580 := by
    simpa [prefixWord, tailWord_506580, baseEnd_506580] using wordTrace_append hprefix tailTrace_506580
  have hstable : (prefixWord ++ tailWord_506580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506580).length < 2 ^ (prefixWord ++ tailWord_506580).sum := by decide
  have hdescent : baseEnd_506580 < baseStart_506580 := by decide
  rcases family_descends (prefixWord ++ tailWord_506580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506584 : List Nat := [2, 1, 2, 2, 3, 4, 1, 2, 3]
def baseStart_506584 : Nat := 118140960795 + 506584 * 2 ^ 59
def prefixEnd_506584 : Nat := 4983230072969 + 3 ^ 40 * 506584 * 2
def baseEnd_506584 : Nat := 231218741224312196862461

theorem tailTrace_506584 : CollatzResearch.WordTrace tailWord_506584 prefixEnd_506584 231218741224312196862461 := by
  unfold tailWord_506584
  simp only [CollatzResearch.WordTrace]
  refine ⟨9238318198370080252143403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12317757597826773669524537 9238318198370080252143403)
  ·
    refine ⟨13857477297555120378215105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9238318198370080252143403 13857477297555120378215105)
    ·
      refine ⟨10393107973166340283661329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13857477297555120378215105 10393107973166340283661329)
      ·
        refine ⟨7794830979874755212745997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10393107973166340283661329 7794830979874755212745997)
        ·
          refine ⟨2923061617453033204779749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7794830979874755212745997 2923061617453033204779749)
          ·
            refine ⟨548074053272443725896203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2923061617453033204779749 548074053272443725896203)
            ·
              refine ⟨822111079908665588844305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548074053272443725896203 822111079908665588844305)
              ·
                refine ⟨616583309931499191633229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822111079908665588844305 616583309931499191633229)
                ·
                  refine ⟨231218741224312196862461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616583309931499191633229 231218741224312196862461)
                  ·
                    rfl

theorem cell20_506584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 3].length) (baseStart_506584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506584 prefixEnd_506584 := by exact prefixLift 506584
  have htrace : WordTrace (prefixWord ++ tailWord_506584) baseStart_506584 baseEnd_506584 := by
    simpa [prefixWord, tailWord_506584, baseEnd_506584] using wordTrace_append hprefix tailTrace_506584
  have hstable : (prefixWord ++ tailWord_506584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506584).length < 2 ^ (prefixWord ++ tailWord_506584).sum := by decide
  have hdescent : baseEnd_506584 < baseStart_506584 := by decide
  rcases family_descends (prefixWord ++ tailWord_506584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506591 : List Nat := [1, 1, 2, 3, 2, 3, 2, 4, 2]
def baseStart_506591 : Nat := 118140960795 + 506591 * 2 ^ 59
def prefixEnd_506591 : Nat := 4983230072969 + 3 ^ 40 * 506591 * 2
def baseEnd_506591 : Nat := 231221936215051283629099

theorem tailTrace_506591 : CollatzResearch.WordTrace tailWord_506591 prefixEnd_506591 231221936215051283629099 := by
  unfold tailWord_506591
  simp only [CollatzResearch.WordTrace]
  refine ⟨18476891707714800699791627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12317927805143200466527751 18476891707714800699791627)
  ·
    refine ⟨27715337561572201049687441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18476891707714800699791627 27715337561572201049687441)
    ·
      refine ⟨20786503171179150787265581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27715337561572201049687441 20786503171179150787265581)
      ·
        refine ⟨7794938689192181545224593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20786503171179150787265581 7794938689192181545224593)
        ·
          refine ⟨5846204016894136158918445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7794938689192181545224593 5846204016894136158918445)
          ·
            refine ⟨2192326506335301059594417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5846204016894136158918445 2192326506335301059594417)
            ·
              refine ⟨1644244879751475794695813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2192326506335301059594417 1644244879751475794695813)
              ·
                refine ⟨308295914953401711505465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1644244879751475794695813 308295914953401711505465)
                ·
                  refine ⟨231221936215051283629099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308295914953401711505465 231221936215051283629099)
                  ·
                    rfl

theorem cell20_506591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 4, 2].length) (baseStart_506591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506591 prefixEnd_506591 := by exact prefixLift 506591
  have htrace : WordTrace (prefixWord ++ tailWord_506591) baseStart_506591 baseEnd_506591 := by
    simpa [prefixWord, tailWord_506591, baseEnd_506591] using wordTrace_append hprefix tailTrace_506591
  have hstable : (prefixWord ++ tailWord_506591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506591).length < 2 ^ (prefixWord ++ tailWord_506591).sum := by decide
  have hdescent : baseEnd_506591 < baseStart_506591 := by decide
  rcases family_descends (prefixWord ++ tailWord_506591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506633 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 6]
def baseStart_506633 : Nat := 118140960795 + 506633 * 2 ^ 59
def prefixEnd_506633 : Nat := 4983230072969 + 3 ^ 40 * 506633 * 2
def baseEnd_506633 : Nat := 231241106159485804228927

theorem tailTrace_506633 : CollatzResearch.WordTrace tailWord_506633 prefixEnd_506633 231241106159485804228927 := by
  unfold tailWord_506633
  simp only [CollatzResearch.WordTrace]
  refine ⟨18478423573562641872820553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12318949049041761248547035 18478423573562641872820553)
  ·
    refine ⟨13858817680171981404615415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18478423573562641872820553 13858817680171981404615415)
    ·
      refine ⟨20788226520257972106923123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13858817680171981404615415 20788226520257972106923123)
      ·
        refine ⟨31182339780386958160384685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20788226520257972106923123 31182339780386958160384685)
        ·
          refine ⟨11693377417645109310144257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31182339780386958160384685 11693377417645109310144257)
          ·
            refine ⟨8770033063233831982608193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11693377417645109310144257 8770033063233831982608193)
            ·
              refine ⟨6577524797425373986956145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8770033063233831982608193 6577524797425373986956145)
              ·
                refine ⟨4933143598069030490217109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6577524797425373986956145 4933143598069030490217109)
                ·
                  refine ⟨231241106159485804228927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4933143598069030490217109 231241106159485804228927)
                  ·
                    rfl

theorem cell20_506633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_506633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506633 prefixEnd_506633 := by exact prefixLift 506633
  have htrace : WordTrace (prefixWord ++ tailWord_506633) baseStart_506633 baseEnd_506633 := by
    simpa [prefixWord, tailWord_506633, baseEnd_506633] using wordTrace_append hprefix tailTrace_506633
  have hstable : (prefixWord ++ tailWord_506633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506633).length < 2 ^ (prefixWord ++ tailWord_506633).sum := by decide
  have hdescent : baseEnd_506633 < baseStart_506633 := by decide
  rcases family_descends (prefixWord ++ tailWord_506633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506642 : List Nat := [3, 2, 4, 1, 2, 1, 3, 2, 2]
def baseStart_506642 : Nat := 118140960795 + 506642 * 2 ^ 59
def prefixEnd_506642 : Nat := 4983230072969 + 3 ^ 40 * 506642 * 2
def baseEnd_506642 : Nat := 231245214004721772928891

theorem tailTrace_506642 : CollatzResearch.WordTrace tailWord_506642 prefixEnd_506642 231245214004721772928891 := by
  unfold tailWord_506642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4619687957632509102474545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12319167887020024273265453 4619687957632509102474545)
  ·
    refine ⟨3464765968224381826855909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4619687957632509102474545 3464765968224381826855909)
    ·
      refine ⟨649643619042071592535483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3464765968224381826855909 649643619042071592535483)
      ·
        refine ⟨974465428563107388803225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 649643619042071592535483 974465428563107388803225)
        ·
          refine ⟨730849071422330541602419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 974465428563107388803225 730849071422330541602419)
          ·
            refine ⟨1096273607133495812403629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730849071422330541602419 1096273607133495812403629)
            ·
              refine ⟨411102602675060929651361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1096273607133495812403629 411102602675060929651361)
              ·
                refine ⟨308326952006295697238521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411102602675060929651361 308326952006295697238521)
                ·
                  refine ⟨231245214004721772928891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308326952006295697238521 231245214004721772928891)
                  ·
                    rfl

theorem cell20_506642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_506642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506642 prefixEnd_506642 := by exact prefixLift 506642
  have htrace : WordTrace (prefixWord ++ tailWord_506642) baseStart_506642 baseEnd_506642 := by
    simpa [prefixWord, tailWord_506642, baseEnd_506642] using wordTrace_append hprefix tailTrace_506642
  have hstable : (prefixWord ++ tailWord_506642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506642).length < 2 ^ (prefixWord ++ tailWord_506642).sum := by decide
  have hdescent : baseEnd_506642 < baseStart_506642 := by decide
  rcases family_descends (prefixWord ++ tailWord_506642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506653 : List Nat := [1, 4, 2, 4, 1, 1, 2, 5]
def baseStart_506653 : Nat := 118140960795 + 506653 * 2 ^ 59
def prefixEnd_506653 : Nat := 4983230072969 + 3 ^ 40 * 506653 * 2
def baseEnd_506653 : Nat := 77083411568151541187393

theorem tailTrace_506653 : CollatzResearch.WordTrace tailWord_506653 prefixEnd_506653 77083411568151541187393 := by
  unfold tailWord_506653
  simp only [CollatzResearch.WordTrace]
  refine ⟨18479153033490185288548613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12319435355660123525699075 18479153033490185288548613)
  ·
    refine ⟨3464841193779409741602865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18479153033490185288548613 3464841193779409741602865)
    ·
      refine ⟨2598630895334557306202149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3464841193779409741602865 2598630895334557306202149)
      ·
        refine ⟨487243292875229494912903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2598630895334557306202149 487243292875229494912903)
        ·
          refine ⟨730864939312844242369355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487243292875229494912903 730864939312844242369355)
          ·
            refine ⟨1096297408969266363554033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730864939312844242369355 1096297408969266363554033)
            ·
              refine ⟨822223056726949772665525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1096297408969266363554033 822223056726949772665525)
              ·
                refine ⟨77083411568151541187393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 822223056726949772665525 77083411568151541187393)
                ·
                  rfl

theorem cell20_506653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 5].length) (baseStart_506653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506653 prefixEnd_506653 := by exact prefixLift 506653
  have htrace : WordTrace (prefixWord ++ tailWord_506653) baseStart_506653 baseEnd_506653 := by
    simpa [prefixWord, tailWord_506653, baseEnd_506653] using wordTrace_append hprefix tailTrace_506653
  have hstable : (prefixWord ++ tailWord_506653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506653).length < 2 ^ (prefixWord ++ tailWord_506653).sum := by decide
  have hdescent : baseEnd_506653 < baseStart_506653 := by decide
  rcases family_descends (prefixWord ++ tailWord_506653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506657 : List Nat := [1, 2, 3, 2, 1, 2, 4, 5]
def baseStart_506657 : Nat := 118140960795 + 506657 * 2 ^ 59
def prefixEnd_506657 : Nat := 4983230072969 + 3 ^ 40 * 506657 * 2
def baseEnd_506657 : Nat := 77084020137816129142943

theorem tailTrace_506657 : CollatzResearch.WordTrace tailWord_506657 prefixEnd_506657 77084020137816129142943 := by
  unfold tailWord_506657
  simp only [CollatzResearch.WordTrace]
  refine ⟨18479298925475693971694225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12319532616983795981129483 18479298925475693971694225)
  ·
    refine ⟨13859474194106770478770669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18479298925475693971694225 13859474194106770478770669)
    ·
      refine ⟨5197302822790038929539001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13859474194106770478770669 5197302822790038929539001)
      ·
        refine ⟨3897977117092529197154251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5197302822790038929539001 3897977117092529197154251)
        ·
          refine ⟨5846965675638793795731377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3897977117092529197154251 5846965675638793795731377)
          ·
            refine ⟨4385224256729095346798533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5846965675638793795731377 4385224256729095346798533)
            ·
              refine ⟨822229548136705377524725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4385224256729095346798533 822229548136705377524725)
              ·
                refine ⟨77084020137816129142943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 822229548136705377524725 77084020137816129142943)
                ·
                  rfl

theorem cell20_506657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 5].length) (baseStart_506657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506657 prefixEnd_506657 := by exact prefixLift 506657
  have htrace : WordTrace (prefixWord ++ tailWord_506657) baseStart_506657 baseEnd_506657 := by
    simpa [prefixWord, tailWord_506657, baseEnd_506657] using wordTrace_append hprefix tailTrace_506657
  have hstable : (prefixWord ++ tailWord_506657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506657).length < 2 ^ (prefixWord ++ tailWord_506657).sum := by decide
  have hdescent : baseEnd_506657 < baseStart_506657 := by decide
  rcases family_descends (prefixWord ++ tailWord_506657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506660 : List Nat := [2, 3, 1, 3, 3, 1, 1, 3, 3]
def baseStart_506660 : Nat := 118140960795 + 506660 * 2 ^ 59
def prefixEnd_506660 : Nat := 4983230072969 + 3 ^ 40 * 506660 * 2
def baseEnd_506660 : Nat := 231253429695193710328817

theorem tailTrace_506660 : CollatzResearch.WordTrace tailWord_506660 prefixEnd_506660 231253429695193710328817 := by
  unfold tailWord_506660
  simp only [CollatzResearch.WordTrace]
  refine ⟨9239704172232412742026717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12319605562976550322702289 9239704172232412742026717)
  ·
    refine ⟨3464889064587154778260019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9239704172232412742026717 3464889064587154778260019)
    ·
      refine ⟨5197333596880732167390029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3464889064587154778260019 5197333596880732167390029)
      ·
        refine ⟨1949000098830274562771261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5197333596880732167390029 1949000098830274562771261)
        ·
          refine ⟨730875037061352961039223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1949000098830274562771261 730875037061352961039223)
          ·
            refine ⟨1096312555592029441558835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730875037061352961039223 1096312555592029441558835)
            ·
              refine ⟨1644468833388044162338253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096312555592029441558835 1644468833388044162338253)
              ·
                refine ⟨616675812520516560876845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1644468833388044162338253 616675812520516560876845)
                ·
                  refine ⟨231253429695193710328817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616675812520516560876845 231253429695193710328817)
                  ·
                    rfl

theorem cell20_506660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_506660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506660 prefixEnd_506660 := by exact prefixLift 506660
  have htrace : WordTrace (prefixWord ++ tailWord_506660) baseStart_506660 baseEnd_506660 := by
    simpa [prefixWord, tailWord_506660, baseEnd_506660] using wordTrace_append hprefix tailTrace_506660
  have hstable : (prefixWord ++ tailWord_506660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506660).length < 2 ^ (prefixWord ++ tailWord_506660).sum := by decide
  have hdescent : baseEnd_506660 < baseStart_506660 := by decide
  rcases family_descends (prefixWord ++ tailWord_506660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506694 : List Nat := [6, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_506694 : Nat := 118140960795 + 506694 * 2 ^ 59
def prefixEnd_506694 : Nat := 4983230072969 + 3 ^ 40 * 506694 * 2
def baseEnd_506694 : Nat := 231268948221640703195345

theorem tailTrace_506694 : CollatzResearch.WordTrace tailWord_506694 prefixEnd_506694 231268948221640703195345 := by
  unfold tailWord_506694
  simp only [CollatzResearch.WordTrace]
  refine ⟨577520263323176540337223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12320432284227766193860757 577520263323176540337223)
  ·
    refine ⟨866280394984764810505835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 577520263323176540337223 866280394984764810505835)
    ·
      refine ⟨1299420592477147215758753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 866280394984764810505835 1299420592477147215758753)
      ·
        refine ⟨974565444357860411819065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1299420592477147215758753 974565444357860411819065)
        ·
          refine ⟨730924083268395308864299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 974565444357860411819065 730924083268395308864299)
          ·
            refine ⟨1096386124902592963296449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730924083268395308864299 1096386124902592963296449)
            ·
              refine ⟨822289593676944722472337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1096386124902592963296449 822289593676944722472337)
              ·
                refine ⟨616717195257708541854253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822289593676944722472337 616717195257708541854253)
                ·
                  refine ⟨231268948221640703195345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616717195257708541854253 231268948221640703195345)
                  ·
                    rfl

theorem cell20_506694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_506694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506694 prefixEnd_506694 := by exact prefixLift 506694
  have htrace : WordTrace (prefixWord ++ tailWord_506694) baseStart_506694 baseEnd_506694 := by
    simpa [prefixWord, tailWord_506694, baseEnd_506694] using wordTrace_append hprefix tailTrace_506694
  have hstable : (prefixWord ++ tailWord_506694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506694).length < 2 ^ (prefixWord ++ tailWord_506694).sum := by decide
  have hdescent : baseEnd_506694 < baseStart_506694 := by decide
  rcases family_descends (prefixWord ++ tailWord_506694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506701 : List Nat := [1, 6, 1, 2, 2, 1, 1, 4, 2]
def baseStart_506701 : Nat := 118140960795 + 506701 * 2 ^ 59
def prefixEnd_506701 : Nat := 4983230072969 + 3 ^ 40 * 506701 * 2
def baseEnd_506701 : Nat := 231272143212379789961983

theorem tailTrace_506701 : CollatzResearch.WordTrace tailWord_506701 prefixEnd_506701 231272143212379789961983 := by
  unfold tailWord_506701
  simp only [CollatzResearch.WordTrace]
  refine ⟨18480903737316289486295957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12320602491544192990863971 18480903737316289486295957)
  ·
    refine ⟨866292362686701069670123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18480903737316289486295957 866292362686701069670123)
    ·
      refine ⟨1299438544030051604505185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 866292362686701069670123 1299438544030051604505185)
      ·
        refine ⟨974578908022538703378889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1299438544030051604505185 974578908022538703378889)
        ·
          refine ⟨730934181016904027534167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 974578908022538703378889 730934181016904027534167)
          ·
            refine ⟨1096401271525356041301251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 730934181016904027534167 1096401271525356041301251)
            ·
              refine ⟨1644601907288034061951877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1096401271525356041301251 1644601907288034061951877)
              ·
                refine ⟨308362857616506386615977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1644601907288034061951877 308362857616506386615977)
                ·
                  refine ⟨231272143212379789961983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308362857616506386615977 231272143212379789961983)
                  ·
                    rfl

theorem cell20_506701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_506701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506701 prefixEnd_506701 := by exact prefixLift 506701
  have htrace : WordTrace (prefixWord ++ tailWord_506701) baseStart_506701 baseEnd_506701 := by
    simpa [prefixWord, tailWord_506701, baseEnd_506701] using wordTrace_append hprefix tailTrace_506701
  have hstable : (prefixWord ++ tailWord_506701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506701).length < 2 ^ (prefixWord ++ tailWord_506701).sum := by decide
  have hdescent : baseEnd_506701 < baseStart_506701 := by decide
  rcases family_descends (prefixWord ++ tailWord_506701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506702 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_506702 : Nat := 118140960795 + 506702 * 2 ^ 59
def prefixEnd_506702 : Nat := 4983230072969 + 3 ^ 40 * 506702 * 2
def baseEnd_506702 : Nat := 231272599639628230928645

theorem tailTrace_506702 : CollatzResearch.WordTrace tailWord_506702 prefixEnd_506702 231272599639628230928645 := by
  unfold tailWord_506702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2310117526289083332135295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12320626806875111104721573 2310117526289083332135295)
  ·
    refine ⟨3465176289433624998202943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2310117526289083332135295 3465176289433624998202943)
    ·
      refine ⟨5197764434150437497304415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3465176289433624998202943 5197764434150437497304415)
      ·
        refine ⟨7796646651225656245956623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5197764434150437497304415 7796646651225656245956623)
        ·
          refine ⟨11694969976838484368934935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7796646651225656245956623 11694969976838484368934935)
          ·
            refine ⟨17542454965257726553402403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11694969976838484368934935 17542454965257726553402403)
            ·
              refine ⟨26313682447886589830103605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17542454965257726553402403 26313682447886589830103605)
              ·
                refine ⟨2466907729489367796572213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26313682447886589830103605 2466907729489367796572213)
                ·
                  refine ⟨231272599639628230928645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2466907729489367796572213 231272599639628230928645)
                  ·
                    rfl

theorem cell20_506702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_506702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506702 prefixEnd_506702 := by exact prefixLift 506702
  have htrace : WordTrace (prefixWord ++ tailWord_506702) baseStart_506702 baseEnd_506702 := by
    simpa [prefixWord, tailWord_506702, baseEnd_506702] using wordTrace_append hprefix tailTrace_506702
  have hstable : (prefixWord ++ tailWord_506702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506702).length < 2 ^ (prefixWord ++ tailWord_506702).sum := by decide
  have hdescent : baseEnd_506702 < baseStart_506702 := by decide
  rcases family_descends (prefixWord ++ tailWord_506702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506757 : List Nat := [1, 3, 1, 1, 3, 3, 3, 2, 3]
def baseStart_506757 : Nat := 118140960795 + 506757 * 2 ^ 59
def prefixEnd_506757 : Nat := 4983230072969 + 3 ^ 40 * 506757 * 2
def baseEnd_506757 : Nat := 231297703138292484095087

theorem tailTrace_506757 : CollatzResearch.WordTrace tailWord_506757 prefixEnd_506757 231297703138292484095087 := by
  unfold tailWord_506757
  simp only [CollatzResearch.WordTrace]
  refine ⟨18482946225113411050334525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12321964150075607366889683 18482946225113411050334525)
  ·
    refine ⟨6931104834417529143875447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18482946225113411050334525 6931104834417529143875447)
    ·
      refine ⟨10396657251626293715813171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6931104834417529143875447 10396657251626293715813171)
      ·
        refine ⟨15594985877439440573719757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10396657251626293715813171 15594985877439440573719757)
        ·
          refine ⟨5848119704039790215144909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15594985877439440573719757 5848119704039790215144909)
          ·
            refine ⟨2193044889014921330679341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5848119704039790215144909 2193044889014921330679341)
            ·
              refine ⟨822391833380595499004753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2193044889014921330679341 822391833380595499004753)
              ·
                refine ⟨616793875035446624253565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 822391833380595499004753 616793875035446624253565)
                ·
                  refine ⟨231297703138292484095087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 616793875035446624253565 231297703138292484095087)
                  ·
                    rfl

theorem cell20_506757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_506757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506757 prefixEnd_506757 := by exact prefixLift 506757
  have htrace : WordTrace (prefixWord ++ tailWord_506757) baseStart_506757 baseEnd_506757 := by
    simpa [prefixWord, tailWord_506757, baseEnd_506757] using wordTrace_append hprefix tailTrace_506757
  have hstable : (prefixWord ++ tailWord_506757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506757).length < 2 ^ (prefixWord ++ tailWord_506757).sum := by decide
  have hdescent : baseEnd_506757 < baseStart_506757 := by decide
  rcases family_descends (prefixWord ++ tailWord_506757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506809 : List Nat := [1, 2, 1, 4, 2, 4, 6]
def baseStart_506809 : Nat := 118140960795 + 506809 * 2 ^ 59
def prefixEnd_506809 : Nat := 4983230072969 + 3 ^ 40 * 506809 * 2
def baseEnd_506809 : Nat := 25702381928356823817949

theorem tailTrace_506809 : CollatzResearch.WordTrace tailWord_506809 prefixEnd_506809 25702381928356823817949 := by
  unfold tailWord_506809
  simp only [CollatzResearch.WordTrace]
  refine ⟨18484842820925023931227481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12323228547283349287484987 18484842820925023931227481)
  ·
    refine ⟨13863632115693767948420611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18484842820925023931227481 13863632115693767948420611)
    ·
      refine ⟨20795448173540651922630917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13863632115693767948420611 20795448173540651922630917)
      ·
        refine ⟨3899146532538872235493297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20795448173540651922630917 3899146532538872235493297)
        ·
          refine ⟨2924359899404154176619973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3899146532538872235493297 2924359899404154176619973)
          ·
            refine ⟨548317481138278908116245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2924359899404154176619973 548317481138278908116245)
            ·
              refine ⟨25702381928356823817949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 548317481138278908116245 25702381928356823817949)
              ·
                rfl

theorem cell20_506809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 6].length) (baseStart_506809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506809 prefixEnd_506809 := by exact prefixLift 506809
  have htrace : WordTrace (prefixWord ++ tailWord_506809) baseStart_506809 baseEnd_506809 := by
    simpa [prefixWord, tailWord_506809, baseEnd_506809] using wordTrace_append hprefix tailTrace_506809
  have hstable : (prefixWord ++ tailWord_506809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506809).length < 2 ^ (prefixWord ++ tailWord_506809).sum := by decide
  have hdescent : baseEnd_506809 < baseStart_506809 := by decide
  rcases family_descends (prefixWord ++ tailWord_506809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506816 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 5]
def baseStart_506816 : Nat := 118140960795 + 506816 * 2 ^ 59
def prefixEnd_506816 : Nat := 4983230072969 + 3 ^ 40 * 506816 * 2
def baseEnd_506816 : Nat := 231324632345950501128179

theorem tailTrace_506816 : CollatzResearch.WordTrace tailWord_506816 prefixEnd_506816 231324632345950501128179 := by
  unfold tailWord_506816
  simp only [CollatzResearch.WordTrace]
  refine ⟨9242549065949832063366151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12323398754599776084488201 9242549065949832063366151)
  ·
    refine ⟨13863823598924748095049227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9242549065949832063366151 13863823598924748095049227)
    ·
      refine ⟨20795735398387122142573841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13863823598924748095049227 20795735398387122142573841)
      ·
        refine ⟨15596801548790341606930381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20795735398387122142573841 15596801548790341606930381)
        ·
          refine ⟨5848800580796378102598893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15596801548790341606930381 5848800580796378102598893)
          ·
            refine ⟨2193300217798641788474585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5848800580796378102598893 2193300217798641788474585)
            ·
              refine ⟨1644975163348981341355939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2193300217798641788474585 1644975163348981341355939)
              ·
                refine ⟨2467462745023472012033909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1644975163348981341355939 2467462745023472012033909)
                ·
                  refine ⟨231324632345950501128179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2467462745023472012033909 231324632345950501128179)
                  ·
                    rfl

theorem cell20_506816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_506816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506816 prefixEnd_506816 := by exact prefixLift 506816
  have htrace : WordTrace (prefixWord ++ tailWord_506816) baseStart_506816 baseEnd_506816 := by
    simpa [prefixWord, tailWord_506816, baseEnd_506816] using wordTrace_append hprefix tailTrace_506816
  have hstable : (prefixWord ++ tailWord_506816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506816).length < 2 ^ (prefixWord ++ tailWord_506816).sum := by decide
  have hdescent : baseEnd_506816 < baseStart_506816 := by decide
  rcases family_descends (prefixWord ++ tailWord_506816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506930 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_506930 : Nat := 118140960795 + 506930 * 2 ^ 59
def prefixEnd_506930 : Nat := 4983230072969 + 3 ^ 40 * 506930 * 2
def baseEnd_506930 : Nat := 231376665052272771327713

theorem tailTrace_506930 : CollatzResearch.WordTrace tailWord_506930 prefixEnd_506930 231376665052272771327713 := by
  unfold tailWord_506930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4622314013371665399095561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12326170702324441064254829 4622314013371665399095561)
  ·
    refine ⟨3466735510028749049321671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4622314013371665399095561 3466735510028749049321671)
    ·
      refine ⟨5200103265043123573982507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3466735510028749049321671 5200103265043123573982507)
      ·
        refine ⟨7800154897564685360973761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5200103265043123573982507 7800154897564685360973761)
        ·
          refine ⟨5850116173173514020730321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7800154897564685360973761 5850116173173514020730321)
          ·
            refine ⟨4387587129880135515547741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5850116173173514020730321 4387587129880135515547741)
            ·
              refine ⟨1645345173705050818330403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4387587129880135515547741 1645345173705050818330403)
              ·
                refine ⟨2468017760557576227495605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1645345173705050818330403 2468017760557576227495605)
                ·
                  refine ⟨231376665052272771327713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2468017760557576227495605 231376665052272771327713)
                  ·
                    rfl

theorem cell20_506930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_506930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506930 prefixEnd_506930 := by exact prefixLift 506930
  have htrace : WordTrace (prefixWord ++ tailWord_506930) baseStart_506930 baseEnd_506930 := by
    simpa [prefixWord, tailWord_506930, baseEnd_506930] using wordTrace_append hprefix tailTrace_506930
  have hstable : (prefixWord ++ tailWord_506930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506930).length < 2 ^ (prefixWord ++ tailWord_506930).sum := by decide
  have hdescent : baseEnd_506930 < baseStart_506930 := by decide
  rcases family_descends (prefixWord ++ tailWord_506930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506944 : List Nat := [2, 1, 1, 2, 2, 3, 2, 7]
def baseStart_506944 : Nat := 118140960795 + 506944 * 2 ^ 59
def prefixEnd_506944 : Nat := 4983230072969 + 3 ^ 40 * 506944 * 2
def baseEnd_506944 : Nat := 77127685011250314953663

theorem tailTrace_506944 : CollatzResearch.WordTrace tailWord_506944 prefixEnd_506944 77127685011250314953663 := by
  unfold tailWord_506944
  simp only [CollatzResearch.WordTrace]
  refine ⟨9244883337717970993695943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12326511116957294658261257 9244883337717970993695943)
  ·
    refine ⟨13867325006576956490543915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9244883337717970993695943 13867325006576956490543915)
    ·
      refine ⟨20800987509865434735815873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13867325006576956490543915 20800987509865434735815873)
      ·
        refine ⟨15600740632399076051861905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20800987509865434735815873 15600740632399076051861905)
        ·
          refine ⟨11700555474299307038896429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15600740632399076051861905 11700555474299307038896429)
          ·
            refine ⟨4387708302862240139586161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11700555474299307038896429 4387708302862240139586161)
            ·
              refine ⟨3290781227146680104689621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4387708302862240139586161 3290781227146680104689621)
              ·
                refine ⟨77127685011250314953663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3290781227146680104689621 77127685011250314953663)
                ·
                  rfl

theorem cell20_506944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_506944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506944 prefixEnd_506944 := by exact prefixLift 506944
  have htrace : WordTrace (prefixWord ++ tailWord_506944) baseStart_506944 baseEnd_506944 := by
    simpa [prefixWord, tailWord_506944, baseEnd_506944] using wordTrace_append hprefix tailTrace_506944
  have hstable : (prefixWord ++ tailWord_506944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506944).length < 2 ^ (prefixWord ++ tailWord_506944).sum := by decide
  have hdescent : baseEnd_506944 < baseStart_506944 := by decide
  rcases family_descends (prefixWord ++ tailWord_506944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506947 : List Nat := [1, 1, 1, 3, 1, 2, 7, 1, 3]
def baseStart_506947 : Nat := 118140960795 + 506947 * 2 ^ 59
def prefixEnd_506947 : Nat := 4983230072969 + 3 ^ 40 * 506947 * 2
def baseEnd_506947 : Nat := 231384424315496267760977

theorem tailTrace_506947 : CollatzResearch.WordTrace tailWord_506947 prefixEnd_506947 231384424315496267760977 := by
  unfold tailWord_506947
  simp only [CollatzResearch.WordTrace]
  refine ⟨18489876094425073499751095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12326584062950048999834063 18489876094425073499751095)
  ·
    refine ⟨27734814141637610249626643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18489876094425073499751095 27734814141637610249626643)
    ·
      refine ⟨41602221212456415374439965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27734814141637610249626643 41602221212456415374439965)
      ·
        refine ⟨15600832954671155765414987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41602221212456415374439965 15600832954671155765414987)
        ·
          refine ⟨23401249432006733648122481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15600832954671155765414987 23401249432006733648122481)
          ·
            refine ⟨17550937074005050236091861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23401249432006733648122481 17550937074005050236091861)
            ·
              refine ⟨411350087671993364908403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 17550937074005050236091861 411350087671993364908403)
              ·
                refine ⟨617025131507990047362605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411350087671993364908403 617025131507990047362605)
                ·
                  refine ⟨231384424315496267760977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 617025131507990047362605 231384424315496267760977)
                  ·
                    rfl

theorem cell20_506947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 3].length) (baseStart_506947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506947 prefixEnd_506947 := by exact prefixLift 506947
  have htrace : WordTrace (prefixWord ++ tailWord_506947) baseStart_506947 baseEnd_506947 := by
    simpa [prefixWord, tailWord_506947, baseEnd_506947] using wordTrace_append hprefix tailTrace_506947
  have hstable : (prefixWord ++ tailWord_506947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506947).length < 2 ^ (prefixWord ++ tailWord_506947).sum := by decide
  have hdescent : baseEnd_506947 < baseStart_506947 := by decide
  rcases family_descends (prefixWord ++ tailWord_506947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506957 : List Nat := [1, 6, 1, 1, 1, 4, 2, 4]
def baseStart_506957 : Nat := 118140960795 + 506957 * 2 ^ 59
def prefixEnd_506957 : Nat := 4983230072969 + 3 ^ 40 * 506957 * 2
def baseEnd_506957 : Nat := 77129662862660225809201

theorem tailTrace_506957 : CollatzResearch.WordTrace tailWord_506957 prefixEnd_506957 77129662862660225809201 := by
  unfold tailWord_506957
  simp only [CollatzResearch.WordTrace]
  refine ⟨18490240824388845207615125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12326827216259230138410083 18490240824388845207615125)
  ·
    refine ⟨866730038643227119106959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18490240824388845207615125 866730038643227119106959)
    ·
      refine ⟨1300095057964840678660439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 866730038643227119106959 1300095057964840678660439)
      ·
        refine ⟨1950142586947261017990659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1300095057964840678660439 1950142586947261017990659)
        ·
          refine ⟨2925213880420891526985989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1950142586947261017990659 2925213880420891526985989)
          ·
            refine ⟨548477602578917161309873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2925213880420891526985989 548477602578917161309873)
            ·
              refine ⟨411358201934187870982405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548477602578917161309873 411358201934187870982405)
              ·
                refine ⟨77129662862660225809201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 411358201934187870982405 77129662862660225809201)
                ·
                  rfl

theorem cell20_506957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 4].length) (baseStart_506957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506957 prefixEnd_506957 := by exact prefixLift 506957
  have htrace : WordTrace (prefixWord ++ tailWord_506957) baseStart_506957 baseEnd_506957 := by
    simpa [prefixWord, tailWord_506957, baseEnd_506957] using wordTrace_append hprefix tailTrace_506957
  have hstable : (prefixWord ++ tailWord_506957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506957).length < 2 ^ (prefixWord ++ tailWord_506957).sum := by decide
  have hdescent : baseEnd_506957 < baseStart_506957 := by decide
  rcases family_descends (prefixWord ++ tailWord_506957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506961 : List Nat := [1, 2, 2, 1, 3, 1, 6, 4]
def baseStart_506961 : Nat := 118140960795 + 506961 * 2 ^ 59
def prefixEnd_506961 : Nat := 4983230072969 + 3 ^ 40 * 506961 * 2
def baseEnd_506961 : Nat := 77130271432324813764751

theorem tailTrace_506961 : CollatzResearch.WordTrace tailWord_506961 prefixEnd_506961 77130271432324813764751 := by
  unfold tailWord_506961
  simp only [CollatzResearch.WordTrace]
  refine ⟨18490386716374353890760737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12326924477582902593840491 18490386716374353890760737)
  ·
    refine ⟨13867790037280765418070553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18490386716374353890760737 13867790037280765418070553)
    ·
      refine ⟨10400842527960574063552915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13867790037280765418070553 10400842527960574063552915)
      ·
        refine ⟨15601263791940861095329373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10400842527960574063552915 15601263791940861095329373)
        ·
          refine ⟨5850473921977822910748515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15601263791940861095329373 5850473921977822910748515)
          ·
            refine ⟨8775710882966734366122773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5850473921977822910748515 8775710882966734366122773)
            ·
              refine ⟨411361447639065673412005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8775710882966734366122773 411361447639065673412005)
              ·
                refine ⟨77130271432324813764751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 411361447639065673412005 77130271432324813764751)
                ·
                  rfl

theorem cell20_506961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 6, 4].length) (baseStart_506961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506961 prefixEnd_506961 := by exact prefixLift 506961
  have htrace : WordTrace (prefixWord ++ tailWord_506961) baseStart_506961 baseEnd_506961 := by
    simpa [prefixWord, tailWord_506961, baseEnd_506961] using wordTrace_append hprefix tailTrace_506961
  have hstable : (prefixWord ++ tailWord_506961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506961).length < 2 ^ (prefixWord ++ tailWord_506961).sum := by decide
  have hdescent : baseEnd_506961 < baseStart_506961 := by decide
  rcases family_descends (prefixWord ++ tailWord_506961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_506978 : List Nat := [3, 3, 2, 2, 1, 3, 6]
def baseStart_506978 : Nat := 118140960795 + 506978 * 2 ^ 59
def prefixEnd_506978 : Nat := 4983230072969 + 3 ^ 40 * 506978 * 2
def baseEnd_506978 : Nat := 25710952617799770858613

theorem tailTrace_506978 : CollatzResearch.WordTrace tailWord_506978 prefixEnd_506978 25710952617799770858613 := by
  unfold tailWord_506978
  simp only [CollatzResearch.WordTrace]
  refine ⟨4622751689328191448532397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12327337838208510529419725 4622751689328191448532397)
  ·
    refine ⟨1733531883498071793199649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4622751689328191448532397 1733531883498071793199649)
    ·
      refine ⟨1300148912623553844899737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1733531883498071793199649 1300148912623553844899737)
      ·
        refine ⟨975111684467665383674803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1300148912623553844899737 975111684467665383674803)
        ·
          refine ⟨1462667526701498075512205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975111684467665383674803 1462667526701498075512205)
          ·
            refine ⟨548500322513061778317077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1462667526701498075512205 548500322513061778317077)
            ·
              refine ⟨25710952617799770858613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 548500322513061778317077 25710952617799770858613)
              ·
                rfl

theorem cell20_506978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 6].length) (baseStart_506978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_506978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_506978 prefixEnd_506978 := by exact prefixLift 506978
  have htrace : WordTrace (prefixWord ++ tailWord_506978) baseStart_506978 baseEnd_506978 := by
    simpa [prefixWord, tailWord_506978, baseEnd_506978] using wordTrace_append hprefix tailTrace_506978
  have hstable : (prefixWord ++ tailWord_506978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_506978).length < 2 ^ (prefixWord ++ tailWord_506978).sum := by decide
  have hdescent : baseEnd_506978 < baseStart_506978 := by decide
  rcases family_descends (prefixWord ++ tailWord_506978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507027 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 7]
def baseStart_507027 : Nat := 118140960795 + 507027 * 2 ^ 59
def prefixEnd_507027 : Nat := 4983230072969 + 3 ^ 40 * 507027 * 2
def baseEnd_507027 : Nat := 231420938495371545093983

theorem tailTrace_507027 : CollatzResearch.WordTrace tailWord_507027 prefixEnd_507027 231420938495371545093983 := by
  unfold tailWord_507027
  simp only [CollatzResearch.WordTrace]
  refine ⟨18492793934135247162663335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12328529289423498108442223 18492793934135247162663335)
  ·
    refine ⟨27739190901202870743995003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18492793934135247162663335 27739190901202870743995003)
    ·
      refine ⟨41608786351804306115992505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27739190901202870743995003 41608786351804306115992505)
      ·
        refine ⟨31206589763853229586994379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41608786351804306115992505 31206589763853229586994379)
        ·
          refine ⟨46809884645779844380491569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31206589763853229586994379 46809884645779844380491569)
          ·
            refine ⟨35107413484334883285368677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46809884645779844380491569 35107413484334883285368677)
            ·
              refine ⟨6582640028312790616006627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35107413484334883285368677 6582640028312790616006627)
              ·
                refine ⟨9873960042469185924009941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6582640028312790616006627 9873960042469185924009941)
                ·
                  refine ⟨231420938495371545093983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9873960042469185924009941 231420938495371545093983)
                  ·
                    rfl

theorem cell20_507027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_507027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507027 prefixEnd_507027 := by exact prefixLift 507027
  have htrace : WordTrace (prefixWord ++ tailWord_507027) baseStart_507027 baseEnd_507027 := by
    simpa [prefixWord, tailWord_507027, baseEnd_507027] using wordTrace_append hprefix tailTrace_507027
  have hstable : (prefixWord ++ tailWord_507027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507027).length < 2 ^ (prefixWord ++ tailWord_507027).sum := by decide
  have hdescent : baseEnd_507027 < baseStart_507027 := by decide
  rcases family_descends (prefixWord ++ tailWord_507027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507068 : List Nat := [2, 2, 2, 3, 2, 2, 1, 2, 4]
def baseStart_507068 : Nat := 118140960795 + 507068 * 2 ^ 59
def prefixEnd_507068 : Nat := 4983230072969 + 3 ^ 40 * 507068 * 2
def baseEnd_507068 : Nat := 231439652012557624727149

theorem tailTrace_507068 : CollatzResearch.WordTrace tailWord_507068 prefixEnd_507068 231439652012557624727149 := by
  unfold tailWord_507068
  simp only [CollatzResearch.WordTrace]
  refine ⟨9247144663493355582452929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12329526217991140776603905 9247144663493355582452929)
  ·
    refine ⟨6935358497620016686839697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9247144663493355582452929 6935358497620016686839697)
    ·
      refine ⟨5201518873215012515129773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6935358497620016686839697 5201518873215012515129773)
      ·
        refine ⟨1950569577455629693173665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5201518873215012515129773 1950569577455629693173665)
        ·
          refine ⟨1462927183091722269880249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1950569577455629693173665 1462927183091722269880249)
          ·
            refine ⟨1097195387318791702410187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1462927183091722269880249 1097195387318791702410187)
            ·
              refine ⟨1645793080978187553615281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097195387318791702410187 1645793080978187553615281)
              ·
                refine ⟨1234344810733640665211461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1645793080978187553615281 1234344810733640665211461)
                ·
                  refine ⟨231439652012557624727149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1234344810733640665211461 231439652012557624727149)
                  ·
                    rfl

theorem cell20_507068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_507068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507068 prefixEnd_507068 := by exact prefixLift 507068
  have htrace : WordTrace (prefixWord ++ tailWord_507068) baseStart_507068 baseEnd_507068 := by
    simpa [prefixWord, tailWord_507068, baseEnd_507068] using wordTrace_append hprefix tailTrace_507068
  have hstable : (prefixWord ++ tailWord_507068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507068).length < 2 ^ (prefixWord ++ tailWord_507068).sum := by decide
  have hdescent : baseEnd_507068 < baseStart_507068 := by decide
  rcases family_descends (prefixWord ++ tailWord_507068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507092 : List Nat := [2, 4, 1, 4, 1, 1, 7]
def baseStart_507092 : Nat := 118140960795 + 507092 * 2 ^ 59
def prefixEnd_507092 : Nat := 4983230072969 + 3 ^ 40 * 507092 * 2
def baseEnd_507092 : Nat := 25716734029613356436339

theorem tailTrace_507092 : CollatzResearch.WordTrace tailWord_507092 prefixEnd_507092 25716734029613356436339 := by
  unfold tailWord_507092
  simp only [CollatzResearch.WordTrace]
  refine ⟨9247582339449881631889765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12330109785933175509186353 9247582339449881631889765)
  ·
    refine ⟨1733921688646852805979331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9247582339449881631889765 1733921688646852805979331)
    ·
      refine ⟨2600882532970279208968997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1733921688646852805979331 2600882532970279208968997)
      ·
        refine ⟨487665474931927351681687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2600882532970279208968997 487665474931927351681687)
        ·
          refine ⟨731498212397891027522531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487665474931927351681687 731498212397891027522531)
          ·
            refine ⟨1097247318596836541283797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731498212397891027522531 1097247318596836541283797)
            ·
              refine ⟨25716734029613356436339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1097247318596836541283797 25716734029613356436339)
              ·
                rfl

theorem cell20_507092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 7].length) (baseStart_507092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507092 prefixEnd_507092 := by exact prefixLift 507092
  have htrace : WordTrace (prefixWord ++ tailWord_507092) baseStart_507092 baseEnd_507092 := by
    simpa [prefixWord, tailWord_507092, baseEnd_507092] using wordTrace_append hprefix tailTrace_507092
  have hstable : (prefixWord ++ tailWord_507092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507092).length < 2 ^ (prefixWord ++ tailWord_507092).sum := by decide
  have hdescent : baseEnd_507092 < baseStart_507092 := by decide
  rcases family_descends (prefixWord ++ tailWord_507092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507140 : List Nat := [2, 3, 2, 2, 2, 3, 1, 3, 2]
def baseStart_507140 : Nat := 118140960795 + 507140 * 2 ^ 59
def prefixEnd_507140 : Nat := 4983230072969 + 3 ^ 40 * 507140 * 2
def baseEnd_507140 : Nat := 231472514774445374326855

theorem tailTrace_507140 : CollatzResearch.WordTrace tailWord_507140 prefixEnd_507140 231472514774445374326855 := by
  unfold tailWord_507140
  simp only [CollatzResearch.WordTrace]
  refine ⟨9248457691362933730763437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12331276921817244974351249 9248457691362933730763437)
  ·
    refine ⟨3468171634261100149036289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9248457691362933730763437 3468171634261100149036289)
    ·
      refine ⟨2601128725695825111777217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3468171634261100149036289 2601128725695825111777217)
      ·
        refine ⟨1950846544271868833832913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2601128725695825111777217 1950846544271868833832913)
        ·
          refine ⟨1463134908203901625374685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1950846544271868833832913 1463134908203901625374685)
          ·
            refine ⟨548675590576463109515507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1463134908203901625374685 548675590576463109515507)
            ·
              refine ⟨823013385864694664273261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548675590576463109515507 823013385864694664273261)
              ·
                refine ⟨308630019699260499102473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 823013385864694664273261 308630019699260499102473)
                ·
                  refine ⟨231472514774445374326855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308630019699260499102473 231472514774445374326855)
                  ·
                    rfl

theorem cell20_507140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_507140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507140 prefixEnd_507140 := by exact prefixLift 507140
  have htrace : WordTrace (prefixWord ++ tailWord_507140) baseStart_507140 baseEnd_507140 := by
    simpa [prefixWord, tailWord_507140, baseEnd_507140] using wordTrace_append hprefix tailTrace_507140
  have hstable : (prefixWord ++ tailWord_507140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507140).length < 2 ^ (prefixWord ++ tailWord_507140).sum := by decide
  have hdescent : baseEnd_507140 < baseStart_507140 := by decide
  rcases family_descends (prefixWord ++ tailWord_507140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507141 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 7]
def baseStart_507141 : Nat := 118140960795 + 507141 * 2 ^ 59
def prefixEnd_507141 : Nat := 4983230072969 + 3 ^ 40 * 507141 * 2
def baseEnd_507141 : Nat := 231472971201693815293517

theorem tailTrace_507141 : CollatzResearch.WordTrace tailWord_507141 prefixEnd_507141 231472971201693815293517 := by
  unfold tailWord_507141
  simp only [CollatzResearch.WordTrace]
  refine ⟨18496951855722244632313277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12331301237148163088208851 18496951855722244632313277)
  ·
    refine ⟨6936356945895841737117479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18496951855722244632313277 6936356945895841737117479)
    ·
      refine ⟨10404535418843762605676219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6936356945895841737117479 10404535418843762605676219)
      ·
        refine ⟨15606803128265643908514329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10404535418843762605676219 15606803128265643908514329)
        ·
          refine ⟨11705102346199232931385747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15606803128265643908514329 11705102346199232931385747)
          ·
            refine ⟨17557653519298849397078621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11705102346199232931385747 17557653519298849397078621)
            ·
              refine ⟨6584120069737068523904483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17557653519298849397078621 6584120069737068523904483)
              ·
                refine ⟨9876180104605602785856725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6584120069737068523904483 9876180104605602785856725)
                ·
                  refine ⟨231472971201693815293517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9876180104605602785856725 231472971201693815293517)
                  ·
                    rfl

theorem cell20_507141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_507141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507141 prefixEnd_507141 := by exact prefixLift 507141
  have htrace : WordTrace (prefixWord ++ tailWord_507141) baseStart_507141 baseEnd_507141 := by
    simpa [prefixWord, tailWord_507141, baseEnd_507141] using wordTrace_append hprefix tailTrace_507141
  have hstable : (prefixWord ++ tailWord_507141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507141).length < 2 ^ (prefixWord ++ tailWord_507141).sum := by decide
  have hdescent : baseEnd_507141 < baseStart_507141 := by decide
  rcases family_descends (prefixWord ++ tailWord_507141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507206 : List Nat := [6, 1, 1, 3, 9]
def baseStart_507206 : Nat := 118140960795 + 507206 * 2 ^ 59
def prefixEnd_507206 : Nat := 4983230072969 + 3 ^ 40 * 507206 * 2
def baseEnd_507206 : Nat := 2858057271269660223785

theorem tailTrace_507206 : CollatzResearch.WordTrace tailWord_507206 prefixEnd_507206 2858057271269660223785 := by
  unfold tailWord_507206
  simp only [CollatzResearch.WordTrace]
  refine ⟨578103831265211272919671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12332881733657840488952981 578103831265211272919671)
  ·
    refine ⟨867155746897816909379507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 578103831265211272919671 867155746897816909379507)
    ·
      refine ⟨1300733620346725364069261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 867155746897816909379507 1300733620346725364069261)
      ·
        refine ⟨487775107630022011525973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1300733620346725364069261 487775107630022011525973)
        ·
          refine ⟨2858057271269660223785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 487775107630022011525973 2858057271269660223785)
          ·
            rfl

theorem cell20_507206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 9].length) (baseStart_507206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507206 prefixEnd_507206 := by exact prefixLift 507206
  have htrace : WordTrace (prefixWord ++ tailWord_507206) baseStart_507206 baseEnd_507206 := by
    simpa [prefixWord, tailWord_507206, baseEnd_507206] using wordTrace_append hprefix tailTrace_507206
  have hstable : (prefixWord ++ tailWord_507206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507206).length < 2 ^ (prefixWord ++ tailWord_507206).sum := by decide
  have hdescent : baseEnd_507206 < baseStart_507206 := by decide
  rcases family_descends (prefixWord ++ tailWord_507206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507255 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 5]
def baseStart_507255 : Nat := 118140960795 + 507255 * 2 ^ 59
def prefixEnd_507255 : Nat := 4983230072969 + 3 ^ 40 * 507255 * 2
def baseEnd_507255 : Nat := 231525003908016085493051

theorem tailTrace_507255 : CollatzResearch.WordTrace tailWord_507255 prefixEnd_507255 231525003908016085493051 := by
  unfold tailWord_507255
  simp only [CollatzResearch.WordTrace]
  refine ⟨18501109777309242101963219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12334073184872828067975479 18501109777309242101963219)
  ·
    refine ⟨27751664665963863152944829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18501109777309242101963219 27751664665963863152944829)
    ·
      refine ⟨10406874249736448682354311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27751664665963863152944829 10406874249736448682354311)
      ·
        refine ⟨15610311374604673023531467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10406874249736448682354311 15610311374604673023531467)
        ·
          refine ⟨23415467061907009535297201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15610311374604673023531467 23415467061907009535297201)
          ·
            refine ⟨17561600296430257151472901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23415467061907009535297201 17561600296430257151472901)
            ·
              refine ⟨3292800055580673215901169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17561600296430257151472901 3292800055580673215901169)
              ·
                refine ⟨2469600041685504911925877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3292800055580673215901169 2469600041685504911925877)
                ·
                  refine ⟨231525003908016085493051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2469600041685504911925877 231525003908016085493051)
                  ·
                    rfl

theorem cell20_507255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_507255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507255 prefixEnd_507255 := by exact prefixLift 507255
  have htrace : WordTrace (prefixWord ++ tailWord_507255) baseStart_507255 baseEnd_507255 := by
    simpa [prefixWord, tailWord_507255, baseEnd_507255] using wordTrace_append hprefix tailTrace_507255
  have hstable : (prefixWord ++ tailWord_507255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507255).length < 2 ^ (prefixWord ++ tailWord_507255).sum := by decide
  have hdescent : baseEnd_507255 < baseStart_507255 := by decide
  rcases family_descends (prefixWord ++ tailWord_507255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507265 : List Nat := [1, 2, 4, 3, 2, 1, 7]
def baseStart_507265 : Nat := 118140960795 + 507265 * 2 ^ 59
def prefixEnd_507265 : Nat := 4983230072969 + 3 ^ 40 * 507265 * 2
def baseEnd_507265 : Nat := 25725507575611166128853

theorem tailTrace_507265 : CollatzResearch.WordTrace tailWord_507265 prefixEnd_507265 25725507575611166128853 := by
  unfold tailWord_507265
  simp only [CollatzResearch.WordTrace]
  refine ⟨18501474507273013809827249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12334316338182009206551499 18501474507273013809827249)
  ·
    refine ⟨13876105880454760357370437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18501474507273013809827249 13876105880454760357370437)
    ·
      refine ⟨2601769852585267567006957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13876105880454760357370437 2601769852585267567006957)
      ·
        refine ⟨975663694719475337627609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2601769852585267567006957 975663694719475337627609)
        ·
          refine ⟨731747771039606503220707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 975663694719475337627609 731747771039606503220707)
          ·
            refine ⟨1097621656559409754831061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731747771039606503220707 1097621656559409754831061)
            ·
              refine ⟨25725507575611166128853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1097621656559409754831061 25725507575611166128853)
              ·
                rfl

theorem cell20_507265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 7].length) (baseStart_507265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507265 prefixEnd_507265 := by exact prefixLift 507265
  have htrace : WordTrace (prefixWord ++ tailWord_507265) baseStart_507265 baseEnd_507265 := by
    simpa [prefixWord, tailWord_507265, baseEnd_507265] using wordTrace_append hprefix tailTrace_507265
  have hstable : (prefixWord ++ tailWord_507265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507265).length < 2 ^ (prefixWord ++ tailWord_507265).sum := by decide
  have hdescent : baseEnd_507265 < baseStart_507265 := by decide
  rcases family_descends (prefixWord ++ tailWord_507265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507272 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 5]
def baseStart_507272 : Nat := 118140960795 + 507272 * 2 ^ 59
def prefixEnd_507272 : Nat := 4983230072969 + 3 ^ 40 * 507272 * 2
def baseEnd_507272 : Nat := 231532763171239581926315

theorem tailTrace_507272 : CollatzResearch.WordTrace tailWord_507272 prefixEnd_507272 231532763171239581926315 := by
  unfold tailWord_507272
  simp only [CollatzResearch.WordTrace]
  refine ⟨9250864909123827002666035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12334486545498436003554713 9250864909123827002666035)
  ·
    refine ⟨13876297363685740503999053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9250864909123827002666035 13876297363685740503999053)
    ·
      refine ⟨5203611511382152688999645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13876297363685740503999053 5203611511382152688999645)
      ·
        refine ⟨1951354316768307258374867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5203611511382152688999645 1951354316768307258374867)
        ·
          refine ⟨2927031475152460887562301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1951354316768307258374867 2927031475152460887562301)
          ·
            refine ⟨1097636803182172832835863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2927031475152460887562301 1097636803182172832835863)
            ·
              refine ⟨1646455204773259249253795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1097636803182172832835863 1646455204773259249253795)
              ·
                refine ⟨2469682807159888873880693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1646455204773259249253795 2469682807159888873880693)
                ·
                  refine ⟨231532763171239581926315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2469682807159888873880693 231532763171239581926315)
                  ·
                    rfl

theorem cell20_507272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_507272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507272 prefixEnd_507272 := by exact prefixLift 507272
  have htrace : WordTrace (prefixWord ++ tailWord_507272) baseStart_507272 baseEnd_507272 := by
    simpa [prefixWord, tailWord_507272, baseEnd_507272] using wordTrace_append hprefix tailTrace_507272
  have hstable : (prefixWord ++ tailWord_507272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507272).length < 2 ^ (prefixWord ++ tailWord_507272).sum := by decide
  have hdescent : baseEnd_507272 < baseStart_507272 := by decide
  rcases family_descends (prefixWord ++ tailWord_507272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507289 : List Nat := [1, 2, 1, 2, 1, 6, 3, 1, 3]
def baseStart_507289 : Nat := 118140960795 + 507289 * 2 ^ 59
def prefixEnd_507289 : Nat := 4983230072969 + 3 ^ 40 * 507289 * 2
def baseEnd_507289 : Nat := 231540522434463078359579

theorem tailTrace_507289 : CollatzResearch.WordTrace tailWord_507289 prefixEnd_507289 231540522434463078359579 := by
  unfold tailWord_507289
  simp only [CollatzResearch.WordTrace]
  refine ⟨18502349859186065908700921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12334899906124043939133947 18502349859186065908700921)
  ·
    refine ⟨13876762394389549431525691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18502349859186065908700921 13876762394389549431525691)
    ·
      refine ⟨20815143591584324147288537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13876762394389549431525691 20815143591584324147288537)
      ·
        refine ⟨15611357693688243110466403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20815143591584324147288537 15611357693688243110466403)
        ·
          refine ⟨23417036540532364665699605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15611357693688243110466403 23417036540532364665699605)
          ·
            refine ⟨1097673587837454593704669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23417036540532364665699605 1097673587837454593704669)
            ·
              refine ⟨411627595439045472639251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1097673587837454593704669 411627595439045472639251)
              ·
                refine ⟨617441393158568208958877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411627595439045472639251 617441393158568208958877)
                ·
                  refine ⟨231540522434463078359579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 617441393158568208958877 231540522434463078359579)
                  ·
                    rfl

theorem cell20_507289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 3].length) (baseStart_507289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507289 prefixEnd_507289 := by exact prefixLift 507289
  have htrace : WordTrace (prefixWord ++ tailWord_507289) baseStart_507289 baseEnd_507289 := by
    simpa [prefixWord, tailWord_507289, baseEnd_507289] using wordTrace_append hprefix tailTrace_507289
  have hstable : (prefixWord ++ tailWord_507289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507289).length < 2 ^ (prefixWord ++ tailWord_507289).sum := by decide
  have hdescent : baseEnd_507289 < baseStart_507289 := by decide
  rcases family_descends (prefixWord ++ tailWord_507289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507331 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 5]
def baseStart_507331 : Nat := 118140960795 + 507331 * 2 ^ 59
def prefixEnd_507331 : Nat := 4983230072969 + 3 ^ 40 * 507331 * 2
def baseEnd_507331 : Nat := 231559692378897598959407

theorem tailTrace_507331 : CollatzResearch.WordTrace tailWord_507331 prefixEnd_507331 231559692378897598959407 := by
  unfold tailWord_507331
  simp only [CollatzResearch.WordTrace]
  refine ⟨18503881725033907081729847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12335921150022604721153231 18503881725033907081729847)
  ·
    refine ⟨27755822587550860622594771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18503881725033907081729847 27755822587550860622594771)
    ·
      refine ⟨41633733881326290933892157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27755822587550860622594771 41633733881326290933892157)
      ·
        refine ⟨15612650205497359100209559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41633733881326290933892157 15612650205497359100209559)
        ·
          refine ⟨23418975308246038650314339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15612650205497359100209559 23418975308246038650314339)
          ·
            refine ⟨35128462962369057975471509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23418975308246038650314339 35128462962369057975471509)
            ·
              refine ⟨1646646701361049592600227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35128462962369057975471509 1646646701361049592600227)
              ·
                refine ⟨2469970052041574388900341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1646646701361049592600227 2469970052041574388900341)
                ·
                  refine ⟨231559692378897598959407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2469970052041574388900341 231559692378897598959407)
                  ·
                    rfl

theorem cell20_507331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 5].length) (baseStart_507331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507331 prefixEnd_507331 := by exact prefixLift 507331
  have htrace : WordTrace (prefixWord ++ tailWord_507331) baseStart_507331 baseEnd_507331 := by
    simpa [prefixWord, tailWord_507331, baseEnd_507331] using wordTrace_append hprefix tailTrace_507331
  have hstable : (prefixWord ++ tailWord_507331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507331).length < 2 ^ (prefixWord ++ tailWord_507331).sum := by decide
  have hdescent : baseEnd_507331 < baseStart_507331 := by decide
  rcases family_descends (prefixWord ++ tailWord_507331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507386 : List Nat := [3, 1, 1, 1, 1, 2, 6, 2, 3]
def baseStart_507386 : Nat := 118140960795 + 507386 * 2 ^ 59
def prefixEnd_507386 : Nat := 4983230072969 + 3 ^ 40 * 507386 * 2
def baseEnd_507386 : Nat := 231584795877561852125849

theorem tailTrace_507386 : CollatzResearch.WordTrace tailWord_507386 prefixEnd_507386 231584795877561852125849 := by
  unfold tailWord_507386
  simp only [CollatzResearch.WordTrace]
  refine ⟨4626471934958662868745503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12337258493223100983321341 4626471934958662868745503)
  ·
    refine ⟨6939707902437994303118255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4626471934958662868745503 6939707902437994303118255)
    ·
      refine ⟨10409561853656991454677383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6939707902437994303118255 10409561853656991454677383)
      ·
        refine ⟨15614342780485487182016075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10409561853656991454677383 15614342780485487182016075)
        ·
          refine ⟨23421514170728230773024113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15614342780485487182016075 23421514170728230773024113)
          ·
            refine ⟨17566135628046173079768085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23421514170728230773024113 17566135628046173079768085)
            ·
              refine ⟨823412607564664363114129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17566135628046173079768085 823412607564664363114129)
              ·
                refine ⟨617559455673498272335597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 823412607564664363114129 617559455673498272335597)
                ·
                  refine ⟨231584795877561852125849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 617559455673498272335597 231584795877561852125849)
                  ·
                    rfl

theorem cell20_507386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_507386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507386 prefixEnd_507386 := by exact prefixLift 507386
  have htrace : WordTrace (prefixWord ++ tailWord_507386) baseStart_507386 baseEnd_507386 := by
    simpa [prefixWord, tailWord_507386, baseEnd_507386] using wordTrace_append hprefix tailTrace_507386
  have hstable : (prefixWord ++ tailWord_507386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507386).length < 2 ^ (prefixWord ++ tailWord_507386).sum := by decide
  have hdescent : baseEnd_507386 < baseStart_507386 := by decide
  rcases family_descends (prefixWord ++ tailWord_507386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507389 : List Nat := [1, 4, 1, 1, 1, 4, 4, 2, 2]
def baseStart_507389 : Nat := 118140960795 + 507389 * 2 ^ 59
def prefixEnd_507389 : Nat := 4983230072969 + 3 ^ 40 * 507389 * 2
def baseEnd_507389 : Nat := 231586165159307175025837

theorem tailTrace_507389 : CollatzResearch.WordTrace tailWord_507389 prefixEnd_507389 231586165159307175025837 := by
  unfold tailWord_507389
  simp only [CollatzResearch.WordTrace]
  refine ⟨18505997158823782987341221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12337331439215855324894147 18505997158823782987341221)
  ·
    refine ⟨3469874467279459310126479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18505997158823782987341221 3469874467279459310126479)
    ·
      refine ⟨5204811700919188965189719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3469874467279459310126479 5204811700919188965189719)
      ·
        refine ⟨7807217551378783447784579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5204811700919188965189719 7807217551378783447784579)
        ·
          refine ⟨11710826327068175171676869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7807217551378783447784579 11710826327068175171676869)
          ·
            refine ⟨2195779936325282844689413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11710826327068175171676869 2195779936325282844689413)
            ·
              refine ⟨411708738060990533379265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2195779936325282844689413 411708738060990533379265)
              ·
                refine ⟨308781553545742900034449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411708738060990533379265 308781553545742900034449)
                ·
                  refine ⟨231586165159307175025837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308781553545742900034449 231586165159307175025837)
                  ·
                    rfl

theorem cell20_507389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_507389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507389 prefixEnd_507389 := by exact prefixLift 507389
  have htrace : WordTrace (prefixWord ++ tailWord_507389) baseStart_507389 baseEnd_507389 := by
    simpa [prefixWord, tailWord_507389, baseEnd_507389] using wordTrace_append hprefix tailTrace_507389
  have hstable : (prefixWord ++ tailWord_507389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507389).length < 2 ^ (prefixWord ++ tailWord_507389).sum := by decide
  have hdescent : baseEnd_507389 < baseStart_507389 := by decide
  rcases family_descends (prefixWord ++ tailWord_507389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507396 : List Nat := [2, 3, 2, 3, 2, 2, 1, 5]
def baseStart_507396 : Nat := 118140960795 + 507396 * 2 ^ 59
def prefixEnd_507396 : Nat := 4983230072969 + 3 ^ 40 * 507396 * 2
def baseEnd_507396 : Nat := 77196453383348753930825

theorem tailTrace_507396 : CollatzResearch.WordTrace tailWord_507396 prefixEnd_507396 77196453383348753930825 := by
  unfold tailWord_507396
  simp only [CollatzResearch.WordTrace]
  refine ⟨9253126234899211591423021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12337501646532282121897361 9253126234899211591423021)
  ·
    refine ⟨3469922338087204346783633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9253126234899211591423021 3469922338087204346783633)
    ·
      refine ⟨2602441753565403260087725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3469922338087204346783633 2602441753565403260087725)
      ·
        refine ⟨975915657587026222532897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2602441753565403260087725 975915657587026222532897)
        ·
          refine ⟨731936743190269666899673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 975915657587026222532897 731936743190269666899673)
          ·
            refine ⟨548952557392702250174755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 731936743190269666899673 548952557392702250174755)
            ·
              refine ⟨823428836089053375262133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 548952557392702250174755 823428836089053375262133)
              ·
                refine ⟨77196453383348753930825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 823428836089053375262133 77196453383348753930825)
                ·
                  rfl

theorem cell20_507396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 5].length) (baseStart_507396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507396 prefixEnd_507396 := by exact prefixLift 507396
  have htrace : WordTrace (prefixWord ++ tailWord_507396) baseStart_507396 baseEnd_507396 := by
    simpa [prefixWord, tailWord_507396, baseEnd_507396] using wordTrace_append hprefix tailTrace_507396
  have hstable : (prefixWord ++ tailWord_507396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507396).length < 2 ^ (prefixWord ++ tailWord_507396).sum := by decide
  have hdescent : baseEnd_507396 < baseStart_507396 := by decide
  rcases family_descends (prefixWord ++ tailWord_507396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507400 : List Nat := [2, 1, 3, 2, 1, 1, 5, 5]
def baseStart_507400 : Nat := 118140960795 + 507400 * 2 ^ 59
def prefixEnd_507400 : Nat := 4983230072969 + 3 ^ 40 * 507400 * 2
def baseEnd_507400 : Nat := 77197061953013341886375

theorem tailTrace_507400 : CollatzResearch.WordTrace tailWord_507400 prefixEnd_507400 77197061953013341886375 := by
  unfold tailWord_507400
  simp only [CollatzResearch.WordTrace]
  refine ⟨9253199180891965932995827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12337598907855954577327769 9253199180891965932995827)
  ·
    refine ⟨13879798771337948899493741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9253199180891965932995827 13879798771337948899493741)
    ·
      refine ⟨5204924539251730837310153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13879798771337948899493741 5204924539251730837310153)
      ·
        refine ⟨3903693404438798127982615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5204924539251730837310153 3903693404438798127982615)
        ·
          refine ⟨5855540106658197191973923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3903693404438798127982615 5855540106658197191973923)
          ·
            refine ⟨8783310159987295787960885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5855540106658197191973923 8783310159987295787960885)
            ·
              refine ⟨823435327498808980121333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8783310159987295787960885 823435327498808980121333)
              ·
                refine ⟨77197061953013341886375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 823435327498808980121333 77197061953013341886375)
                ·
                  rfl

theorem cell20_507400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 5].length) (baseStart_507400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507400 prefixEnd_507400 := by exact prefixLift 507400
  have htrace : WordTrace (prefixWord ++ tailWord_507400) baseStart_507400 baseEnd_507400 := by
    simpa [prefixWord, tailWord_507400, baseEnd_507400] using wordTrace_append hprefix tailTrace_507400
  have hstable : (prefixWord ++ tailWord_507400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507400).length < 2 ^ (prefixWord ++ tailWord_507400).sum := by decide
  have hdescent : baseEnd_507400 < baseStart_507400 := by decide
  rcases family_descends (prefixWord ++ tailWord_507400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507427 : List Nat := [1, 1, 1, 4, 5, 1, 2, 3, 2]
def baseStart_507427 : Nat := 118140960795 + 507427 * 2 ^ 59
def prefixEnd_507427 : Nat := 4983230072969 + 3 ^ 40 * 507427 * 2
def baseEnd_507427 : Nat := 231603509394747931759015

theorem tailTrace_507427 : CollatzResearch.WordTrace tailWord_507427 prefixEnd_507427 231603509394747931759015 := by
  unfold tailWord_507427
  simp only [CollatzResearch.WordTrace]
  refine ⟨18507383132686115477224535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12338255421790743651483023 18507383132686115477224535)
  ·
    refine ⟨27761074699029173215836803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18507383132686115477224535 27761074699029173215836803)
    ·
      refine ⟨41641612048543759823755205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27761074699029173215836803 41641612048543759823755205)
      ·
        refine ⟨7807802259101954966954101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41641612048543759823755205 7807802259101954966954101)
        ·
          refine ⟨731981461790808278151947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7807802259101954966954101 731981461790808278151947)
          ·
            refine ⟨1097972192686212417227921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731981461790808278151947 1097972192686212417227921)
            ·
              refine ⟨823479144514659312920941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1097972192686212417227921 823479144514659312920941)
              ·
                refine ⟨308804679192997242345353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 823479144514659312920941 308804679192997242345353)
                ·
                  refine ⟨231603509394747931759015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308804679192997242345353 231603509394747931759015)
                  ·
                    rfl

theorem cell20_507427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 2].length) (baseStart_507427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507427 prefixEnd_507427 := by exact prefixLift 507427
  have htrace : WordTrace (prefixWord ++ tailWord_507427) baseStart_507427 baseEnd_507427 := by
    simpa [prefixWord, tailWord_507427, baseEnd_507427] using wordTrace_append hprefix tailTrace_507427
  have hstable : (prefixWord ++ tailWord_507427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507427).length < 2 ^ (prefixWord ++ tailWord_507427).sum := by decide
  have hdescent : baseEnd_507427 < baseStart_507427 := by decide
  rcases family_descends (prefixWord ++ tailWord_507427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507448 : List Nat := [2, 1, 2, 1, 4, 2, 2, 4, 2]
def baseStart_507448 : Nat := 118140960795 + 507448 * 2 ^ 59
def prefixEnd_507448 : Nat := 4983230072969 + 3 ^ 40 * 507448 * 2
def baseEnd_507448 : Nat := 231613094366965192058929

theorem tailTrace_507448 : CollatzResearch.WordTrace tailWord_507448 prefixEnd_507448 231613094366965192058929 := by
  unfold tailWord_507448
  simp only [CollatzResearch.WordTrace]
  refine ⟨9254074532805018031869499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12338766043740024042492665 9254074532805018031869499)
  ·
    refine ⟨13881111799207527047804249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9254074532805018031869499 13881111799207527047804249)
    ·
      refine ⟨10410833849405645285853187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13881111799207527047804249 10410833849405645285853187)
      ·
        refine ⟨15616250774108467928779781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10410833849405645285853187 15616250774108467928779781)
        ·
          refine ⟨2928047020145337736646209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15616250774108467928779781 2928047020145337736646209)
          ·
            refine ⟨2196035265109003302484657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2928047020145337736646209 2196035265109003302484657)
            ·
              refine ⟨1647026448831752476863493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2196035265109003302484657 1647026448831752476863493)
              ·
                refine ⟨308817459155953589411905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1647026448831752476863493 308817459155953589411905)
                ·
                  refine ⟨231613094366965192058929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308817459155953589411905 231613094366965192058929)
                  ·
                    rfl

theorem cell20_507448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 4, 2].length) (baseStart_507448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507448 prefixEnd_507448 := by exact prefixLift 507448
  have htrace : WordTrace (prefixWord ++ tailWord_507448) baseStart_507448 baseEnd_507448 := by
    simpa [prefixWord, tailWord_507448, baseEnd_507448] using wordTrace_append hprefix tailTrace_507448
  have hstable : (prefixWord ++ tailWord_507448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507448).length < 2 ^ (prefixWord ++ tailWord_507448).sum := by decide
  have hdescent : baseEnd_507448 < baseStart_507448 := by decide
  rcases family_descends (prefixWord ++ tailWord_507448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507476 : List Nat := [2, 4, 1, 1, 1, 2, 3, 6]
def baseStart_507476 : Nat := 118140960795 + 507476 * 2 ^ 59
def prefixEnd_507476 : Nat := 4983230072969 + 3 ^ 40 * 507476 * 2
def baseEnd_507476 : Nat := 77208624776640513041827

theorem tailTrace_507476 : CollatzResearch.WordTrace tailWord_507476 prefixEnd_507476 77208624776640513041827 := by
  unfold tailWord_507476
  simp only [CollatzResearch.WordTrace]
  refine ⟨9254585154754298422879141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12339446873005731230505521 9254585154754298422879141)
  ·
    refine ⟨1735234716516430954289839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9254585154754298422879141 1735234716516430954289839)
    ·
      refine ⟨2602852074774646431434759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1735234716516430954289839 2602852074774646431434759)
      ·
        refine ⟨3904278112161969647152139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2602852074774646431434759 3904278112161969647152139)
        ·
          refine ⟨5856417168242954470728209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3904278112161969647152139 5856417168242954470728209)
          ·
            refine ⟨4392312876182215853046157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5856417168242954470728209 4392312876182215853046157)
            ·
              refine ⟨1647117328568330944892309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4392312876182215853046157 1647117328568330944892309)
              ·
                refine ⟨77208624776640513041827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1647117328568330944892309 77208624776640513041827)
                ·
                  rfl

theorem cell20_507476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_507476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507476 prefixEnd_507476 := by exact prefixLift 507476
  have htrace : WordTrace (prefixWord ++ tailWord_507476) baseStart_507476 baseEnd_507476 := by
    simpa [prefixWord, tailWord_507476, baseEnd_507476] using wordTrace_append hprefix tailTrace_507476
  have hstable : (prefixWord ++ tailWord_507476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507476).length < 2 ^ (prefixWord ++ tailWord_507476).sum := by decide
  have hdescent : baseEnd_507476 < baseStart_507476 := by decide
  rcases family_descends (prefixWord ++ tailWord_507476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507478 : List Nat := [5, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_507478 : Nat := 118140960795 + 507478 * 2 ^ 59
def prefixEnd_507478 : Nat := 4983230072969 + 3 ^ 40 * 507478 * 2
def baseEnd_507478 : Nat := 231626787184418421058807

theorem tailTrace_507478 : CollatzResearch.WordTrace tailWord_507478 prefixEnd_507478 231626787184418421058807 := by
  unfold tailWord_507478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1156827703468834449208193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12339495503667567458220725 1156827703468834449208193)
  ·
    refine ⟨867620777601625836906145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1156827703468834449208193 867620777601625836906145)
    ·
      refine ⟨650715583201219377679609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 867620777601625836906145 650715583201219377679609)
      ·
        refine ⟨488036687400914533259707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 650715583201219377679609 488036687400914533259707)
        ·
          refine ⟨732055031101371799889561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488036687400914533259707 732055031101371799889561)
          ·
            refine ⟨549041273326028849917171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 732055031101371799889561 549041273326028849917171)
            ·
              refine ⟨823561909989043274875757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549041273326028849917171 823561909989043274875757)
              ·
                refine ⟨308835716245891228078409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 823561909989043274875757 308835716245891228078409)
                ·
                  refine ⟨231626787184418421058807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308835716245891228078409 231626787184418421058807)
                  ·
                    rfl

theorem cell20_507478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_507478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507478 prefixEnd_507478 := by exact prefixLift 507478
  have htrace : WordTrace (prefixWord ++ tailWord_507478) baseStart_507478 baseEnd_507478 := by
    simpa [prefixWord, tailWord_507478, baseEnd_507478] using wordTrace_append hprefix tailTrace_507478
  have hstable : (prefixWord ++ tailWord_507478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507478).length < 2 ^ (prefixWord ++ tailWord_507478).sum := by decide
  have hdescent : baseEnd_507478 < baseStart_507478 := by decide
  rcases family_descends (prefixWord ++ tailWord_507478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507497 : List Nat := [1, 2, 1, 1, 1, 4, 10]
def baseStart_507497 : Nat := 118140960795 + 507497 * 2 ^ 59
def prefixEnd_507497 : Nat := 4983230072969 + 3 ^ 40 * 507497 * 2
def baseEnd_507497 : Nat := 25737273255793199936155

theorem tailTrace_507497 : CollatzResearch.WordTrace tailWord_507497 prefixEnd_507497 25737273255793199936155 := by
  unfold tailWord_507497
  simp only [CollatzResearch.WordTrace]
  refine ⟨18509936242432517432272745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12339957494955011621515163 18509936242432517432272745)
  ·
    refine ⟨13882452181824388074204559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18509936242432517432272745 13882452181824388074204559)
    ·
      refine ⟨20823678272736582111306839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13882452181824388074204559 20823678272736582111306839)
      ·
        refine ⟨31235517409104873166960259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20823678272736582111306839 31235517409104873166960259)
        ·
          refine ⟨46853276113657309750440389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31235517409104873166960259 46853276113657309750440389)
          ·
            refine ⟨8784989271310745578207573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46853276113657309750440389 8784989271310745578207573)
            ·
              refine ⟨25737273255793199936155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8784989271310745578207573 25737273255793199936155)
              ·
                rfl

theorem cell20_507497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 10].length) (baseStart_507497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507497 prefixEnd_507497 := by exact prefixLift 507497
  have htrace : WordTrace (prefixWord ++ tailWord_507497) baseStart_507497 baseEnd_507497 := by
    simpa [prefixWord, tailWord_507497, baseEnd_507497] using wordTrace_append hprefix tailTrace_507497
  have hstable : (prefixWord ++ tailWord_507497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507497).length < 2 ^ (prefixWord ++ tailWord_507497).sum := by decide
  have hdescent : baseEnd_507497 < baseStart_507497 := by decide
  rcases family_descends (prefixWord ++ tailWord_507497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507517 : List Nat := [1, 4, 1, 1, 4, 1, 4, 1, 3]
def baseStart_507517 : Nat := 118140960795 + 507517 * 2 ^ 59
def prefixEnd_507517 : Nat := 4983230072969 + 3 ^ 40 * 507517 * 2
def baseEnd_507517 : Nat := 231644587847107618758647

theorem tailTrace_507517 : CollatzResearch.WordTrace tailWord_507517 prefixEnd_507517 231644587847107618758647 := by
  unfold tailWord_507517
  simp only [CollatzResearch.WordTrace]
  refine ⟨18510665702360060848000805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12340443801573373898667203 18510665702360060848000805)
  ·
    refine ⟨3470749819192511409000151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18510665702360060848000805 3470749819192511409000151)
    ·
      refine ⟨5206124728788767113500227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3470749819192511409000151 5206124728788767113500227)
      ·
        refine ⟨7809187093183150670250341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5206124728788767113500227 7809187093183150670250341)
        ·
          refine ⟨1464222579971840750671939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7809187093183150670250341 1464222579971840750671939)
          ·
            refine ⟨2196333869957761126007909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464222579971840750671939 2196333869957761126007909)
            ·
              refine ⟨411812600617080211126483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2196333869957761126007909 411812600617080211126483)
              ·
                refine ⟨617718900925620316689725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411812600617080211126483 617718900925620316689725)
                ·
                  refine ⟨231644587847107618758647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 617718900925620316689725 231644587847107618758647)
                  ·
                    rfl

theorem cell20_507517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_507517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507517 prefixEnd_507517 := by exact prefixLift 507517
  have htrace : WordTrace (prefixWord ++ tailWord_507517) baseStart_507517 baseEnd_507517 := by
    simpa [prefixWord, tailWord_507517, baseEnd_507517] using wordTrace_append hprefix tailTrace_507517
  have hstable : (prefixWord ++ tailWord_507517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507517).length < 2 ^ (prefixWord ++ tailWord_507517).sum := by decide
  have hdescent : baseEnd_507517 < baseStart_507517 := by decide
  rcases family_descends (prefixWord ++ tailWord_507517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507554 : List Nat := [3, 3, 1, 4, 2, 1, 2, 2, 2]
def baseStart_507554 : Nat := 118140960795 + 507554 * 2 ^ 59
def prefixEnd_507554 : Nat := 4983230072969 + 3 ^ 40 * 507554 * 2
def baseEnd_507554 : Nat := 231661475655299934525163

theorem tailTrace_507554 : CollatzResearch.WordTrace tailWord_507554 prefixEnd_507554 231661475655299934525163 := by
  unfold tailWord_507554
  simp only [CollatzResearch.WordTrace]
  refine ⟨4628003800806504041774429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12341343468817344111398477 4628003800806504041774429)
  ·
    refine ⟨1735501425302439015665411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4628003800806504041774429 1735501425302439015665411)
    ·
      refine ⟨2603252137953658523498117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1735501425302439015665411 2603252137953658523498117)
      ·
        refine ⟨488109775866310973155897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2603252137953658523498117 488109775866310973155897)
        ·
          refine ⟨366082331899733229866923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488109775866310973155897 366082331899733229866923)
          ·
            refine ⟨549123497849599844800385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366082331899733229866923 549123497849599844800385)
            ·
              refine ⟨411842623387199883600289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549123497849599844800385 411842623387199883600289)
              ·
                refine ⟨308881967540399912700217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411842623387199883600289 308881967540399912700217)
                ·
                  refine ⟨231661475655299934525163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308881967540399912700217 231661475655299934525163)
                  ·
                    rfl

theorem cell20_507554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_507554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507554 prefixEnd_507554 := by exact prefixLift 507554
  have htrace : WordTrace (prefixWord ++ tailWord_507554) baseStart_507554 baseEnd_507554 := by
    simpa [prefixWord, tailWord_507554, baseEnd_507554] using wordTrace_append hprefix tailTrace_507554
  have hstable : (prefixWord ++ tailWord_507554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507554).length < 2 ^ (prefixWord ++ tailWord_507554).sum := by decide
  have hdescent : baseEnd_507554 < baseStart_507554 := by decide
  rcases family_descends (prefixWord ++ tailWord_507554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507606 : List Nat := [5, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_507606 : Nat := 118140960795 + 507606 * 2 ^ 59
def prefixEnd_507606 : Nat := 4983230072969 + 3 ^ 40 * 507606 * 2
def baseEnd_507606 : Nat := 231685209872218864791617

theorem tailTrace_507606 : CollatzResearch.WordTrace tailWord_507606 prefixEnd_507606 231685209872218864791617 := by
  unfold tailWord_507606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1157119487439851815499417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12342607866025086031993781 1157119487439851815499417)
  ·
    refine ⟨867839615579888861624563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1157119487439851815499417 867839615579888861624563)
    ·
      refine ⟨1301759423369833292436845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 867839615579888861624563 1301759423369833292436845)
      ·
        refine ⟨488159783763687484663817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1301759423369833292436845 488159783763687484663817)
        ·
          refine ⟨366119837822765613497863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 488159783763687484663817 366119837822765613497863)
          ·
            refine ⟨549179756734148420246795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366119837822765613497863 549179756734148420246795)
            ·
              refine ⟨823769635101222630370193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549179756734148420246795 823769635101222630370193)
              ·
                refine ⟨617827226325916972777645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 823769635101222630370193 617827226325916972777645)
                ·
                  refine ⟨231685209872218864791617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 617827226325916972777645 231685209872218864791617)
                  ·
                    rfl

theorem cell20_507606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_507606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507606 prefixEnd_507606 := by exact prefixLift 507606
  have htrace : WordTrace (prefixWord ++ tailWord_507606) baseStart_507606 baseEnd_507606 := by
    simpa [prefixWord, tailWord_507606, baseEnd_507606] using wordTrace_append hprefix tailTrace_507606
  have hstable : (prefixWord ++ tailWord_507606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507606).length < 2 ^ (prefixWord ++ tailWord_507606).sum := by decide
  have hdescent : baseEnd_507606 < baseStart_507606 := by decide
  rcases family_descends (prefixWord ++ tailWord_507606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507621 : List Nat := [1, 3, 1, 4, 1, 1, 4, 1, 4]
def baseStart_507621 : Nat := 118140960795 + 507621 * 2 ^ 59
def prefixEnd_507621 : Nat := 4983230072969 + 3 ^ 40 * 507621 * 2
def baseEnd_507621 : Nat := 231692056280945479291555

theorem tailTrace_507621 : CollatzResearch.WordTrace tailWord_507621 prefixEnd_507621 231692056280945479291555 := by
  unfold tailWord_507621
  simp only [CollatzResearch.WordTrace]
  refine ⟨18514458893983286609786717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12342972595988857739857811 18514458893983286609786717)
  ·
    refine ⟨6942922085243732478670019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18514458893983286609786717 6942922085243732478670019)
    ·
      refine ⟨10414383127865598718005029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6942922085243732478670019 10414383127865598718005029)
      ·
        refine ⟨1952696836474799759625943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10414383127865598718005029 1952696836474799759625943)
        ·
          refine ⟨2929045254712199639438915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1952696836474799759625943 2929045254712199639438915)
          ·
            refine ⟨4393567882068299459158373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2929045254712199639438915 4393567882068299459158373)
            ·
              refine ⟨823793977887806148592195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4393567882068299459158373 823793977887806148592195)
              ·
                refine ⟨1235690966831709222888293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 823793977887806148592195 1235690966831709222888293)
                ·
                  refine ⟨231692056280945479291555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1235690966831709222888293 231692056280945479291555)
                  ·
                    rfl

theorem cell20_507621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_507621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507621 prefixEnd_507621 := by exact prefixLift 507621
  have htrace : WordTrace (prefixWord ++ tailWord_507621) baseStart_507621 baseEnd_507621 := by
    simpa [prefixWord, tailWord_507621, baseEnd_507621] using wordTrace_append hprefix tailTrace_507621
  have hstable : (prefixWord ++ tailWord_507621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507621).length < 2 ^ (prefixWord ++ tailWord_507621).sum := by decide
  have hdescent : baseEnd_507621 < baseStart_507621 := by decide
  rcases family_descends (prefixWord ++ tailWord_507621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507635 : List Nat := [1, 1, 1, 2, 2, 3, 2, 5, 3]
def baseStart_507635 : Nat := 118140960795 + 507635 * 2 ^ 59
def prefixEnd_507635 : Nat := 4983230072969 + 3 ^ 40 * 507635 * 2
def baseEnd_507635 : Nat := 231698446262423652824831

theorem tailTrace_507635 : CollatzResearch.WordTrace tailWord_507635 prefixEnd_507635 231698446262423652824831 := by
  unfold tailWord_507635
  simp only [CollatzResearch.WordTrace]
  refine ⟨18514969515932567000796359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12343313010621711333864239 18514969515932567000796359)
  ·
    refine ⟨27772454273898850501194539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18514969515932567000796359 27772454273898850501194539)
    ·
      refine ⟨41658681410848275751791809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27772454273898850501194539 41658681410848275751791809)
      ·
        refine ⟨31244011058136206813843857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41658681410848275751791809 31244011058136206813843857)
        ·
          refine ⟨23433008293602155110382893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31244011058136206813843857 23433008293602155110382893)
          ·
            refine ⟨8787378110100808166393585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23433008293602155110382893 8787378110100808166393585)
            ·
              refine ⟨6590533582575606124795189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8787378110100808166393585 6590533582575606124795189)
              ·
                refine ⟨617862523366463074199549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6590533582575606124795189 617862523366463074199549)
                ·
                  refine ⟨231698446262423652824831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 617862523366463074199549 231698446262423652824831)
                  ·
                    rfl

theorem cell20_507635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 3].length) (baseStart_507635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507635 prefixEnd_507635 := by exact prefixLift 507635
  have htrace : WordTrace (prefixWord ++ tailWord_507635) baseStart_507635 baseEnd_507635 := by
    simpa [prefixWord, tailWord_507635, baseEnd_507635] using wordTrace_append hprefix tailTrace_507635
  have hstable : (prefixWord ++ tailWord_507635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507635).length < 2 ^ (prefixWord ++ tailWord_507635).sum := by decide
  have hdescent : baseEnd_507635 < baseStart_507635 := by decide
  rcases family_descends (prefixWord ++ tailWord_507635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507668 : List Nat := [2, 4, 4, 1, 1, 1, 3, 2, 2]
def baseStart_507668 : Nat := 118140960795 + 507668 * 2 ^ 59
def prefixEnd_507668 : Nat := 4983230072969 + 3 ^ 40 * 507668 * 2
def baseEnd_507668 : Nat := 231713508361622204724697

theorem tailTrace_507668 : CollatzResearch.WordTrace tailWord_507668 prefixEnd_507668 231713508361622204724697 := by
  unfold tailWord_507668
  simp only [CollatzResearch.WordTrace]
  refine ⟨9258086562406506818373829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12344115416542009091165105 9258086562406506818373829)
  ·
    refine ⟨1735891230451220028445093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9258086562406506818373829 1735891230451220028445093)
    ·
      refine ⟨325479605709603755333455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1735891230451220028445093 325479605709603755333455)
      ·
        refine ⟨488219408564405633000183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 325479605709603755333455 488219408564405633000183)
        ·
          refine ⟨732329112846608449500275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488219408564405633000183 732329112846608449500275)
          ·
            refine ⟨1098493669269912674250413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732329112846608449500275 1098493669269912674250413)
            ·
              refine ⟨411935125976217252843905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1098493669269912674250413 411935125976217252843905)
              ·
                refine ⟨308951344482162939632929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 411935125976217252843905 308951344482162939632929)
                ·
                  refine ⟨231713508361622204724697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308951344482162939632929 231713508361622204724697)
                  ·
                    rfl

theorem cell20_507668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_507668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507668 prefixEnd_507668 := by exact prefixLift 507668
  have htrace : WordTrace (prefixWord ++ tailWord_507668) baseStart_507668 baseEnd_507668 := by
    simpa [prefixWord, tailWord_507668, baseEnd_507668] using wordTrace_append hprefix tailTrace_507668
  have hstable : (prefixWord ++ tailWord_507668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507668).length < 2 ^ (prefixWord ++ tailWord_507668).sum := by decide
  have hdescent : baseEnd_507668 < baseStart_507668 := by decide
  rcases family_descends (prefixWord ++ tailWord_507668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507756 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 6]
def baseStart_507756 : Nat := 118140960795 + 507756 * 2 ^ 59
def prefixEnd_507756 : Nat := 4983230072969 + 3 ^ 40 * 507756 * 2
def baseEnd_507756 : Nat := 231753673959485009791003

theorem tailTrace_507756 : CollatzResearch.WordTrace tailWord_507756 prefixEnd_507756 231753673959485009791003 := by
  unfold tailWord_507756
  simp only [CollatzResearch.WordTrace]
  refine ⟨9259691374247102332975561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12346255165662803110634081 9259691374247102332975561)
  ·
    refine ⟨6944768530685326749731671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9259691374247102332975561 6944768530685326749731671)
    ·
      refine ⟨10417152796027990124597507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6944768530685326749731671 10417152796027990124597507)
      ·
        refine ⟨15625729194041985186896261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10417152796027990124597507 15625729194041985186896261)
        ·
          refine ⟨2929824223882872222543049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15625729194041985186896261 2929824223882872222543049)
          ·
            refine ⟨2197368167912154166907287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2929824223882872222543049 2197368167912154166907287)
            ·
              refine ⟨3296052251868231250360931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2197368167912154166907287 3296052251868231250360931)
              ·
                refine ⟨4944078377802346875541397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3296052251868231250360931 4944078377802346875541397)
                ·
                  refine ⟨231753673959485009791003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4944078377802346875541397 231753673959485009791003)
                  ·
                    rfl

theorem cell20_507756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_507756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507756 prefixEnd_507756 := by exact prefixLift 507756
  have htrace : WordTrace (prefixWord ++ tailWord_507756) baseStart_507756 baseEnd_507756 := by
    simpa [prefixWord, tailWord_507756, baseEnd_507756] using wordTrace_append hprefix tailTrace_507756
  have hstable : (prefixWord ++ tailWord_507756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507756).length < 2 ^ (prefixWord ++ tailWord_507756).sum := by decide
  have hdescent : baseEnd_507756 < baseStart_507756 := by decide
  rcases family_descends (prefixWord ++ tailWord_507756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507783 : List Nat := [1, 1, 4, 2, 4, 2, 1, 2, 3]
def baseStart_507783 : Nat := 118140960795 + 507783 * 2 ^ 59
def prefixEnd_507783 : Nat := 4983230072969 + 3 ^ 40 * 507783 * 2
def baseEnd_507783 : Nat := 231765997495192915890893

theorem tailTrace_507783 : CollatzResearch.WordTrace tailWord_507783 prefixEnd_507783 231765997495192915890893 := by
  unfold tailWord_507783
  simp only [CollatzResearch.WordTrace]
  refine ⟨18520367519396388277184003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12346911679597592184789335 18520367519396388277184003)
  ·
    refine ⟨27780551279094582415776005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18520367519396388277184003 27780551279094582415776005)
    ·
      refine ⟨5208853364830234202958001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27780551279094582415776005 5208853364830234202958001)
      ·
        refine ⟨3906640023622675652218501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5208853364830234202958001 3906640023622675652218501)
        ·
          refine ⟨732495004429251684790969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3906640023622675652218501 732495004429251684790969)
          ·
            refine ⟨549371253321938763593227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 732495004429251684790969 549371253321938763593227)
            ·
              refine ⟨824056879982908145389841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549371253321938763593227 824056879982908145389841)
              ·
                refine ⟨618042659987181109042381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 824056879982908145389841 618042659987181109042381)
                ·
                  refine ⟨231765997495192915890893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 618042659987181109042381 231765997495192915890893)
                  ·
                    rfl

theorem cell20_507783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 3].length) (baseStart_507783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507783 prefixEnd_507783 := by exact prefixLift 507783
  have htrace : WordTrace (prefixWord ++ tailWord_507783) baseStart_507783 baseEnd_507783 := by
    simpa [prefixWord, tailWord_507783, baseEnd_507783] using wordTrace_append hprefix tailTrace_507783
  have hstable : (prefixWord ++ tailWord_507783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507783).length < 2 ^ (prefixWord ++ tailWord_507783).sum := by decide
  have hdescent : baseEnd_507783 < baseStart_507783 := by decide
  rcases family_descends (prefixWord ++ tailWord_507783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507800 : List Nat := [2, 1, 2, 6, 1, 1, 3, 1, 3]
def baseStart_507800 : Nat := 118140960795 + 507800 * 2 ^ 59
def prefixEnd_507800 : Nat := 4983230072969 + 3 ^ 40 * 507800 * 2
def baseEnd_507800 : Nat := 231773756758416412324157

theorem tailTrace_507800 : CollatzResearch.WordTrace tailWord_507800 prefixEnd_507800 231773756758416412324157 := by
  unfold tailWord_507800
  simp only [CollatzResearch.WordTrace]
  refine ⟨9260493780167400090276427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12347325040223200120368569 9260493780167400090276427)
  ·
    refine ⟨13890740670251100135414641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9260493780167400090276427 13890740670251100135414641)
    ·
      refine ⟨10418055502688325101560981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13890740670251100135414641 10418055502688325101560981)
      ·
        refine ⟨488346351688515239135671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10418055502688325101560981 488346351688515239135671)
        ·
          refine ⟨732519527532772858703507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488346351688515239135671 732519527532772858703507)
          ·
            refine ⟨1098779291299159288055261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732519527532772858703507 1098779291299159288055261)
            ·
              refine ⟨412042234237184733020723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1098779291299159288055261 412042234237184733020723)
              ·
                refine ⟨618063351355777099531085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412042234237184733020723 618063351355777099531085)
                ·
                  refine ⟨231773756758416412324157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 618063351355777099531085 231773756758416412324157)
                  ·
                    rfl

theorem cell20_507800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 3].length) (baseStart_507800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507800 prefixEnd_507800 := by exact prefixLift 507800
  have htrace : WordTrace (prefixWord ++ tailWord_507800) baseStart_507800 baseEnd_507800 := by
    simpa [prefixWord, tailWord_507800, baseEnd_507800] using wordTrace_append hprefix tailTrace_507800
  have hstable : (prefixWord ++ tailWord_507800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507800).length < 2 ^ (prefixWord ++ tailWord_507800).sum := by decide
  have hdescent : baseEnd_507800 < baseStart_507800 := by decide
  rcases family_descends (prefixWord ++ tailWord_507800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507825 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 5]
def baseStart_507825 : Nat := 118140960795 + 507825 * 2 ^ 59
def prefixEnd_507825 : Nat := 4983230072969 + 3 ^ 40 * 507825 * 2
def baseEnd_507825 : Nat := 231785167439627436490721

theorem tailTrace_507825 : CollatzResearch.WordTrace tailWord_507825 prefixEnd_507825 231785167439627436490721 := by
  unfold tailWord_507825
  simp only [CollatzResearch.WordTrace]
  refine ⟨18521899385244229450212929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12347932923496152966808619 18521899385244229450212929)
  ·
    refine ⟨13891424538933172087659697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18521899385244229450212929 13891424538933172087659697)
    ·
      refine ⟨10418568404199879065744773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13891424538933172087659697 10418568404199879065744773)
      ·
        refine ⟨1953481575787477324827145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10418568404199879065744773 1953481575787477324827145)
        ·
          refine ⟨1465111181840607993620359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1953481575787477324827145 1465111181840607993620359)
          ·
            refine ⟨2197666772760911990430539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465111181840607993620359 2197666772760911990430539)
            ·
              refine ⟨3296500159141367985645809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2197666772760911990430539 3296500159141367985645809)
              ·
                refine ⟨2472375119356025989234357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3296500159141367985645809 2472375119356025989234357)
                ·
                  refine ⟨231785167439627436490721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2472375119356025989234357 231785167439627436490721)
                  ·
                    rfl

theorem cell20_507825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_507825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507825 prefixEnd_507825 := by exact prefixLift 507825
  have htrace : WordTrace (prefixWord ++ tailWord_507825) baseStart_507825 baseEnd_507825 := by
    simpa [prefixWord, tailWord_507825, baseEnd_507825] using wordTrace_append hprefix tailTrace_507825
  have hstable : (prefixWord ++ tailWord_507825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507825).length < 2 ^ (prefixWord ++ tailWord_507825).sum := by decide
  have hdescent : baseEnd_507825 < baseStart_507825 := by decide
  rcases family_descends (prefixWord ++ tailWord_507825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507863 : List Nat := [1, 1, 3, 2, 1, 1, 5, 3, 3]
def baseStart_507863 : Nat := 118140960795 + 507863 * 2 ^ 59
def prefixEnd_507863 : Nat := 4983230072969 + 3 ^ 40 * 507863 * 2
def baseEnd_507863 : Nat := 231802511675068193223899

theorem tailTrace_507863 : CollatzResearch.WordTrace tailWord_507863 prefixEnd_507863 231802511675068193223899 := by
  unfold tailWord_507863
  simp only [CollatzResearch.WordTrace]
  refine ⟨18523285359106561940096243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12348856906071041293397495 18523285359106561940096243)
  ·
    refine ⟨27784928038659842910144365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18523285359106561940096243 27784928038659842910144365)
    ·
      refine ⟨10419348014497441091304137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27784928038659842910144365 10419348014497441091304137)
      ·
        refine ⟨7814511010873080818478103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10419348014497441091304137 7814511010873080818478103)
        ·
          refine ⟨11721766516309621227717155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7814511010873080818478103 11721766516309621227717155)
          ·
            refine ⟨17582649774464431841575733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11721766516309621227717155 17582649774464431841575733)
            ·
              refine ⟨1648373416356040485147725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17582649774464431841575733 1648373416356040485147725)
              ·
                refine ⟨618140031133515181930397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1648373416356040485147725 618140031133515181930397)
                ·
                  refine ⟨231802511675068193223899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 618140031133515181930397 231802511675068193223899)
                  ·
                    rfl

theorem cell20_507863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 3].length) (baseStart_507863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507863 prefixEnd_507863 := by exact prefixLift 507863
  have htrace : WordTrace (prefixWord ++ tailWord_507863) baseStart_507863 baseEnd_507863 := by
    simpa [prefixWord, tailWord_507863, baseEnd_507863] using wordTrace_append hprefix tailTrace_507863
  have hstable : (prefixWord ++ tailWord_507863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507863).length < 2 ^ (prefixWord ++ tailWord_507863).sum := by decide
  have hdescent : baseEnd_507863 < baseStart_507863 := by decide
  rcases family_descends (prefixWord ++ tailWord_507863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507884 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 7]
def baseStart_507884 : Nat := 118140960795 + 507884 * 2 ^ 59
def prefixEnd_507884 : Nat := 4983230072969 + 3 ^ 40 * 507884 * 2
def baseEnd_507884 : Nat := 231812096647285453523813

theorem tailTrace_507884 : CollatzResearch.WordTrace tailWord_507884 prefixEnd_507884 231812096647285453523813 := by
  unfold tailWord_507884
  simp only [CollatzResearch.WordTrace]
  refine ⟨9262025646015241263305353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12349367528020321684407137 9262025646015241263305353)
  ·
    refine ⟨6946519234511430947479015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9262025646015241263305353 6946519234511430947479015)
    ·
      refine ⟨10419778851767146421218523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6946519234511430947479015 10419778851767146421218523)
      ·
        refine ⟨15629668277650719631827785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10419778851767146421218523 15629668277650719631827785)
        ·
          refine ⟨11722251208238039723870839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15629668277650719631827785 11722251208238039723870839)
          ·
            refine ⟨17583376812357059585806259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11722251208238039723870839 17583376812357059585806259)
            ·
              refine ⟨26375065218535589378709389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17583376812357059585806259 26375065218535589378709389)
              ·
                refine ⟨9890649456950846017016021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26375065218535589378709389 9890649456950846017016021)
                ·
                  refine ⟨231812096647285453523813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9890649456950846017016021 231812096647285453523813)
                  ·
                    rfl

theorem cell20_507884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_507884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507884 prefixEnd_507884 := by exact prefixLift 507884
  have htrace : WordTrace (prefixWord ++ tailWord_507884) baseStart_507884 baseEnd_507884 := by
    simpa [prefixWord, tailWord_507884, baseEnd_507884] using wordTrace_append hprefix tailTrace_507884
  have hstable : (prefixWord ++ tailWord_507884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507884).length < 2 ^ (prefixWord ++ tailWord_507884).sum := by decide
  have hdescent : baseEnd_507884 < baseStart_507884 := by decide
  rcases family_descends (prefixWord ++ tailWord_507884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507887 : List Nat := [1, 1, 2, 1, 4, 2, 2, 5, 2]
def baseStart_507887 : Nat := 118140960795 + 507887 * 2 ^ 59
def prefixEnd_507887 : Nat := 4983230072969 + 3 ^ 40 * 507887 * 2
def baseEnd_507887 : Nat := 231813465929030776423801

theorem tailTrace_507887 : CollatzResearch.WordTrace tailWord_507887 prefixEnd_507887 231813465929030776423801 := by
  unfold tailWord_507887
  simp only [CollatzResearch.WordTrace]
  refine ⟨18524160711019614038969915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12349440474013076025979943 18524160711019614038969915)
  ·
    refine ⟨27786241066529421058454873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18524160711019614038969915 27786241066529421058454873)
    ·
      refine ⟨20839680799897065793841155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27786241066529421058454873 20839680799897065793841155)
      ·
        refine ⟨31259521199845598690761733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20839680799897065793841155 31259521199845598690761733)
        ·
          refine ⟨5861160224971049754517825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31259521199845598690761733 5861160224971049754517825)
          ·
            refine ⟨4395870168728287315888369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5861160224971049754517825 4395870168728287315888369)
            ·
              refine ⟨3296902626546215486916277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4395870168728287315888369 3296902626546215486916277)
              ·
                refine ⟨309084621238707701898401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3296902626546215486916277 309084621238707701898401)
                ·
                  refine ⟨231813465929030776423801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309084621238707701898401 231813465929030776423801)
                  ·
                    rfl

theorem cell20_507887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 2].length) (baseStart_507887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507887 prefixEnd_507887 := by exact prefixLift 507887
  have htrace : WordTrace (prefixWord ++ tailWord_507887) baseStart_507887 baseEnd_507887 := by
    simpa [prefixWord, tailWord_507887, baseEnd_507887] using wordTrace_append hprefix tailTrace_507887
  have hstable : (prefixWord ++ tailWord_507887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507887).length < 2 ^ (prefixWord ++ tailWord_507887).sum := by decide
  have hdescent : baseEnd_507887 < baseStart_507887 := by decide
  rcases family_descends (prefixWord ++ tailWord_507887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507894 : List Nat := [5, 1, 1, 1, 4, 8]
def baseStart_507894 : Nat := 118140960795 + 507894 * 2 ^ 59
def prefixEnd_507894 : Nat := 4983230072969 + 3 ^ 40 * 507894 * 2
def baseEnd_507894 : Nat := 8585802256287772710757

theorem tailTrace_507894 : CollatzResearch.WordTrace tailWord_507894 prefixEnd_507894 8585802256287772710757 := by
  unfold tailWord_507894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1157776001374640889654671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12349610681329502822983157 1157776001374640889654671)
  ·
    refine ⟨1736664002061961334482007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1157776001374640889654671 1736664002061961334482007)
    ·
      refine ⟨2604996003092942001723011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1736664002061961334482007 2604996003092942001723011)
      ·
        refine ⟨3907494004639413002584517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2604996003092942001723011 3907494004639413002584517)
        ·
          refine ⟨732655125869889937984597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3907494004639413002584517 732655125869889937984597)
          ·
            refine ⟨8585802256287772710757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 732655125869889937984597 8585802256287772710757)
            ·
              rfl

theorem cell20_507894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 8].length) (baseStart_507894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507894 prefixEnd_507894 := by exact prefixLift 507894
  have htrace : WordTrace (prefixWord ++ tailWord_507894) baseStart_507894 baseEnd_507894 := by
    simpa [prefixWord, tailWord_507894, baseEnd_507894] using wordTrace_append hprefix tailTrace_507894
  have hstable : (prefixWord ++ tailWord_507894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507894).length < 2 ^ (prefixWord ++ tailWord_507894).sum := by decide
  have hdescent : baseEnd_507894 < baseStart_507894 := by decide
  rcases family_descends (prefixWord ++ tailWord_507894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507901 : List Nat := [1, 4, 1, 1, 1, 2, 3, 4, 3]
def baseStart_507901 : Nat := 118140960795 + 507901 * 2 ^ 59
def prefixEnd_507901 : Nat := 4983230072969 + 3 ^ 40 * 507901 * 2
def baseEnd_507901 : Nat := 231819855910508949957077

theorem tailTrace_507901 : CollatzResearch.WordTrace tailWord_507901 prefixEnd_507901 231819855910508949957077 := by
  unfold tailWord_507901
  simp only [CollatzResearch.WordTrace]
  refine ⟨18524671332968894429979557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12349780888645929619986371 18524671332968894429979557)
  ·
    refine ⟨3473375874931667705621167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18524671332968894429979557 3473375874931667705621167)
    ·
      refine ⟨5210063812397501558431751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3473375874931667705621167 5210063812397501558431751)
      ·
        refine ⟨7815095718596252337647627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5210063812397501558431751 7815095718596252337647627)
        ·
          refine ⟨11722643577894378506471441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7815095718596252337647627 11722643577894378506471441)
          ·
            refine ⟨8791982683420783879853581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11722643577894378506471441 8791982683420783879853581)
            ·
              refine ⟨3296993506282793954945093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8791982683420783879853581 3296993506282793954945093)
              ·
                refine ⟨618186282428023866552205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3296993506282793954945093 618186282428023866552205)
                ·
                  refine ⟨231819855910508949957077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 618186282428023866552205 231819855910508949957077)
                  ·
                    rfl

theorem cell20_507901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_507901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507901 prefixEnd_507901 := by exact prefixLift 507901
  have htrace : WordTrace (prefixWord ++ tailWord_507901) baseStart_507901 baseEnd_507901 := by
    simpa [prefixWord, tailWord_507901, baseEnd_507901] using wordTrace_append hprefix tailTrace_507901
  have hstable : (prefixWord ++ tailWord_507901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507901).length < 2 ^ (prefixWord ++ tailWord_507901).sum := by decide
  have hdescent : baseEnd_507901 < baseStart_507901 := by decide
  rcases family_descends (prefixWord ++ tailWord_507901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507925 : List Nat := [1, 3, 2, 1, 5, 1, 1, 2, 4]
def baseStart_507925 : Nat := 118140960795 + 507925 * 2 ^ 59
def prefixEnd_507925 : Nat := 4983230072969 + 3 ^ 40 * 507925 * 2
def baseEnd_507925 : Nat := 231830810164471533156979

theorem tailTrace_507925 : CollatzResearch.WordTrace tailWord_507925 prefixEnd_507925 231830810164471533156979 := by
  unfold tailWord_507925
  simp only [CollatzResearch.WordTrace]
  refine ⟨18525546684881946528853229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12350364456587964352568819 18525546684881946528853229)
  ·
    refine ⟨6947080006830729948319961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18525546684881946528853229 6947080006830729948319961)
    ·
      refine ⟨5210310005123047461239971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6947080006830729948319961 5210310005123047461239971)
      ·
        refine ⟨7815465007684571191859957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5210310005123047461239971 7815465007684571191859957)
        ·
          refine ⟨732699844470428549236871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7815465007684571191859957 732699844470428549236871)
          ·
            refine ⟨1099049766705642823855307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 732699844470428549236871 1099049766705642823855307)
            ·
              refine ⟨1648574650058464235782961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099049766705642823855307 1648574650058464235782961)
              ·
                refine ⟨1236430987543848176837221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1648574650058464235782961 1236430987543848176837221)
                ·
                  refine ⟨231830810164471533156979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1236430987543848176837221 231830810164471533156979)
                  ·
                    rfl

theorem cell20_507925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_507925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507925 prefixEnd_507925 := by exact prefixLift 507925
  have htrace : WordTrace (prefixWord ++ tailWord_507925) baseStart_507925 baseEnd_507925 := by
    simpa [prefixWord, tailWord_507925, baseEnd_507925] using wordTrace_append hprefix tailTrace_507925
  have hstable : (prefixWord ++ tailWord_507925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507925).length < 2 ^ (prefixWord ++ tailWord_507925).sum := by decide
  have hdescent : baseEnd_507925 < baseStart_507925 := by decide
  rcases family_descends (prefixWord ++ tailWord_507925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507953 : List Nat := [1, 2, 2, 3, 1, 4, 7]
def baseStart_507953 : Nat := 118140960795 + 507953 * 2 ^ 59
def prefixEnd_507953 : Nat := 4983230072969 + 3 ^ 40 * 507953 * 2
def baseEnd_507953 : Nat := 25760398903047542247059

theorem tailTrace_507953 : CollatzResearch.WordTrace tailWord_507953 prefixEnd_507953 25760398903047542247059 := by
  unfold tailWord_507953
  simp only [CollatzResearch.WordTrace]
  refine ⟨18526567928780507310872513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12351045285853671540581675 18526567928780507310872513)
  ·
    refine ⟨13894925946585380483154385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18526567928780507310872513 13894925946585380483154385)
    ·
      refine ⟨10421194459939035362365789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13894925946585380483154385 10421194459939035362365789)
      ·
        refine ⟨3907947922477138260887171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10421194459939035362365789 3907947922477138260887171)
        ·
          refine ⟨5861921883715707391330757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3907947922477138260887171 5861921883715707391330757)
          ·
            refine ⟨1099110353196695135874517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5861921883715707391330757 1099110353196695135874517)
            ·
              refine ⟨25760398903047542247059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1099110353196695135874517 25760398903047542247059)
              ·
                rfl

theorem cell20_507953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 7].length) (baseStart_507953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507953 prefixEnd_507953 := by exact prefixLift 507953
  have htrace : WordTrace (prefixWord ++ tailWord_507953) baseStart_507953 baseEnd_507953 := by
    simpa [prefixWord, tailWord_507953, baseEnd_507953] using wordTrace_append hprefix tailTrace_507953
  have hstable : (prefixWord ++ tailWord_507953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507953).length < 2 ^ (prefixWord ++ tailWord_507953).sum := by decide
  have hdescent : baseEnd_507953 < baseStart_507953 := by decide
  rcases family_descends (prefixWord ++ tailWord_507953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_507997 : List Nat := [1, 4, 4, 1, 1, 1, 3, 3, 2]
def baseStart_507997 : Nat := 118140960795 + 507997 * 2 ^ 59
def prefixEnd_507997 : Nat := 4983230072969 + 3 ^ 40 * 507997 * 2
def baseEnd_507997 : Nat := 231863672926359282756685

theorem tailTrace_507997 : CollatzResearch.WordTrace tailWord_507997 prefixEnd_507997 231863672926359282756685 := by
  unfold tailWord_507997
  simp only [CollatzResearch.WordTrace]
  refine ⟨18528172740621102825474245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12352115160414068550316163 18528172740621102825474245)
  ·
    refine ⟨3474032388866456779776421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18528172740621102825474245 3474032388866456779776421)
    ·
      refine ⟨651381072912460646208079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3474032388866456779776421 651381072912460646208079)
      ·
        refine ⟨977071609368690969312119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651381072912460646208079 977071609368690969312119)
        ·
          refine ⟨1465607414053036453968179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977071609368690969312119 1465607414053036453968179)
          ·
            refine ⟨2198411121079554680952269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465607414053036453968179 2198411121079554680952269)
            ·
              refine ⟨824404170404833005357101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2198411121079554680952269 824404170404833005357101)
              ·
                refine ⟨309151563901812377008913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 824404170404833005357101 309151563901812377008913)
                ·
                  refine ⟨231863672926359282756685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309151563901812377008913 231863672926359282756685)
                  ·
                    rfl

theorem cell20_507997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_507997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_507997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_507997 prefixEnd_507997 := by exact prefixLift 507997
  have htrace : WordTrace (prefixWord ++ tailWord_507997) baseStart_507997 baseEnd_507997 := by
    simpa [prefixWord, tailWord_507997, baseEnd_507997] using wordTrace_append hprefix tailTrace_507997
  have hstable : (prefixWord ++ tailWord_507997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_507997).length < 2 ^ (prefixWord ++ tailWord_507997).sum := by decide
  have hdescent : baseEnd_507997 < baseStart_507997 := by decide
  rcases family_descends (prefixWord ++ tailWord_507997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508029 : List Nat := [1, 4, 1, 1, 3, 2, 1, 7]
def baseStart_508029 : Nat := 118140960795 + 508029 * 2 ^ 59
def prefixEnd_508029 : Nat := 4983230072969 + 3 ^ 40 * 508029 * 2
def baseEnd_508029 : Nat := 77292759532769797896629

theorem tailTrace_508029 : CollatzResearch.WordTrace tailWord_508029 prefixEnd_508029 77292759532769797896629 := by
  unfold tailWord_508029
  simp only [CollatzResearch.WordTrace]
  refine ⟨18529339876505172290639141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12352893251003448193759427 18529339876505172290639141)
  ·
    refine ⟨3474251226844719804494839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18529339876505172290639141 3474251226844719804494839)
    ·
      refine ⟨5211376840267079706742259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3474251226844719804494839 5211376840267079706742259)
      ·
        refine ⟨7817065260400619560113389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5211376840267079706742259 7817065260400619560113389)
        ·
          refine ⟨2931399472650232335042521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7817065260400619560113389 2931399472650232335042521)
          ·
            refine ⟨2198549604487674251281891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2931399472650232335042521 2198549604487674251281891)
            ·
              refine ⟨3297824406731511376922837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2198549604487674251281891 3297824406731511376922837)
              ·
                refine ⟨77292759532769797896629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3297824406731511376922837 77292759532769797896629)
                ·
                  rfl

theorem cell20_508029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 7].length) (baseStart_508029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508029 prefixEnd_508029 := by exact prefixLift 508029
  have htrace : WordTrace (prefixWord ++ tailWord_508029) baseStart_508029 baseEnd_508029 := by
    simpa [prefixWord, tailWord_508029, baseEnd_508029] using wordTrace_append hprefix tailTrace_508029
  have hstable : (prefixWord ++ tailWord_508029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508029).length < 2 ^ (prefixWord ++ tailWord_508029).sum := by decide
  have hdescent : baseEnd_508029 < baseStart_508029 := by decide
  rcases family_descends (prefixWord ++ tailWord_508029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508119 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 8]
def baseStart_508119 : Nat := 118140960795 + 508119 * 2 ^ 59
def prefixEnd_508119 : Nat := 4983230072969 + 3 ^ 40 * 508119 * 2
def baseEnd_508119 : Nat := 231919357050669080689519

theorem tailTrace_508119 : CollatzResearch.WordTrace tailWord_508119 prefixEnd_508119 231919357050669080689519 := by
  unfold tailWord_508119
  simp only [CollatzResearch.WordTrace]
  refine ⟨18532622446179117661415411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12355081630786078440943607 18532622446179117661415411)
  ·
    refine ⟨27798933669268676492123117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18532622446179117661415411 27798933669268676492123117)
    ·
      refine ⟨10424600125975753684546169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27798933669268676492123117 10424600125975753684546169)
      ·
        refine ⟨7818450094481815263409627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10424600125975753684546169 7818450094481815263409627)
        ·
          refine ⟨11727675141722722895114441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7818450094481815263409627 11727675141722722895114441)
          ·
            refine ⟨8795756356292042171335831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11727675141722722895114441 8795756356292042171335831)
            ·
              refine ⟨13193634534438063257003747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8795756356292042171335831 13193634534438063257003747)
              ·
                refine ⟨19790451801657094885505621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13193634534438063257003747 19790451801657094885505621)
                ·
                  refine ⟨231919357050669080689519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19790451801657094885505621 231919357050669080689519)
                  ·
                    rfl

theorem cell20_508119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_508119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508119 prefixEnd_508119 := by exact prefixLift 508119
  have htrace : WordTrace (prefixWord ++ tailWord_508119) baseStart_508119 baseEnd_508119 := by
    simpa [prefixWord, tailWord_508119, baseEnd_508119] using wordTrace_append hprefix tailTrace_508119
  have hstable : (prefixWord ++ tailWord_508119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508119).length < 2 ^ (prefixWord ++ tailWord_508119).sum := by decide
  have hdescent : baseEnd_508119 < baseStart_508119 := by decide
  rcases family_descends (prefixWord ++ tailWord_508119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508125 : List Nat := [1, 4, 3, 2, 1, 3, 1, 2, 3]
def baseStart_508125 : Nat := 118140960795 + 508125 * 2 ^ 59
def prefixEnd_508125 : Nat := 4983230072969 + 3 ^ 40 * 508125 * 2
def baseEnd_508125 : Nat := 231922095614159726489495

theorem tailTrace_508125 : CollatzResearch.WordTrace tailWord_508125 prefixEnd_508125 231922095614159726489495 := by
  unfold tailWord_508125
  simp only [CollatzResearch.WordTrace]
  refine ⟨18532841284157380686133829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12355227522771587124089219 18532841284157380686133829)
  ·
    refine ⟨3474907740779508878650093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18532841284157380686133829 3474907740779508878650093)
    ·
      refine ⟨1303090402792315829493785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3474907740779508878650093 1303090402792315829493785)
      ·
        refine ⟨977317802094236872120339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1303090402792315829493785 977317802094236872120339)
        ·
          refine ⟨1465976703141355308180509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977317802094236872120339 1465976703141355308180509)
          ·
            refine ⟨549741263678008240567691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1465976703141355308180509 549741263678008240567691)
            ·
              refine ⟨824611895517012360851537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549741263678008240567691 824611895517012360851537)
              ·
                refine ⟨618458921637759270638653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 824611895517012360851537 618458921637759270638653)
                ·
                  refine ⟨231922095614159726489495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 618458921637759270638653 231922095614159726489495)
                  ·
                    rfl

theorem cell20_508125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_508125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508125 prefixEnd_508125 := by exact prefixLift 508125
  have htrace : WordTrace (prefixWord ++ tailWord_508125) baseStart_508125 baseEnd_508125 := by
    simpa [prefixWord, tailWord_508125, baseEnd_508125] using wordTrace_append hprefix tailTrace_508125
  have hstable : (prefixWord ++ tailWord_508125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508125).length < 2 ^ (prefixWord ++ tailWord_508125).sum := by decide
  have hdescent : baseEnd_508125 < baseStart_508125 := by decide
  rcases family_descends (prefixWord ++ tailWord_508125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508136 : List Nat := [2, 1, 4, 1, 2, 2, 1, 3, 4]
def baseStart_508136 : Nat := 118140960795 + 508136 * 2 ^ 59
def prefixEnd_508136 : Nat := 4983230072969 + 3 ^ 40 * 508136 * 2
def baseEnd_508136 : Nat := 231927116313892577122783

theorem tailTrace_508136 : CollatzResearch.WordTrace tailWord_508136 prefixEnd_508136 231927116313892577122783 := by
  unfold tailWord_508136
  simp only [CollatzResearch.WordTrace]
  refine ⟨9266621243558764782392131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12355494991411686376522841 9266621243558764782392131)
  ·
    refine ⟨13899931865338147173588197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9266621243558764782392131 13899931865338147173588197)
    ·
      refine ⟨2606237224750902595047787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13899931865338147173588197 2606237224750902595047787)
      ·
        refine ⟨3909355837126353892571681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2606237224750902595047787 3909355837126353892571681)
        ·
          refine ⟨2932016877844765419428761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3909355837126353892571681 2932016877844765419428761)
          ·
            refine ⟨2199012658383574064571571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2932016877844765419428761 2199012658383574064571571)
            ·
              refine ⟨3298518987575361096857357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2199012658383574064571571 3298518987575361096857357)
              ·
                refine ⟨1236944620340760411321509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3298518987575361096857357 1236944620340760411321509)
                ·
                  refine ⟨231927116313892577122783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1236944620340760411321509 231927116313892577122783)
                  ·
                    rfl

theorem cell20_508136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_508136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508136 prefixEnd_508136 := by exact prefixLift 508136
  have htrace : WordTrace (prefixWord ++ tailWord_508136) baseStart_508136 baseEnd_508136 := by
    simpa [prefixWord, tailWord_508136, baseEnd_508136] using wordTrace_append hprefix tailTrace_508136
  have hstable : (prefixWord ++ tailWord_508136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508136).length < 2 ^ (prefixWord ++ tailWord_508136).sum := by decide
  have hdescent : baseEnd_508136 < baseStart_508136 := by decide
  rcases family_descends (prefixWord ++ tailWord_508136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508191 : List Nat := [1, 1, 2, 4, 3, 3, 1, 1, 4]
def baseStart_508191 : Nat := 118140960795 + 508191 * 2 ^ 59
def prefixEnd_508191 : Nat := 4983230072969 + 3 ^ 40 * 508191 * 2
def baseEnd_508191 : Nat := 231952219812556830289225

theorem tailTrace_508191 : CollatzResearch.WordTrace tailWord_508191 prefixEnd_508191 231952219812556830289225 := by
  unfold tailWord_508191
  simp only [CollatzResearch.WordTrace]
  refine ⟨18535248501918273958036427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12356832334612182638690951 18535248501918273958036427)
  ·
    refine ⟨27802872752877410937054641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18535248501918273958036427 27802872752877410937054641)
    ·
      refine ⟨20852154564658058202790981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27802872752877410937054641 20852154564658058202790981)
      ·
        refine ⟨3909778980873385913023309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20852154564658058202790981 3909778980873385913023309)
        ·
          refine ⟨1466167117827519717383741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3909778980873385913023309 1466167117827519717383741)
          ·
            refine ⟨549812669185319894018903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1466167117827519717383741 549812669185319894018903)
            ·
              refine ⟨824719003777979841028355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549812669185319894018903 824719003777979841028355)
              ·
                refine ⟨1237078505666969761542533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 824719003777979841028355 1237078505666969761542533)
                ·
                  refine ⟨231952219812556830289225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1237078505666969761542533 231952219812556830289225)
                  ·
                    rfl

theorem cell20_508191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 4].length) (baseStart_508191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508191 prefixEnd_508191 := by exact prefixLift 508191
  have htrace : WordTrace (prefixWord ++ tailWord_508191) baseStart_508191 baseEnd_508191 := by
    simpa [prefixWord, tailWord_508191, baseEnd_508191] using wordTrace_append hprefix tailTrace_508191
  have hstable : (prefixWord ++ tailWord_508191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508191).length < 2 ^ (prefixWord ++ tailWord_508191).sum := by decide
  have hdescent : baseEnd_508191 < baseStart_508191 := by decide
  rcases family_descends (prefixWord ++ tailWord_508191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508240 : List Nat := [2, 1, 1, 1, 1, 14]
def baseStart_508240 : Nat := 118140960795 + 508240 * 2 ^ 59
def prefixEnd_508240 : Nat := 4983230072969 + 3 ^ 40 * 508240 * 2
def baseEnd_508240 : Nat := 8591651286952979172433

theorem tailTrace_508240 : CollatzResearch.WordTrace tailWord_508240 prefixEnd_508240 8591651286952979172433 := by
  unfold tailWord_508240
  simp only [CollatzResearch.WordTrace]
  refine ⟨9268517839370377663285087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12358023785827170217713449 9268517839370377663285087)
  ·
    refine ⟨13902776759055566494927631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9268517839370377663285087 13902776759055566494927631)
    ·
      refine ⟨20854165138583349742391447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13902776759055566494927631 20854165138583349742391447)
      ·
        refine ⟨31281247707875024613587171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20854165138583349742391447 31281247707875024613587171)
        ·
          refine ⟨46921871561812536920380757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31281247707875024613587171 46921871561812536920380757)
          ·
            refine ⟨8591651286952979172433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 46921871561812536920380757 8591651286952979172433)
            ·
              rfl

theorem cell20_508240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 14].length) (baseStart_508240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508240 prefixEnd_508240 := by exact prefixLift 508240
  have htrace : WordTrace (prefixWord ++ tailWord_508240) baseStart_508240 baseEnd_508240 := by
    simpa [prefixWord, tailWord_508240, baseEnd_508240] using wordTrace_append hprefix tailTrace_508240
  have hstable : (prefixWord ++ tailWord_508240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508240).length < 2 ^ (prefixWord ++ tailWord_508240).sum := by decide
  have hdescent : baseEnd_508240 < baseStart_508240 := by decide
  rcases family_descends (prefixWord ++ tailWord_508240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508274 : List Nat := [3, 2, 1, 2, 1, 4, 3, 4]
def baseStart_508274 : Nat := 118140960795 + 508274 * 2 ^ 59
def prefixEnd_508274 : Nat := 4983230072969 + 3 ^ 40 * 508274 * 2
def baseEnd_508274 : Nat := 77330034424725810174073

theorem tailTrace_508274 : CollatzResearch.WordTrace tailWord_508274 prefixEnd_508274 77330034424725810174073 := by
  unfold tailWord_508274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4634568940154394783326969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12358850507078386088871917 4634568940154394783326969)
  ·
    refine ⟨3475926705115796087495227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4634568940154394783326969 3475926705115796087495227)
    ·
      refine ⟨5213890057673694131242841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3475926705115796087495227 5213890057673694131242841)
      ·
        refine ⟨3910417543255270598432131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5213890057673694131242841 3910417543255270598432131)
        ·
          refine ⟨5865626314882905897648197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3910417543255270598432131 5865626314882905897648197)
          ·
            refine ⟨1099804934040544855809037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5865626314882905897648197 1099804934040544855809037)
            ·
              refine ⟨412426850265204320928389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1099804934040544855809037 412426850265204320928389)
              ·
                refine ⟨77330034424725810174073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 412426850265204320928389 77330034424725810174073)
                ·
                  rfl

theorem cell20_508274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_508274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508274 prefixEnd_508274 := by exact prefixLift 508274
  have htrace : WordTrace (prefixWord ++ tailWord_508274) baseStart_508274 baseEnd_508274 := by
    simpa [prefixWord, tailWord_508274, baseEnd_508274] using wordTrace_append hprefix tailTrace_508274
  have hstable : (prefixWord ++ tailWord_508274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508274).length < 2 ^ (prefixWord ++ tailWord_508274).sum := by decide
  have hdescent : baseEnd_508274 < baseStart_508274 := by decide
  rcases family_descends (prefixWord ++ tailWord_508274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508298 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 5]
def baseStart_508298 : Nat := 118140960795 + 508298 * 2 ^ 59
def prefixEnd_508298 : Nat := 4983230072969 + 3 ^ 40 * 508298 * 2
def baseEnd_508298 : Nat := 232001057528140013722121

theorem tailTrace_508298 : CollatzResearch.WordTrace tailWord_508298 prefixEnd_508298 232001057528140013722121 := by
  unfold tailWord_508298
  simp only [CollatzResearch.WordTrace]
  refine ⟨4634787778132657808045387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12359434075020420821454365 4634787778132657808045387)
  ·
    refine ⟨6952181667198986712068081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4634787778132657808045387 6952181667198986712068081)
    ·
      refine ⟨5214136250399240034051061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6952181667198986712068081 5214136250399240034051061)
      ·
        refine ⟨488825273474928753192287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5214136250399240034051061 488825273474928753192287)
        ·
          refine ⟨733237910212393129788431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488825273474928753192287 733237910212393129788431)
          ·
            refine ⟨1099856865318589694682647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733237910212393129788431 1099856865318589694682647)
            ·
              refine ⟨1649785297977884542023971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099856865318589694682647 1649785297977884542023971)
              ·
                refine ⟨2474677946966826813035957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1649785297977884542023971 2474677946966826813035957)
                ·
                  refine ⟨232001057528140013722121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2474677946966826813035957 232001057528140013722121)
                  ·
                    rfl

theorem cell20_508298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_508298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508298 prefixEnd_508298 := by exact prefixLift 508298
  have htrace : WordTrace (prefixWord ++ tailWord_508298) baseStart_508298 baseEnd_508298 := by
    simpa [prefixWord, tailWord_508298, baseEnd_508298] using wordTrace_append hprefix tailTrace_508298
  have hstable : (prefixWord ++ tailWord_508298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508298).length < 2 ^ (prefixWord ++ tailWord_508298).sum := by decide
  have hdescent : baseEnd_508298 < baseStart_508298 := by decide
  rcases family_descends (prefixWord ++ tailWord_508298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508343 : List Nat := [1, 1, 3, 1, 3, 3, 3, 3, 2]
def baseStart_508343 : Nat := 118140960795 + 508343 * 2 ^ 59
def prefixEnd_508343 : Nat := 4983230072969 + 3 ^ 40 * 508343 * 2
def baseEnd_508343 : Nat := 232021596754319857221937

theorem tailTrace_508343 : CollatzResearch.WordTrace tailWord_508343 prefixEnd_508343 232021596754319857221937 := by
  unfold tailWord_508343
  simp only [CollatzResearch.WordTrace]
  refine ⟨18540792397367603917569683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12360528264911735945046455 18540792397367603917569683)
  ·
    refine ⟨27811188596051405876354525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18540792397367603917569683 27811188596051405876354525)
    ·
      refine ⟨10429195723519277203632947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27811188596051405876354525 10429195723519277203632947)
      ·
        refine ⟨15643793585278915805449421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10429195723519277203632947 15643793585278915805449421)
        ·
          refine ⟨5866422594479593427043533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15643793585278915805449421 5866422594479593427043533)
          ·
            refine ⟨2199908472929847535141325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5866422594479593427043533 2199908472929847535141325)
            ·
              refine ⟨824965677348692825677997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2199908472929847535141325 824965677348692825677997)
              ·
                refine ⟨309362129005759809629249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 824965677348692825677997 309362129005759809629249)
                ·
                  refine ⟨232021596754319857221937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309362129005759809629249 232021596754319857221937)
                  ·
                    rfl

theorem cell20_508343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 3, 2].length) (baseStart_508343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508343 prefixEnd_508343 := by exact prefixLift 508343
  have htrace : WordTrace (prefixWord ++ tailWord_508343) baseStart_508343 baseEnd_508343 := by
    simpa [prefixWord, tailWord_508343, baseEnd_508343] using wordTrace_append hprefix tailTrace_508343
  have hstable : (prefixWord ++ tailWord_508343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508343).length < 2 ^ (prefixWord ++ tailWord_508343).sum := by decide
  have hdescent : baseEnd_508343 < baseStart_508343 := by decide
  rcases family_descends (prefixWord ++ tailWord_508343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508360 : List Nat := [2, 1, 3, 1, 3, 3, 3, 2, 2]
def baseStart_508360 : Nat := 118140960795 + 508360 * 2 ^ 59
def prefixEnd_508360 : Nat := 4983230072969 + 3 ^ 40 * 508360 * 2
def baseEnd_508360 : Nat := 232029356017543353655201

theorem tailTrace_508360 : CollatzResearch.WordTrace tailWord_508360 prefixEnd_508360 232029356017543353655201 := by
  unfold tailWord_508360
  simp only [CollatzResearch.WordTrace]
  refine ⟨9270706219153007910469267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12360941625537343880625689 9270706219153007910469267)
  ·
    refine ⟨13906059328729511865703901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9270706219153007910469267 13906059328729511865703901)
    ·
      refine ⟨5214772248273566949638963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13906059328729511865703901 5214772248273566949638963)
      ·
        refine ⟨7822158372410350424458445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5214772248273566949638963 7822158372410350424458445)
        ·
          refine ⟨2933309389653881409171917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7822158372410350424458445 2933309389653881409171917)
          ·
            refine ⟨1099991021120205528439469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2933309389653881409171917 1099991021120205528439469)
            ·
              refine ⟨412496632920077073164801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1099991021120205528439469 412496632920077073164801)
              ·
                refine ⟨309372474690057804873601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412496632920077073164801 309372474690057804873601)
                ·
                  refine ⟨232029356017543353655201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309372474690057804873601 232029356017543353655201)
                  ·
                    rfl

theorem cell20_508360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 2].length) (baseStart_508360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508360 prefixEnd_508360 := by exact prefixLift 508360
  have htrace : WordTrace (prefixWord ++ tailWord_508360) baseStart_508360 baseEnd_508360 := by
    simpa [prefixWord, tailWord_508360, baseEnd_508360] using wordTrace_append hprefix tailTrace_508360
  have hstable : (prefixWord ++ tailWord_508360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508360).length < 2 ^ (prefixWord ++ tailWord_508360).sum := by decide
  have hdescent : baseEnd_508360 < baseStart_508360 := by decide
  rcases family_descends (prefixWord ++ tailWord_508360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508370 : List Nat := [3, 2, 2, 4, 1, 2, 2, 1, 3]
def baseStart_508370 : Nat := 118140960795 + 508370 * 2 ^ 59
def prefixEnd_508370 : Nat := 4983230072969 + 3 ^ 40 * 508370 * 2
def baseEnd_508370 : Nat := 232033920290027763321827

theorem tailTrace_508370 : CollatzResearch.WordTrace tailWord_508370 prefixEnd_508370 232033920290027763321827 := by
  unfold tailWord_508370
  simp only [CollatzResearch.WordTrace]
  refine ⟨4635444292067446882200641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12361184778846525019201709 4635444292067446882200641)
  ·
    refine ⟨3476583219050585161650481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4635444292067446882200641 3476583219050585161650481)
    ·
      refine ⟨2607437414287938871237861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3476583219050585161650481 2607437414287938871237861)
      ·
        refine ⟨488894515178988538357099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2607437414287938871237861 488894515178988538357099)
        ·
          refine ⟨733341772768482807535649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488894515178988538357099 733341772768482807535649)
          ·
            refine ⟨550006329576362105651737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 733341772768482807535649 550006329576362105651737)
            ·
              refine ⟨412504747182271579238803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550006329576362105651737 412504747182271579238803)
              ·
                refine ⟨618757120773407368858205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412504747182271579238803 618757120773407368858205)
                ·
                  refine ⟨232033920290027763321827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 618757120773407368858205 232033920290027763321827)
                  ·
                    rfl

theorem cell20_508370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_508370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508370 prefixEnd_508370 := by exact prefixLift 508370
  have htrace : WordTrace (prefixWord ++ tailWord_508370) baseStart_508370 baseEnd_508370 := by
    simpa [prefixWord, tailWord_508370, baseEnd_508370] using wordTrace_append hprefix tailTrace_508370
  have hstable : (prefixWord ++ tailWord_508370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508370).length < 2 ^ (prefixWord ++ tailWord_508370).sum := by decide
  have hdescent : baseEnd_508370 < baseStart_508370 := by decide
  rcases family_descends (prefixWord ++ tailWord_508370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508374 : List Nat := [5, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_508374 : Nat := 118140960795 + 508374 * 2 ^ 59
def prefixEnd_508374 : Nat := 4983230072969 + 3 ^ 40 * 508374 * 2
def baseEnd_508374 : Nat := 232035745999021527188477

theorem tailTrace_508374 : CollatzResearch.WordTrace tailWord_508374 prefixEnd_508374 232035745999021527188477 := by
  unfold tailWord_508374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1158870191265956013246761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12361282040170197474632117 1158870191265956013246761)
  ·
    refine ⟨869152643449467009935071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1158870191265956013246761 869152643449467009935071)
    ·
      refine ⟨1303728965174200514902607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 869152643449467009935071 1303728965174200514902607)
      ·
        refine ⟨1955593447761300772353911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1303728965174200514902607 1955593447761300772353911)
        ·
          refine ⟨2933390171641951158530867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1955593447761300772353911 2933390171641951158530867)
          ·
            refine ⟨4400085257462926737796301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2933390171641951158530867 4400085257462926737796301)
            ·
              refine ⟨1650031971548597526673613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4400085257462926737796301 1650031971548597526673613)
              ·
                refine ⟨618761989330724072502605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1650031971548597526673613 618761989330724072502605)
                ·
                  refine ⟨232035745999021527188477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 618761989330724072502605 232035745999021527188477)
                  ·
                    rfl

theorem cell20_508374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_508374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508374 prefixEnd_508374 := by exact prefixLift 508374
  have htrace : WordTrace (prefixWord ++ tailWord_508374) baseStart_508374 baseEnd_508374 := by
    simpa [prefixWord, tailWord_508374, baseEnd_508374] using wordTrace_append hprefix tailTrace_508374
  have hstable : (prefixWord ++ tailWord_508374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508374).length < 2 ^ (prefixWord ++ tailWord_508374).sum := by decide
  have hdescent : baseEnd_508374 < baseStart_508374 := by decide
  rcases family_descends (prefixWord ++ tailWord_508374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508385 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 6]
def baseStart_508385 : Nat := 118140960795 + 508385 * 2 ^ 59
def prefixEnd_508385 : Nat := 4983230072969 + 3 ^ 40 * 508385 * 2
def baseEnd_508385 : Nat := 232040766698754377821765

theorem tailTrace_508385 : CollatzResearch.WordTrace tailWord_508385 prefixEnd_508385 232040766698754377821765 := by
  unfold tailWord_508385
  simp only [CollatzResearch.WordTrace]
  refine ⟨18542324263215445090598609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12361549508810296727065739 18542324263215445090598609)
  ·
    refine ⟨13906743197411583817948957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18542324263215445090598609 13906743197411583817948957)
    ·
      refine ⟨5215028699029343931730859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13906743197411583817948957 5215028699029343931730859)
      ·
        refine ⟨7822543048544015897596289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5215028699029343931730859 7822543048544015897596289)
        ·
          refine ⟨5866907286408011923197217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7822543048544015897596289 5866907286408011923197217)
          ·
            refine ⟨4400180464806008942397913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5866907286408011923197217 4400180464806008942397913)
            ·
              refine ⟨3300135348604506706798435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4400180464806008942397913 3300135348604506706798435)
              ·
                refine ⟨4950203022906760060197653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3300135348604506706798435 4950203022906760060197653)
                ·
                  refine ⟨232040766698754377821765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4950203022906760060197653 232040766698754377821765)
                  ·
                    rfl

theorem cell20_508385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_508385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508385 prefixEnd_508385 := by exact prefixLift 508385
  have htrace : WordTrace (prefixWord ++ tailWord_508385) baseStart_508385 baseEnd_508385 := by
    simpa [prefixWord, tailWord_508385, baseEnd_508385] using wordTrace_append hprefix tailTrace_508385
  have hstable : (prefixWord ++ tailWord_508385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508385).length < 2 ^ (prefixWord ++ tailWord_508385).sum := by decide
  have hdescent : baseEnd_508385 < baseStart_508385 := by decide
  rcases family_descends (prefixWord ++ tailWord_508385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508422 : List Nat := [6, 2, 1, 1, 1, 1, 3, 5]
def baseStart_508422 : Nat := 118140960795 + 508422 * 2 ^ 59
def prefixEnd_508422 : Nat := 4983230072969 + 3 ^ 40 * 508422 * 2
def baseEnd_508422 : Nat := 77352551502315564529427

theorem tailTrace_508422 : CollatzResearch.WordTrace tailWord_508422 prefixEnd_508422 77352551502315564529427 := by
  unfold tailWord_508422
  simp only [CollatzResearch.WordTrace]
  refine ⟨579489805127543762802985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12362449176054266939797013 579489805127543762802985)
  ·
    refine ⟨434617353845657822102239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 579489805127543762802985 434617353845657822102239)
    ·
      refine ⟨651926030768486733153359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434617353845657822102239 651926030768486733153359)
      ·
        refine ⟨977889046152730099730039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651926030768486733153359 977889046152730099730039)
        ·
          refine ⟨1466833569229095149595059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977889046152730099730039 1466833569229095149595059)
          ·
            refine ⟨2200250353843642724392589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466833569229095149595059 2200250353843642724392589)
            ·
              refine ⟨825093882691366021647221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2200250353843642724392589 825093882691366021647221)
              ·
                refine ⟨77352551502315564529427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 825093882691366021647221 77352551502315564529427)
                ·
                  rfl

theorem cell20_508422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_508422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508422 prefixEnd_508422 := by exact prefixLift 508422
  have htrace : WordTrace (prefixWord ++ tailWord_508422) baseStart_508422 baseEnd_508422 := by
    simpa [prefixWord, tailWord_508422, baseEnd_508422] using wordTrace_append hprefix tailTrace_508422
  have hstable : (prefixWord ++ tailWord_508422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508422).length < 2 ^ (prefixWord ++ tailWord_508422).sum := by decide
  have hdescent : baseEnd_508422 < baseStart_508422 := by decide
  rcases family_descends (prefixWord ++ tailWord_508422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508429 : List Nat := [1, 7, 1, 1, 1, 1, 2, 3, 3]
def baseStart_508429 : Nat := 118140960795 + 508429 * 2 ^ 59
def prefixEnd_508429 : Nat := 4983230072969 + 3 ^ 40 * 508429 * 2
def baseEnd_508429 : Nat := 232060849497685780354919

theorem tailTrace_508429 : CollatzResearch.WordTrace tailWord_508429 prefixEnd_508429 232060849497685780354919 := by
  unfold tailWord_508429
  simp only [CollatzResearch.WordTrace]
  refine ⟨18543929075056040605200341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12362619383370693736800227 18543929075056040605200341)
  ·
    refine ⟨434623337696625951684383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 18543929075056040605200341 434623337696625951684383)
    ·
      refine ⟨651935006544938927526575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434623337696625951684383 651935006544938927526575)
      ·
        refine ⟨977902509817408391289863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651935006544938927526575 977902509817408391289863)
        ·
          refine ⟨1466853764726112586934795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 977902509817408391289863 1466853764726112586934795)
          ·
            refine ⟨2200280647089168880402193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1466853764726112586934795 2200280647089168880402193)
            ·
              refine ⟨1650210485316876660301645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2200280647089168880402193 1650210485316876660301645)
              ·
                refine ⟨618828931993828747613117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1650210485316876660301645 618828931993828747613117)
                ·
                  refine ⟨232060849497685780354919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 618828931993828747613117 232060849497685780354919)
                  ·
                    rfl

theorem cell20_508429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_508429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508429 prefixEnd_508429 := by exact prefixLift 508429
  have htrace : WordTrace (prefixWord ++ tailWord_508429) baseStart_508429 baseEnd_508429 := by
    simpa [prefixWord, tailWord_508429, baseEnd_508429] using wordTrace_append hprefix tailTrace_508429
  have hstable : (prefixWord ++ tailWord_508429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508429).length < 2 ^ (prefixWord ++ tailWord_508429).sum := by decide
  have hdescent : baseEnd_508429 < baseStart_508429 := by decide
  rcases family_descends (prefixWord ++ tailWord_508429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508440 : List Nat := [2, 1, 2, 3, 3, 2, 1, 2, 4]
def baseStart_508440 : Nat := 118140960795 + 508440 * 2 ^ 59
def prefixEnd_508440 : Nat := 4983230072969 + 3 ^ 40 * 508440 * 2
def baseEnd_508440 : Nat := 232065870197418630988207

theorem tailTrace_508440 : CollatzResearch.WordTrace tailWord_508440 prefixEnd_508440 232065870197418630988207 := by
  unfold tailWord_508440
  simp only [CollatzResearch.WordTrace]
  refine ⟨9272165139008094741925387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12362886852010792989233849 9272165139008094741925387)
  ·
    refine ⟨13908247708512142112888081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9272165139008094741925387 13908247708512142112888081)
    ·
      refine ⟨10431185781384106584666061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13908247708512142112888081 10431185781384106584666061)
      ·
        refine ⟨3911694668019039969249773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10431185781384106584666061 3911694668019039969249773)
        ·
          refine ⟨1466885500507139988468665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3911694668019039969249773 1466885500507139988468665)
          ·
            refine ⟨1100164125380354991351499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1466885500507139988468665 1100164125380354991351499)
            ·
              refine ⟨1650246188070532487027249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100164125380354991351499 1650246188070532487027249)
              ·
                refine ⟨1237684641052899365270437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1650246188070532487027249 1237684641052899365270437)
                ·
                  refine ⟨232065870197418630988207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1237684641052899365270437 232065870197418630988207)
                  ·
                    rfl

theorem cell20_508440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_508440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508440 prefixEnd_508440 := by exact prefixLift 508440
  have htrace : WordTrace (prefixWord ++ tailWord_508440) baseStart_508440 baseEnd_508440 := by
    simpa [prefixWord, tailWord_508440, baseEnd_508440] using wordTrace_append hprefix tailTrace_508440
  have hstable : (prefixWord ++ tailWord_508440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508440).length < 2 ^ (prefixWord ++ tailWord_508440).sum := by decide
  have hdescent : baseEnd_508440 < baseStart_508440 := by decide
  rcases family_descends (prefixWord ++ tailWord_508440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508544 : List Nat := [2, 1, 1, 2, 1, 5, 1, 7]
def baseStart_508544 : Nat := 118140960795 + 508544 * 2 ^ 59
def prefixEnd_508544 : Nat := 4983230072969 + 3 ^ 40 * 508544 * 2
def baseEnd_508544 : Nat := 77371112877085497173705

theorem tailTrace_508544 : CollatzResearch.WordTrace tailWord_508544 prefixEnd_508544 77371112877085497173705 := by
  unfold tailWord_508544
  simp only [CollatzResearch.WordTrace]
  refine ⟨9274061734819707622818343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12365415646426276830424457 9274061734819707622818343)
  ·
    refine ⟨13911092602229561434227515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9274061734819707622818343 13911092602229561434227515)
    ·
      refine ⟨20866638903344342151341273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13911092602229561434227515 20866638903344342151341273)
      ·
        refine ⟨15649979177508256613505955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20866638903344342151341273 15649979177508256613505955)
        ·
          refine ⟨23474968766262384920258933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15649979177508256613505955 23474968766262384920258933)
          ·
            refine ⟨2200778321837098586274275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23474968766262384920258933 2200778321837098586274275)
            ·
              refine ⟨3301167482755647879411413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2200778321837098586274275 3301167482755647879411413)
              ·
                refine ⟨77371112877085497173705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3301167482755647879411413 77371112877085497173705)
                ·
                  rfl

theorem cell20_508544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_508544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508544 prefixEnd_508544 := by exact prefixLift 508544
  have htrace : WordTrace (prefixWord ++ tailWord_508544) baseStart_508544 baseEnd_508544 := by
    simpa [prefixWord, tailWord_508544, baseEnd_508544] using wordTrace_append hprefix tailTrace_508544
  have hstable : (prefixWord ++ tailWord_508544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508544).length < 2 ^ (prefixWord ++ tailWord_508544).sum := by decide
  have hdescent : baseEnd_508544 < baseStart_508544 := by decide
  rcases family_descends (prefixWord ++ tailWord_508544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508547 : List Nat := [1, 1, 1, 3, 3, 1, 6, 1, 3]
def baseStart_508547 : Nat := 118140960795 + 508547 * 2 ^ 59
def prefixEnd_508547 : Nat := 4983230072969 + 3 ^ 40 * 508547 * 2
def baseEnd_508547 : Nat := 232114707913001814421103

theorem tailTrace_508547 : CollatzResearch.WordTrace tailWord_508547 prefixEnd_508547 232114707913001814421103 := by
  unfold tailWord_508547
  simp only [CollatzResearch.WordTrace]
  refine ⟨18548232888628546757995895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12365488592419031171997263 18548232888628546757995895)
  ·
    refine ⟨27822349332942820136993843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18548232888628546757995895 27822349332942820136993843)
    ·
      refine ⟨41733523999414230205490765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27822349332942820136993843 41733523999414230205490765)
      ·
        refine ⟨15650071499780336327059037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41733523999414230205490765 15650071499780336327059037)
        ·
          refine ⟨5868776812417626122647139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15650071499780336327059037 5868776812417626122647139)
          ·
            refine ⟨8803165218626439183970709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5868776812417626122647139 8803165218626439183970709)
            ·
              refine ⟨412648369623114336748627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8803165218626439183970709 412648369623114336748627)
              ·
                refine ⟨618972554434671505122941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412648369623114336748627 618972554434671505122941)
                ·
                  refine ⟨232114707913001814421103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 618972554434671505122941 232114707913001814421103)
                  ·
                    rfl

theorem cell20_508547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 3].length) (baseStart_508547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508547 prefixEnd_508547 := by exact prefixLift 508547
  have htrace : WordTrace (prefixWord ++ tailWord_508547) baseStart_508547 baseEnd_508547 := by
    simpa [prefixWord, tailWord_508547, baseEnd_508547] using wordTrace_append hprefix tailTrace_508547
  have hstable : (prefixWord ++ tailWord_508547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508547).length < 2 ^ (prefixWord ++ tailWord_508547).sum := by decide
  have hdescent : baseEnd_508547 < baseStart_508547 := by decide
  rcases family_descends (prefixWord ++ tailWord_508547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508626 : List Nat := [3, 2, 2, 2, 3, 1, 2, 3, 2]
def baseStart_508626 : Nat := 118140960795 + 508626 * 2 ^ 59
def prefixEnd_508626 : Nat := 4983230072969 + 3 ^ 40 * 508626 * 2
def baseEnd_508626 : Nat := 232150765665628650787447

theorem tailTrace_508626 : CollatzResearch.WordTrace tailWord_508626 prefixEnd_508626 232150765665628650787447 := by
  unfold tailWord_508626
  simp only [CollatzResearch.WordTrace]
  refine ⟨4637778563835585812530433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12367409503561562166747821 4637778563835585812530433)
  ·
    refine ⟨3478333922876689359397825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4637778563835585812530433 3478333922876689359397825)
    ·
      refine ⟨2608750442157517019548369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3478333922876689359397825 2608750442157517019548369)
      ·
        refine ⟨1956562831618137764661277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2608750442157517019548369 1956562831618137764661277)
        ·
          refine ⟨733711061856801661747979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1956562831618137764661277 733711061856801661747979)
          ·
            refine ⟨1100566592785202492621969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733711061856801661747979 1100566592785202492621969)
            ·
              refine ⟨825424944588901869466477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1100566592785202492621969 825424944588901869466477)
              ·
                refine ⟨309534354220838201049929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 825424944588901869466477 309534354220838201049929)
                ·
                  refine ⟨232150765665628650787447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309534354220838201049929 232150765665628650787447)
                  ·
                    rfl

theorem cell20_508626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_508626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508626 prefixEnd_508626 := by exact prefixLift 508626
  have htrace : WordTrace (prefixWord ++ tailWord_508626) baseStart_508626 baseEnd_508626 := by
    simpa [prefixWord, tailWord_508626, baseEnd_508626] using wordTrace_append hprefix tailTrace_508626
  have hstable : (prefixWord ++ tailWord_508626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508626).length < 2 ^ (prefixWord ++ tailWord_508626).sum := by decide
  have hdescent : baseEnd_508626 < baseStart_508626 := by decide
  rcases family_descends (prefixWord ++ tailWord_508626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508644 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 5]
def baseStart_508644 : Nat := 118140960795 + 508644 * 2 ^ 59
def prefixEnd_508644 : Nat := 4983230072969 + 3 ^ 40 * 508644 * 2
def baseEnd_508644 : Nat := 232158981356100588187373

theorem tailTrace_508644 : CollatzResearch.WordTrace tailWord_508644 prefixEnd_508644 232158981356100588187373 := by
  unfold tailWord_508644
  simp only [CollatzResearch.WordTrace]
  refine ⟨9275885384638566162138493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12367847179518088216184657 9275885384638566162138493)
  ·
    refine ⟨3478457019239462310801935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9275885384638566162138493 3478457019239462310801935)
    ·
      refine ⟨5217685528859193466202903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3478457019239462310801935 5217685528859193466202903)
      ·
        refine ⟨7826528293288790199304355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5217685528859193466202903 7826528293288790199304355)
        ·
          refine ⟨11739792439933185298956533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7826528293288790199304355 11739792439933185298956533)
          ·
            refine ⟨1100605541243736121777175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11739792439933185298956533 1100605541243736121777175)
            ·
              refine ⟨1650908311865604182665763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100605541243736121777175 1650908311865604182665763)
              ·
                refine ⟨2476362467798406273998645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650908311865604182665763 2476362467798406273998645)
                ·
                  refine ⟨232158981356100588187373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2476362467798406273998645 232158981356100588187373)
                  ·
                    rfl

theorem cell20_508644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_508644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508644 prefixEnd_508644 := by exact prefixLift 508644
  have htrace : WordTrace (prefixWord ++ tailWord_508644) baseStart_508644 baseEnd_508644 := by
    simpa [prefixWord, tailWord_508644, baseEnd_508644] using wordTrace_append hprefix tailTrace_508644
  have hstable : (prefixWord ++ tailWord_508644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508644).length < 2 ^ (prefixWord ++ tailWord_508644).sum := by decide
  have hdescent : baseEnd_508644 < baseStart_508644 := by decide
  rcases family_descends (prefixWord ++ tailWord_508644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508706 : List Nat := [3, 3, 1, 1, 2, 2, 3, 1, 4]
def baseStart_508706 : Nat := 118140960795 + 508706 * 2 ^ 59
def prefixEnd_508706 : Nat := 4983230072969 + 3 ^ 40 * 508706 * 2
def baseEnd_508706 : Nat := 232187279845503928120453

theorem tailTrace_508706 : CollatzResearch.WordTrace tailWord_508706 prefixEnd_508706 232187279845503928120453 := by
  unfold tailWord_508706
  simp only [CollatzResearch.WordTrace]
  refine ⟨4638508023763129228258493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12369354730035011275355981 4638508023763129228258493)
  ·
    refine ⟨1739440508911173460596935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4638508023763129228258493 1739440508911173460596935)
    ·
      refine ⟨2609160763366760190895403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1739440508911173460596935 2609160763366760190895403)
      ·
        refine ⟨3913741145050140286343105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2609160763366760190895403 3913741145050140286343105)
        ·
          refine ⟨2935305858787605214757329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3913741145050140286343105 2935305858787605214757329)
          ·
            refine ⟨2201479394090703911067997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2935305858787605214757329 2201479394090703911067997)
            ·
              refine ⟨825554772784013966650499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2201479394090703911067997 825554772784013966650499)
              ·
                refine ⟨1238332159176020949975749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825554772784013966650499 1238332159176020949975749)
                ·
                  refine ⟨232187279845503928120453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1238332159176020949975749 232187279845503928120453)
                  ·
                    rfl

theorem cell20_508706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_508706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508706 prefixEnd_508706 := by exact prefixLift 508706
  have htrace : WordTrace (prefixWord ++ tailWord_508706) baseStart_508706 baseEnd_508706 := by
    simpa [prefixWord, tailWord_508706, baseEnd_508706] using wordTrace_append hprefix tailTrace_508706
  have hstable : (prefixWord ++ tailWord_508706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508706).length < 2 ^ (prefixWord ++ tailWord_508706).sum := by decide
  have hdescent : baseEnd_508706 < baseStart_508706 := by decide
  rcases family_descends (prefixWord ++ tailWord_508706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508741 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 5]
def baseStart_508741 : Nat := 118140960795 + 508741 * 2 ^ 59
def prefixEnd_508741 : Nat := 4983230072969 + 3 ^ 40 * 508741 * 2
def baseEnd_508741 : Nat := 232203254799199361953643

theorem tailTrace_508741 : CollatzResearch.WordTrace tailWord_508741 prefixEnd_508741 232203254799199361953643 := by
  unfold tailWord_508741
  simp only [CollatzResearch.WordTrace]
  refine ⟨18555308649925717890558077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12370205766617145260372051 18555308649925717890558077)
  ·
    refine ⟨6958240743722144208959279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18555308649925717890558077 6958240743722144208959279)
    ·
      refine ⟨10437361115583216313438919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6958240743722144208959279 10437361115583216313438919)
      ·
        refine ⟨15656041673374824470158379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10437361115583216313438919 15656041673374824470158379)
        ·
          refine ⟨23484062510062236705237569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15656041673374824470158379 23484062510062236705237569)
          ·
            refine ⟨17613046882546677528928177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23484062510062236705237569 17613046882546677528928177)
            ·
              refine ⟨13209785161910008146696133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17613046882546677528928177 13209785161910008146696133)
              ·
                refine ⟨2476834717858126527505525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13209785161910008146696133 2476834717858126527505525)
                ·
                  refine ⟨232203254799199361953643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2476834717858126527505525 232203254799199361953643)
                  ·
                    rfl

theorem cell20_508741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_508741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508741 prefixEnd_508741 := by exact prefixLift 508741
  have htrace : WordTrace (prefixWord ++ tailWord_508741) baseStart_508741 baseEnd_508741 := by
    simpa [prefixWord, tailWord_508741, baseEnd_508741] using wordTrace_append hprefix tailTrace_508741
  have hstable : (prefixWord ++ tailWord_508741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508741).length < 2 ^ (prefixWord ++ tailWord_508741).sum := by decide
  have hdescent : baseEnd_508741 < baseStart_508741 := by decide
  rcases family_descends (prefixWord ++ tailWord_508741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508744 : List Nat := [2, 1, 3, 1, 1, 3, 2, 5, 2]
def baseStart_508744 : Nat := 118140960795 + 508744 * 2 ^ 59
def prefixEnd_508744 : Nat := 4983230072969 + 3 ^ 40 * 508744 * 2
def baseEnd_508744 : Nat := 232204624080944684853631

theorem tailTrace_508744 : CollatzResearch.WordTrace tailWord_508744 prefixEnd_508744 232204624080944684853631 := by
  unfold tailWord_508744
  simp only [CollatzResearch.WordTrace]
  refine ⟨9277709034457424701458643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12370278712609899601944857 9277709034457424701458643)
  ·
    refine ⟨13916563551686137052187965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9277709034457424701458643 13916563551686137052187965)
    ·
      refine ⟨5218711331882301394570487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13916563551686137052187965 5218711331882301394570487)
      ·
        refine ⟨7828066997823452091855731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5218711331882301394570487 7828066997823452091855731)
        ·
          refine ⟨11742100496735178137783597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7828066997823452091855731 11742100496735178137783597)
          ·
            refine ⟨4403287686275691801668849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11742100496735178137783597 4403287686275691801668849)
            ·
              refine ⟨3302465764706768851251637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4403287686275691801668849 3302465764706768851251637)
              ·
                refine ⟨309606165441259579804841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3302465764706768851251637 309606165441259579804841)
                ·
                  refine ⟨232204624080944684853631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309606165441259579804841 232204624080944684853631)
                  ·
                    rfl

theorem cell20_508744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 5, 2].length) (baseStart_508744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508744 prefixEnd_508744 := by exact prefixLift 508744
  have htrace : WordTrace (prefixWord ++ tailWord_508744) baseStart_508744 baseEnd_508744 := by
    simpa [prefixWord, tailWord_508744, baseEnd_508744] using wordTrace_append hprefix tailTrace_508744
  have hstable : (prefixWord ++ tailWord_508744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508744).length < 2 ^ (prefixWord ++ tailWord_508744).sum := by decide
  have hdescent : baseEnd_508744 < baseStart_508744 := by decide
  rcases family_descends (prefixWord ++ tailWord_508744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508761 : List Nat := [1, 2, 1, 2, 2, 4, 4, 2, 2]
def baseStart_508761 : Nat := 118140960795 + 508761 * 2 ^ 59
def prefixEnd_508761 : Nat := 4983230072969 + 3 ^ 40 * 508761 * 2
def baseEnd_508761 : Nat := 232212383344168181286895

theorem tailTrace_508761 : CollatzResearch.WordTrace tailWord_508761 prefixEnd_508761 232212383344168181286895 := by
  unfold tailWord_508761
  simp only [CollatzResearch.WordTrace]
  refine ⟨18556038109853261306286137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12370692073235507537524091 18556038109853261306286137)
  ·
    refine ⟨13917028582389945979714603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18556038109853261306286137 13917028582389945979714603)
    ·
      refine ⟨20875542873584918969571905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13917028582389945979714603 20875542873584918969571905)
      ·
        refine ⟨15656657155188689227178929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20875542873584918969571905 15656657155188689227178929)
        ·
          refine ⟨11742492866391516920384197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15656657155188689227178929 11742492866391516920384197)
          ·
            refine ⟨2201717412448409422572037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11742492866391516920384197 2201717412448409422572037)
            ·
              refine ⟨412822014834076766732257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2201717412448409422572037 412822014834076766732257)
              ·
                refine ⟨309616511125557575049193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412822014834076766732257 309616511125557575049193)
                ·
                  refine ⟨232212383344168181286895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309616511125557575049193 232212383344168181286895)
                  ·
                    rfl

theorem cell20_508761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 2, 2].length) (baseStart_508761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508761 prefixEnd_508761 := by exact prefixLift 508761
  have htrace : WordTrace (prefixWord ++ tailWord_508761) baseStart_508761 baseEnd_508761 := by
    simpa [prefixWord, tailWord_508761, baseEnd_508761] using wordTrace_append hprefix tailTrace_508761
  have hstable : (prefixWord ++ tailWord_508761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508761).length < 2 ^ (prefixWord ++ tailWord_508761).sum := by decide
  have hdescent : baseEnd_508761 < baseStart_508761 := by decide
  rcases family_descends (prefixWord ++ tailWord_508761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508820 : List Nat := [2, 4, 2, 1, 1, 1, 4, 1, 4]
def baseStart_508820 : Nat := 118140960795 + 508820 * 2 ^ 59
def prefixEnd_508820 : Nat := 4983230072969 + 3 ^ 40 * 508820 * 2
def baseEnd_508820 : Nat := 232239312551826198319987

theorem tailTrace_508820 : CollatzResearch.WordTrace tailWord_508820 prefixEnd_508820 232239312551826198319987 := by
  unfold tailWord_508820
  simp only [CollatzResearch.WordTrace]
  refine ⟨9279095008319757191341957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12372126677759676255122609 9279095008319757191341957)
  ·
    refine ⟨1739830314059954473376617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9279095008319757191341957 1739830314059954473376617)
    ·
      refine ⟨1304872735544965855032463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1739830314059954473376617 1304872735544965855032463)
      ·
        refine ⟨1957309103317448782548695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1304872735544965855032463 1957309103317448782548695)
        ·
          refine ⟨2935963654976173173823043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1957309103317448782548695 2935963654976173173823043)
          ·
            refine ⟨4403945482464259760734565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2935963654976173173823043 4403945482464259760734565)
            ·
              refine ⟨825739777962048705137731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4403945482464259760734565 825739777962048705137731)
              ·
                refine ⟨1238609666943073057706597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825739777962048705137731 1238609666943073057706597)
                ·
                  refine ⟨232239312551826198319987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1238609666943073057706597 232239312551826198319987)
                  ·
                    rfl

theorem cell20_508820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_508820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508820 prefixEnd_508820 := by exact prefixLift 508820
  have htrace : WordTrace (prefixWord ++ tailWord_508820) baseStart_508820 baseEnd_508820 := by
    simpa [prefixWord, tailWord_508820, baseEnd_508820] using wordTrace_append hprefix tailTrace_508820
  have hstable : (prefixWord ++ tailWord_508820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508820).length < 2 ^ (prefixWord ++ tailWord_508820).sum := by decide
  have hdescent : baseEnd_508820 < baseStart_508820 := by decide
  rcases family_descends (prefixWord ++ tailWord_508820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508855 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 5]
def baseStart_508855 : Nat := 118140960795 + 508855 * 2 ^ 59
def prefixEnd_508855 : Nat := 4983230072969 + 3 ^ 40 * 508855 * 2
def baseEnd_508855 : Nat := 232255287505521632153177

theorem tailTrace_508855 : CollatzResearch.WordTrace tailWord_508855 prefixEnd_508855 232255287505521632153177 := by
  unfold tailWord_508855
  simp only [CollatzResearch.WordTrace]
  refine ⟨18559466571512715360208019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12372977714341810240138679 18559466571512715360208019)
  ·
    refine ⟨27839199857269073040312029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18559466571512715360208019 27839199857269073040312029)
    ·
      refine ⟨10439699946475902390117011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27839199857269073040312029 10439699946475902390117011)
      ·
        refine ⟨15659549919713853585175517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10439699946475902390117011 15659549919713853585175517)
        ·
          refine ⟨5872331219892695094440819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15659549919713853585175517 5872331219892695094440819)
          ·
            refine ⟨8808496829839042641661229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5872331219892695094440819 8808496829839042641661229)
            ·
              refine ⟨3303186311189640990622961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8808496829839042641661229 3303186311189640990622961)
              ·
                refine ⟨2477389733392230742967221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3303186311189640990622961 2477389733392230742967221)
                ·
                  refine ⟨232255287505521632153177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2477389733392230742967221 232255287505521632153177)
                  ·
                    rfl

theorem cell20_508855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_508855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508855 prefixEnd_508855 := by exact prefixLift 508855
  have htrace : WordTrace (prefixWord ++ tailWord_508855) baseStart_508855 baseEnd_508855 := by
    simpa [prefixWord, tailWord_508855, baseEnd_508855] using wordTrace_append hprefix tailTrace_508855
  have hstable : (prefixWord ++ tailWord_508855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508855).length < 2 ^ (prefixWord ++ tailWord_508855).sum := by decide
  have hdescent : baseEnd_508855 < baseStart_508855 := by decide
  rcases family_descends (prefixWord ++ tailWord_508855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508875 : List Nat := [1, 1, 1, 1, 3, 6, 3, 2, 2]
def baseStart_508875 : Nat := 118140960795 + 508875 * 2 ^ 59
def prefixEnd_508875 : Nat := 4983230072969 + 3 ^ 40 * 508875 * 2
def baseEnd_508875 : Nat := 232264416050490451486429

theorem tailTrace_508875 : CollatzResearch.WordTrace tailWord_508875 prefixEnd_508875 232264416050490451486429 := by
  unfold tailWord_508875
  simp only [CollatzResearch.WordTrace]
  refine ⟨18560196031440258775936079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12373464020960172517290719 18560196031440258775936079)
  ·
    refine ⟨27840294047160388163904119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18560196031440258775936079 27840294047160388163904119)
    ·
      refine ⟨41760441070740582245856179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27840294047160388163904119 41760441070740582245856179)
      ·
        refine ⟨62640661606110873368784269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41760441070740582245856179 62640661606110873368784269)
        ·
          refine ⟨23490248102291577513294101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62640661606110873368784269 23490248102291577513294101)
          ·
            refine ⟨1101105379794917695935661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23490248102291577513294101 1101105379794917695935661)
            ·
              refine ⟨412914517423094135975873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1101105379794917695935661 412914517423094135975873)
              ·
                refine ⟨309685888067320601981905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412914517423094135975873 309685888067320601981905)
                ·
                  refine ⟨232264416050490451486429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309685888067320601981905 232264416050490451486429)
                  ·
                    rfl

theorem cell20_508875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 2].length) (baseStart_508875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508875 prefixEnd_508875 := by exact prefixLift 508875
  have htrace : WordTrace (prefixWord ++ tailWord_508875) baseStart_508875 baseEnd_508875 := by
    simpa [prefixWord, tailWord_508875, baseEnd_508875] using wordTrace_append hprefix tailTrace_508875
  have hstable : (prefixWord ++ tailWord_508875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508875).length < 2 ^ (prefixWord ++ tailWord_508875).sum := by decide
  have hdescent : baseEnd_508875 < baseStart_508875 := by decide
  rcases family_descends (prefixWord ++ tailWord_508875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508879 : List Nat := [1, 1, 2, 1, 1, 6, 3, 1, 4]
def baseStart_508879 : Nat := 118140960795 + 508879 * 2 ^ 59
def prefixEnd_508879 : Nat := 4983230072969 + 3 ^ 40 * 508879 * 2
def baseEnd_508879 : Nat := 232266241759484215353079

theorem tailTrace_508879 : CollatzResearch.WordTrace tailWord_508879 prefixEnd_508879 232266241759484215353079 := by
  unfold tailWord_508879
  simp only [CollatzResearch.WordTrace]
  refine ⟨18560341923425767459081691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12373561282283844972721127 18560341923425767459081691)
  ·
    refine ⟨27840512885138651188622537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18560341923425767459081691 27840512885138651188622537)
    ·
      refine ⟨20880384663853988391466903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27840512885138651188622537 20880384663853988391466903)
      ·
        refine ⟨31320576995780982587200355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20880384663853988391466903 31320576995780982587200355)
        ·
          refine ⟨46980865493671473880800533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31320576995780982587200355 46980865493671473880800533)
          ·
            refine ⟨2202228070015850338162525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46980865493671473880800533 2202228070015850338162525)
            ·
              refine ⟨825835526255943876810947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2202228070015850338162525 825835526255943876810947)
              ·
                refine ⟨1238753289383915815216421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 825835526255943876810947 1238753289383915815216421)
                ·
                  refine ⟨232266241759484215353079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1238753289383915815216421 232266241759484215353079)
                  ·
                    rfl

theorem cell20_508879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 4].length) (baseStart_508879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508879 prefixEnd_508879 := by exact prefixLift 508879
  have htrace : WordTrace (prefixWord ++ tailWord_508879) baseStart_508879 baseEnd_508879 := by
    simpa [prefixWord, tailWord_508879, baseEnd_508879] using wordTrace_append hprefix tailTrace_508879
  have hstable : (prefixWord ++ tailWord_508879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508879).length < 2 ^ (prefixWord ++ tailWord_508879).sum := by decide
  have hdescent : baseEnd_508879 < baseStart_508879 := by decide
  rcases family_descends (prefixWord ++ tailWord_508879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508885 : List Nat := [1, 3, 2, 3, 4, 1, 2, 1, 3]
def baseStart_508885 : Nat := 118140960795 + 508885 * 2 ^ 59
def prefixEnd_508885 : Nat := 4983230072969 + 3 ^ 40 * 508885 * 2
def baseEnd_508885 : Nat := 232268980322974861153055

theorem tailTrace_508885 : CollatzResearch.WordTrace tailWord_508885 prefixEnd_508885 232268980322974861153055 := by
  unfold tailWord_508885
  simp only [CollatzResearch.WordTrace]
  refine ⟨18560560761404030483800109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12373707174269353655866739 18560560761404030483800109)
  ·
    refine ⟨6960210285526511431425041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18560560761404030483800109 6960210285526511431425041)
    ·
      refine ⟨5220157714144883573568781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6960210285526511431425041 5220157714144883573568781)
      ·
        refine ⟨1957559142804331340088293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5220157714144883573568781 1957559142804331340088293)
        ·
          refine ⟨367042339275812126266555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1957559142804331340088293 367042339275812126266555)
          ·
            refine ⟨550563508913718189399833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367042339275812126266555 550563508913718189399833)
            ·
              refine ⟨412922631685288642049875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550563508913718189399833 412922631685288642049875)
              ·
                refine ⟨619383947527932963074813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412922631685288642049875 619383947527932963074813)
                ·
                  refine ⟨232268980322974861153055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 619383947527932963074813 232268980322974861153055)
                  ·
                    rfl

theorem cell20_508885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_508885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508885 prefixEnd_508885 := by exact prefixLift 508885
  have htrace : WordTrace (prefixWord ++ tailWord_508885) baseStart_508885 baseEnd_508885 := by
    simpa [prefixWord, tailWord_508885, baseEnd_508885] using wordTrace_append hprefix tailTrace_508885
  have hstable : (prefixWord ++ tailWord_508885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508885).length < 2 ^ (prefixWord ++ tailWord_508885).sum := by decide
  have hdescent : baseEnd_508885 < baseStart_508885 := by decide
  rcases family_descends (prefixWord ++ tailWord_508885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508889 : List Nat := [1, 2, 1, 2, 5, 1, 4, 1, 3]
def baseStart_508889 : Nat := 118140960795 + 508889 * 2 ^ 59
def prefixEnd_508889 : Nat := 4983230072969 + 3 ^ 40 * 508889 * 2
def baseEnd_508889 : Nat := 232270806031968625019705

theorem tailTrace_508889 : CollatzResearch.WordTrace tailWord_508889 prefixEnd_508889 232270806031968625019705 := by
  unfold tailWord_508889
  simp only [CollatzResearch.WordTrace]
  refine ⟨18560706653389539166945721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12373804435593026111297147 18560706653389539166945721)
  ·
    refine ⟨13920529990042154375209291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18560706653389539166945721 13920529990042154375209291)
    ·
      refine ⟨20880794985063231562813937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13920529990042154375209291 20880794985063231562813937)
      ·
        refine ⟨15660596238797423672110453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20880794985063231562813937 15660596238797423672110453)
        ·
          refine ⟨1468180897387258469260355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15660596238797423672110453 1468180897387258469260355)
          ·
            refine ⟨2202271346080887703890533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468180897387258469260355 2202271346080887703890533)
            ·
              refine ⟨412925877390166444479475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2202271346080887703890533 412925877390166444479475)
              ·
                refine ⟨619388816085249666719213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412925877390166444479475 619388816085249666719213)
                ·
                  refine ⟨232270806031968625019705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 619388816085249666719213 232270806031968625019705)
                  ·
                    rfl

theorem cell20_508889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 3].length) (baseStart_508889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508889 prefixEnd_508889 := by exact prefixLift 508889
  have htrace : WordTrace (prefixWord ++ tailWord_508889) baseStart_508889 baseEnd_508889 := by
    simpa [prefixWord, tailWord_508889, baseEnd_508889] using wordTrace_append hprefix tailTrace_508889
  have hstable : (prefixWord ++ tailWord_508889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508889).length < 2 ^ (prefixWord ++ tailWord_508889).sum := by decide
  have hdescent : baseEnd_508889 < baseStart_508889 := by decide
  rcases family_descends (prefixWord ++ tailWord_508889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508916 : List Nat := [2, 6, 2, 1, 2, 7]
def baseStart_508916 : Nat := 118140960795 + 508916 * 2 ^ 59
def prefixEnd_508916 : Nat := 4983230072969 + 3 ^ 40 * 508916 * 2
def baseEnd_508916 : Nat := 8603078872876908559985

theorem tailTrace_508916 : CollatzResearch.WordTrace tailWord_508916 prefixEnd_508916 8603078872876908559985 := by
  unfold tailWord_508916
  simp only [CollatzResearch.WordTrace]
  refine ⟨9280845712145861389089301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12374460949527815185452401 9280845712145861389089301)
  ·
    refine ⟨435039642756837252613561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9280845712145861389089301 435039642756837252613561)
    ·
      refine ⟨326279732067627939460171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 435039642756837252613561 326279732067627939460171)
      ·
        refine ⟨489419598101441909190257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326279732067627939460171 489419598101441909190257)
        ·
          refine ⟨367064698576081431892693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 489419598101441909190257 367064698576081431892693)
          ·
            refine ⟨8603078872876908559985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 367064698576081431892693 8603078872876908559985)
            ·
              rfl

theorem cell20_508916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 7].length) (baseStart_508916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508916 prefixEnd_508916 := by exact prefixLift 508916
  have htrace : WordTrace (prefixWord ++ tailWord_508916) baseStart_508916 baseEnd_508916 := by
    simpa [prefixWord, tailWord_508916, baseEnd_508916] using wordTrace_append hprefix tailTrace_508916
  have hstable : (prefixWord ++ tailWord_508916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508916).length < 2 ^ (prefixWord ++ tailWord_508916).sum := by decide
  have hdescent : baseEnd_508916 < baseStart_508916 := by decide
  rcases family_descends (prefixWord ++ tailWord_508916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508926 : List Nat := [4, 2, 2, 2, 3, 1, 2, 2, 2]
def baseStart_508926 : Nat := 118140960795 + 508926 * 2 ^ 59
def prefixEnd_508926 : Nat := 4983230072969 + 3 ^ 40 * 508926 * 2
def baseEnd_508926 : Nat := 232287693840160940786221

theorem tailTrace_508926 : CollatzResearch.WordTrace tailWord_508926 prefixEnd_508926 232287693840160940786221 := by
  unfold tailWord_508926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2320257019281936810755329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12374704102836996324028421 2320257019281936810755329)
  ·
    refine ⟨1740192764461452608066497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2320257019281936810755329 1740192764461452608066497)
    ·
      refine ⟨1305144573346089456049873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1740192764461452608066497 1305144573346089456049873)
      ·
        refine ⟨978858430009567092037405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1305144573346089456049873 978858430009567092037405)
        ·
          refine ⟨367071911253587659514027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 978858430009567092037405 367071911253587659514027)
          ·
            refine ⟨550607866880381489271041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367071911253587659514027 550607866880381489271041)
            ·
              refine ⟨412955900160286116953281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 550607866880381489271041 412955900160286116953281)
              ·
                refine ⟨309716925120214587714961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 412955900160286116953281 309716925120214587714961)
                ·
                  refine ⟨232287693840160940786221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309716925120214587714961 232287693840160940786221)
                  ·
                    rfl

theorem cell20_508926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_508926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508926 prefixEnd_508926 := by exact prefixLift 508926
  have htrace : WordTrace (prefixWord ++ tailWord_508926) baseStart_508926 baseEnd_508926 := by
    simpa [prefixWord, tailWord_508926, baseEnd_508926] using wordTrace_append hprefix tailTrace_508926
  have hstable : (prefixWord ++ tailWord_508926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508926).length < 2 ^ (prefixWord ++ tailWord_508926).sum := by decide
  have hdescent : baseEnd_508926 < baseStart_508926 := by decide
  rcases family_descends (prefixWord ++ tailWord_508926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508972 : List Nat := [2, 2, 1, 1, 1, 2, 6, 3, 2]
def baseStart_508972 : Nat := 118140960795 + 508972 * 2 ^ 59
def prefixEnd_508972 : Nat := 4983230072969 + 3 ^ 40 * 508972 * 2
def baseEnd_508972 : Nat := 232308689493589225252699

theorem tailTrace_508972 : CollatzResearch.WordTrace tailWord_508972 prefixEnd_508972 232308689493589225252699 := by
  unfold tailWord_508972
  simp only [CollatzResearch.WordTrace]
  refine ⟨9281866956044422171108585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12375822608059229561478113 9281866956044422171108585)
  ·
    refine ⟨6961400217033316628331439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9281866956044422171108585 6961400217033316628331439)
    ·
      refine ⟨10442100325549974942497159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6961400217033316628331439 10442100325549974942497159)
      ·
        refine ⟨15663150488324962413745739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10442100325549974942497159 15663150488324962413745739)
        ·
          refine ⟨23494725732487443620618609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15663150488324962413745739 23494725732487443620618609)
          ·
            refine ⟨17621044299365582715463957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23494725732487443620618609 17621044299365582715463957)
            ·
              refine ⟨825986451532761689787373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17621044299365582715463957 825986451532761689787373)
              ·
                refine ⟨309744919324785633670265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 825986451532761689787373 309744919324785633670265)
                ·
                  refine ⟨232308689493589225252699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309744919324785633670265 232308689493589225252699)
                  ·
                    rfl

theorem cell20_508972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_508972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508972 prefixEnd_508972 := by exact prefixLift 508972
  have htrace : WordTrace (prefixWord ++ tailWord_508972) baseStart_508972 baseEnd_508972 := by
    simpa [prefixWord, tailWord_508972, baseEnd_508972] using wordTrace_append hprefix tailTrace_508972
  have hstable : (prefixWord ++ tailWord_508972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508972).length < 2 ^ (prefixWord ++ tailWord_508972).sum := by decide
  have hdescent : baseEnd_508972 < baseStart_508972 := by decide
  rcases family_descends (prefixWord ++ tailWord_508972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508976 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 6]
def baseStart_508976 : Nat := 118140960795 + 508976 * 2 ^ 59
def prefixEnd_508976 : Nat := 4983230072969 + 3 ^ 40 * 508976 * 2
def baseEnd_508976 : Nat := 232310515202582989119349

theorem tailTrace_508976 : CollatzResearch.WordTrace tailWord_508976 prefixEnd_508976 232310515202582989119349 := by
  unfold tailWord_508976
  simp only [CollatzResearch.WordTrace]
  refine ⟨9281939902037176512681391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12375919869382902016908521 9281939902037176512681391)
  ·
    refine ⟨13922909853055764769022087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9281939902037176512681391 13922909853055764769022087)
    ·
      refine ⟨20884364779583647153533131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13922909853055764769022087 20884364779583647153533131)
      ·
        refine ⟨31326547169375470730299697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20884364779583647153533131 31326547169375470730299697)
        ·
          refine ⟨23494910377031603047724773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31326547169375470730299697 23494910377031603047724773)
          ·
            refine ⟨4405295695693425571448395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23494910377031603047724773 4405295695693425571448395)
            ·
              refine ⟨6607943543540138357172593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4405295695693425571448395 6607943543540138357172593)
              ·
                refine ⟨4955957657655103767879445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6607943543540138357172593 4955957657655103767879445)
                ·
                  refine ⟨232310515202582989119349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4955957657655103767879445 232310515202582989119349)
                  ·
                    rfl

theorem cell20_508976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_508976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508976 prefixEnd_508976 := by exact prefixLift 508976
  have htrace : WordTrace (prefixWord ++ tailWord_508976) baseStart_508976 baseEnd_508976 := by
    simpa [prefixWord, tailWord_508976, baseEnd_508976] using wordTrace_append hprefix tailTrace_508976
  have hstable : (prefixWord ++ tailWord_508976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508976).length < 2 ^ (prefixWord ++ tailWord_508976).sum := by decide
  have hdescent : baseEnd_508976 < baseStart_508976 := by decide
  rcases family_descends (prefixWord ++ tailWord_508976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508982 : List Nat := [5, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_508982 : Nat := 118140960795 + 508982 * 2 ^ 59
def prefixEnd_508982 : Nat := 4983230072969 + 3 ^ 40 * 508982 * 2
def baseEnd_508982 : Nat := 232313253766073634919325

theorem tailTrace_508982 : CollatzResearch.WordTrace tailWord_508982 prefixEnd_508982 232313253766073634919325 := by
  unfold tailWord_508982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1160256165128288503130075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12376065761368410700054133 1160256165128288503130075)
  ·
    refine ⟨1740384247692432754695113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1160256165128288503130075 1740384247692432754695113)
    ·
      refine ⟨1305288185769324566021335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1740384247692432754695113 1305288185769324566021335)
      ·
        refine ⟨1957932278653986849032003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1305288185769324566021335 1957932278653986849032003)
        ·
          refine ⟨2936898417980980273548005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1957932278653986849032003 2936898417980980273548005)
          ·
            refine ⟨550668453371433801290251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2936898417980980273548005 550668453371433801290251)
            ·
              refine ⟨826002680057150701935377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550668453371433801290251 826002680057150701935377)
              ·
                refine ⟨619502010042863026451533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826002680057150701935377 619502010042863026451533)
                ·
                  refine ⟨232313253766073634919325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 619502010042863026451533 232313253766073634919325)
                  ·
                    rfl

theorem cell20_508982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_508982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508982 prefixEnd_508982 := by exact prefixLift 508982
  have htrace : WordTrace (prefixWord ++ tailWord_508982) baseStart_508982 baseEnd_508982 := by
    simpa [prefixWord, tailWord_508982, baseEnd_508982] using wordTrace_append hprefix tailTrace_508982
  have hstable : (prefixWord ++ tailWord_508982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508982).length < 2 ^ (prefixWord ++ tailWord_508982).sum := by decide
  have hdescent : baseEnd_508982 < baseStart_508982 := by decide
  rcases family_descends (prefixWord ++ tailWord_508982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_508986 : List Nat := [3, 1, 1, 1, 3, 1, 5, 2, 3]
def baseStart_508986 : Nat := 118140960795 + 508986 * 2 ^ 59
def prefixEnd_508986 : Nat := 4983230072969 + 3 ^ 40 * 508986 * 2
def baseEnd_508986 : Nat := 232315079475067398785975

theorem tailTrace_508986 : CollatzResearch.WordTrace tailWord_508986 prefixEnd_508986 232315079475067398785975 := by
  unfold tailWord_508986
  simp only [CollatzResearch.WordTrace]
  refine ⟨4641061133509531183306703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12376163022692083155484541 4641061133509531183306703)
  ·
    refine ⟨6961591700264296774960055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4641061133509531183306703 6961591700264296774960055)
    ·
      refine ⟨10442387550396445162440083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6961591700264296774960055 10442387550396445162440083)
      ·
        refine ⟨15663581325594667743660125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10442387550396445162440083 15663581325594667743660125)
        ·
          refine ⟨5873842997098000403872547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15663581325594667743660125 5873842997098000403872547)
          ·
            refine ⟨8810764495647000605808821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5873842997098000403872547 8810764495647000605808821)
            ·
              refine ⟨826009171466906306794577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8810764495647000605808821 826009171466906306794577)
              ·
                refine ⟨619506878600179730095933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826009171466906306794577 619506878600179730095933)
                ·
                  refine ⟨232315079475067398785975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 619506878600179730095933 232315079475067398785975)
                  ·
                    rfl

theorem cell20_508986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_508986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_508986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_508986 prefixEnd_508986 := by exact prefixLift 508986
  have htrace : WordTrace (prefixWord ++ tailWord_508986) baseStart_508986 baseEnd_508986 := by
    simpa [prefixWord, tailWord_508986, baseEnd_508986] using wordTrace_append hprefix tailTrace_508986
  have hstable : (prefixWord ++ tailWord_508986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_508986).length < 2 ^ (prefixWord ++ tailWord_508986).sum := by decide
  have hdescent : baseEnd_508986 < baseStart_508986 := by decide
  rcases family_descends (prefixWord ++ tailWord_508986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509038 : List Nat := [4, 1, 2, 2, 1, 2, 8]
def baseStart_509038 : Nat := 118140960795 + 509038 * 2 ^ 59
def prefixEnd_509038 : Nat := 4983230072969 + 3 ^ 40 * 509038 * 2
def baseEnd_509038 : Nat := 25815423743554036561381

theorem tailTrace_509038 : CollatzResearch.WordTrace tailWord_509038 prefixEnd_509038 25815423743554036561381 := by
  unfold tailWord_509038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2320767641231217201764971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12377427419899825076079845 2320767641231217201764971)
  ·
    refine ⟨3481151461846825802647457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2320767641231217201764971 3481151461846825802647457)
    ·
      refine ⟨2610863596385119351985593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3481151461846825802647457 2610863596385119351985593)
      ·
        refine ⟨1958147697288839513989195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2610863596385119351985593 1958147697288839513989195)
        ·
          refine ⟨2937221545933259270983793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1958147697288839513989195 2937221545933259270983793)
          ·
            refine ⟨2202916159449944453237845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2937221545933259270983793 2202916159449944453237845)
            ·
              refine ⟨25815423743554036561381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2202916159449944453237845 25815423743554036561381)
              ·
                rfl

theorem cell20_509038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 8].length) (baseStart_509038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509038 prefixEnd_509038 := by exact prefixLift 509038
  have htrace : WordTrace (prefixWord ++ tailWord_509038) baseStart_509038 baseEnd_509038 := by
    simpa [prefixWord, tailWord_509038, baseEnd_509038] using wordTrace_append hprefix tailTrace_509038
  have hstable : (prefixWord ++ tailWord_509038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509038).length < 2 ^ (prefixWord ++ tailWord_509038).sum := by decide
  have hdescent : baseEnd_509038 < baseStart_509038 := by decide
  rcases family_descends (prefixWord ++ tailWord_509038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509124 : List Nat := [2, 3, 3, 1, 3, 1, 1, 2, 4]
def baseStart_509124 : Nat := 118140960795 + 509124 * 2 ^ 59
def prefixEnd_509124 : Nat := 4983230072969 + 3 ^ 40 * 509124 * 2
def baseEnd_509124 : Nat := 232378066435352252185411

theorem tailTrace_509124 : CollatzResearch.WordTrace tailWord_509124 prefixEnd_509124 232378066435352252185411 := by
  unfold tailWord_509124
  simp only [CollatzResearch.WordTrace]
  refine ⟨9284638903769087150875213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12379518538358782867833617 9284638903769087150875213)
  ·
    refine ⟨3481739588913407681578205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9284638903769087150875213 3481739588913407681578205)
    ·
      refine ⟨1305652345842527880591827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3481739588913407681578205 1305652345842527880591827)
      ·
        refine ⟨1958478518763791820887741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1305652345842527880591827 1958478518763791820887741)
        ·
          refine ⟨734429444536421932832903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1958478518763791820887741 734429444536421932832903)
          ·
            refine ⟨1101644166804632899249355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734429444536421932832903 1101644166804632899249355)
            ·
              refine ⟨1652466250206949348874033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1101644166804632899249355 1652466250206949348874033)
              ·
                refine ⟨1239349687655212011655525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1652466250206949348874033 1239349687655212011655525)
                ·
                  refine ⟨232378066435352252185411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1239349687655212011655525 232378066435352252185411)
                  ·
                    rfl

theorem cell20_509124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_509124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509124 prefixEnd_509124 := by exact prefixLift 509124
  have htrace : WordTrace (prefixWord ++ tailWord_509124) baseStart_509124 baseEnd_509124 := by
    simpa [prefixWord, tailWord_509124, baseEnd_509124] using wordTrace_append hprefix tailTrace_509124
  have hstable : (prefixWord ++ tailWord_509124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509124).length < 2 ^ (prefixWord ++ tailWord_509124).sum := by decide
  have hdescent : baseEnd_509124 < baseStart_509124 := by decide
  rcases family_descends (prefixWord ++ tailWord_509124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509128 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 6]
def baseStart_509128 : Nat := 118140960795 + 509128 * 2 ^ 59
def prefixEnd_509128 : Nat := 4983230072969 + 3 ^ 40 * 509128 * 2
def baseEnd_509128 : Nat := 232379892144346016052061

theorem tailTrace_509128 : CollatzResearch.WordTrace tailWord_509128 prefixEnd_509128 232379892144346016052061 := by
  unfold tailWord_509128
  simp only [CollatzResearch.WordTrace]
  refine ⟨9284711849761841492448019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12379615799682455323264025 9284711849761841492448019)
  ·
    refine ⟨13927067774642762238672029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9284711849761841492448019 13927067774642762238672029)
    ·
      refine ⟨5222650415491035839502011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13927067774642762238672029 5222650415491035839502011)
      ·
        refine ⟨7833975623236553759253017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5222650415491035839502011 7833975623236553759253017)
        ·
          refine ⟨5875481717427415319439763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7833975623236553759253017 5875481717427415319439763)
          ·
            refine ⟨8813222576141122979159645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5875481717427415319439763 8813222576141122979159645)
            ·
              refine ⟨3304958466052921117184867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8813222576141122979159645 3304958466052921117184867)
              ·
                refine ⟨4957437699079381675777301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3304958466052921117184867 4957437699079381675777301)
                ·
                  refine ⟨232379892144346016052061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4957437699079381675777301 232379892144346016052061)
                  ·
                    rfl

theorem cell20_509128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_509128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509128 prefixEnd_509128 := by exact prefixLift 509128
  have htrace : WordTrace (prefixWord ++ tailWord_509128) baseStart_509128 baseEnd_509128 := by
    simpa [prefixWord, tailWord_509128, baseEnd_509128] using wordTrace_append hprefix tailTrace_509128
  have hstable : (prefixWord ++ tailWord_509128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509128).length < 2 ^ (prefixWord ++ tailWord_509128).sum := by decide
  have hdescent : baseEnd_509128 < baseStart_509128 := by decide
  rcases family_descends (prefixWord ++ tailWord_509128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509141 : List Nat := [1, 3, 2, 4, 1, 2, 2, 3, 2]
def baseStart_509141 : Nat := 118140960795 + 509141 * 2 ^ 59
def prefixEnd_509141 : Nat := 4983230072969 + 3 ^ 40 * 509141 * 2
def baseEnd_509141 : Nat := 232385825698575748618675

theorem tailTrace_509141 : CollatzResearch.WordTrace tailWord_509141 prefixEnd_509141 232385825698575748618675 := by
  unfold tailWord_509141
  simp only [CollatzResearch.WordTrace]
  refine ⟨18569897848476586205119277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12379931898984390803412851 18569897848476586205119277)
  ·
    refine ⟨6963711693178719826919729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18569897848476586205119277 6963711693178719826919729)
    ·
      refine ⟨5222783769884039870189797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6963711693178719826919729 5222783769884039870189797)
      ·
        refine ⟨979271956853257475660587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5222783769884039870189797 979271956853257475660587)
        ·
          refine ⟨1468907935279886213490881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979271956853257475660587 1468907935279886213490881)
          ·
            refine ⟨1101680951459914660118161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1468907935279886213490881 1101680951459914660118161)
            ·
              refine ⟨826260713594935995088621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1101680951459914660118161 826260713594935995088621)
              ·
                refine ⟨309847767598100998158233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 826260713594935995088621 309847767598100998158233)
                ·
                  refine ⟨232385825698575748618675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309847767598100998158233 232385825698575748618675)
                  ·
                    rfl

theorem cell20_509141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_509141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509141 prefixEnd_509141 := by exact prefixLift 509141
  have htrace : WordTrace (prefixWord ++ tailWord_509141) baseStart_509141 baseEnd_509141 := by
    simpa [prefixWord, tailWord_509141, baseEnd_509141] using wordTrace_append hprefix tailTrace_509141
  have hstable : (prefixWord ++ tailWord_509141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509141).length < 2 ^ (prefixWord ++ tailWord_509141).sum := by decide
  have hdescent : baseEnd_509141 < baseStart_509141 := by decide
  rcases family_descends (prefixWord ++ tailWord_509141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509162 : List Nat := [3, 1, 3, 1, 1, 3, 2, 4, 2]
def baseStart_509162 : Nat := 118140960795 + 509162 * 2 ^ 59
def prefixEnd_509162 : Nat := 4983230072969 + 3 ^ 40 * 509162 * 2
def baseEnd_509162 : Nat := 232395410670793008918589

theorem tailTrace_509162 : CollatzResearch.WordTrace tailWord_509162 prefixEnd_509162 232395410670793008918589 := by
  unfold tailWord_509162
  simp only [CollatzResearch.WordTrace]
  refine ⟨4642665945350126697908435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12380442520933671194422493 4642665945350126697908435)
  ·
    refine ⟨6963998918025190046862653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4642665945350126697908435 6963998918025190046862653)
    ·
      refine ⟨2611499594259446267573495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6963998918025190046862653 2611499594259446267573495)
      ·
        refine ⟨3917249391389169401360243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2611499594259446267573495 3917249391389169401360243)
        ·
          refine ⟨5875874087083754102040365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3917249391389169401360243 5875874087083754102040365)
          ·
            refine ⟨2203452782656407788265137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5875874087083754102040365 2203452782656407788265137)
            ·
              refine ⟨1652589586992305841198853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2203452782656407788265137 1652589586992305841198853)
              ·
                refine ⟨309860547561057345224785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1652589586992305841198853 309860547561057345224785)
                ·
                  refine ⟨232395410670793008918589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309860547561057345224785 232395410670793008918589)
                  ·
                    rfl

theorem cell20_509162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_509162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509162 prefixEnd_509162 := by exact prefixLift 509162
  have htrace : WordTrace (prefixWord ++ tailWord_509162) baseStart_509162 baseEnd_509162 := by
    simpa [prefixWord, tailWord_509162, baseEnd_509162] using wordTrace_append hprefix tailTrace_509162
  have hstable : (prefixWord ++ tailWord_509162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509162).length < 2 ^ (prefixWord ++ tailWord_509162).sum := by decide
  have hdescent : baseEnd_509162 < baseStart_509162 := by decide
  rcases family_descends (prefixWord ++ tailWord_509162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509221 : List Nat := [1, 3, 1, 2, 4, 1, 3, 1, 4]
def baseStart_509221 : Nat := 118140960795 + 509221 * 2 ^ 59
def prefixEnd_509221 : Nat := 4983230072969 + 3 ^ 40 * 509221 * 2
def baseEnd_509221 : Nat := 232422339878451025951681

theorem tailTrace_509221 : CollatzResearch.WordTrace tailWord_509221 prefixEnd_509221 232422339878451025951681 := by
  unfold tailWord_509221
  simp only [CollatzResearch.WordTrace]
  refine ⟨18572815688186759868031517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12381877125457839912021011 18572815688186759868031517)
  ·
    refine ⟨6964805883070034950511819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18572815688186759868031517 6964805883070034950511819)
    ·
      refine ⟨10447208824605052425767729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6964805883070034950511819 10447208824605052425767729)
      ·
        refine ⟨7835406618453789319325797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10447208824605052425767729 7835406618453789319325797)
        ·
          refine ⟨1469138740960085497373587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7835406618453789319325797 1469138740960085497373587)
          ·
            refine ⟨2203708111440128246060381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469138740960085497373587 2203708111440128246060381)
            ·
              refine ⟨826390541790048092272643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2203708111440128246060381 826390541790048092272643)
              ·
                refine ⟨1239585812685072138408965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826390541790048092272643 1239585812685072138408965)
                ·
                  refine ⟨232422339878451025951681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1239585812685072138408965 232422339878451025951681)
                  ·
                    rfl

theorem cell20_509221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_509221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509221 prefixEnd_509221 := by exact prefixLift 509221
  have htrace : WordTrace (prefixWord ++ tailWord_509221) baseStart_509221 baseEnd_509221 := by
    simpa [prefixWord, tailWord_509221, baseEnd_509221] using wordTrace_append hprefix tailTrace_509221
  have hstable : (prefixWord ++ tailWord_509221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509221).length < 2 ^ (prefixWord ++ tailWord_509221).sum := by decide
  have hdescent : baseEnd_509221 < baseStart_509221 := by decide
  rcases family_descends (prefixWord ++ tailWord_509221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509242 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_509242 : Nat := 118140960795 + 509242 * 2 ^ 59
def prefixEnd_509242 : Nat := 4983230072969 + 3 ^ 40 * 509242 * 2
def baseEnd_509242 : Nat := 232431924850668286251595

theorem tailTrace_509242 : CollatzResearch.WordTrace tailWord_509242 prefixEnd_509242 232431924850668286251595 := by
  unfold tailWord_509242
  simp only [CollatzResearch.WordTrace]
  refine ⟨4643395405277670113636495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12382387747407120303030653 4643395405277670113636495)
  ·
    refine ⟨6965093107916505170454743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4643395405277670113636495 6965093107916505170454743)
    ·
      refine ⟨10447639661874757755682115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6965093107916505170454743 10447639661874757755682115)
      ·
        refine ⟨15671459492812136633523173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10447639661874757755682115 15671459492812136633523173)
        ·
          refine ⟨2938398654902275618785595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15671459492812136633523173 2938398654902275618785595)
          ·
            refine ⟨4407597982353413428178393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2938398654902275618785595 4407597982353413428178393)
            ·
              refine ⟨3305698486765060071133795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4407597982353413428178393 3305698486765060071133795)
              ·
                refine ⟨4958547730147590106700693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3305698486765060071133795 4958547730147590106700693)
                ·
                  refine ⟨232431924850668286251595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4958547730147590106700693 232431924850668286251595)
                  ·
                    rfl

theorem cell20_509242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_509242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509242 prefixEnd_509242 := by exact prefixLift 509242
  have htrace : WordTrace (prefixWord ++ tailWord_509242) baseStart_509242 baseEnd_509242 := by
    simpa [prefixWord, tailWord_509242, baseEnd_509242] using wordTrace_append hprefix tailTrace_509242
  have hstable : (prefixWord ++ tailWord_509242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509242).length < 2 ^ (prefixWord ++ tailWord_509242).sum := by decide
  have hdescent : baseEnd_509242 < baseStart_509242 := by decide
  rcases family_descends (prefixWord ++ tailWord_509242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509273 : List Nat := [1, 2, 1, 2, 2, 2, 3, 4, 3]
def baseStart_509273 : Nat := 118140960795 + 509273 * 2 ^ 59
def prefixEnd_509273 : Nat := 4983230072969 + 3 ^ 40 * 509273 * 2
def baseEnd_509273 : Nat := 232446074095369956218135

theorem tailTrace_509273 : CollatzResearch.WordTrace tailWord_509273 prefixEnd_509273 232446074095369956218135 := by
  unfold tailWord_509273
  simp only [CollatzResearch.WordTrace]
  refine ⟨18574712283998372748924473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12383141522665581832616315 18574712283998372748924473)
  ·
    refine ⟨13931034212998779561693355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18574712283998372748924473 13931034212998779561693355)
    ·
      refine ⟨20896551319498169342540033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13931034212998779561693355 20896551319498169342540033)
      ·
        refine ⟨15672413489623627006905025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20896551319498169342540033 15672413489623627006905025)
        ·
          refine ⟨11754310117217720255178769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15672413489623627006905025 11754310117217720255178769)
          ·
            refine ⟨8815732587913290191384077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11754310117217720255178769 8815732587913290191384077)
            ·
              refine ⟨3305899720467483821769029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8815732587913290191384077 3305899720467483821769029)
              ·
                refine ⟨619856197587653216581693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3305899720467483821769029 619856197587653216581693)
                ·
                  refine ⟨232446074095369956218135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 619856197587653216581693 232446074095369956218135)
                  ·
                    rfl

theorem cell20_509273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 3].length) (baseStart_509273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509273 prefixEnd_509273 := by exact prefixLift 509273
  have htrace : WordTrace (prefixWord ++ tailWord_509273) baseStart_509273 baseEnd_509273 := by
    simpa [prefixWord, tailWord_509273, baseEnd_509273] using wordTrace_append hprefix tailTrace_509273
  have hstable : (prefixWord ++ tailWord_509273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509273).length < 2 ^ (prefixWord ++ tailWord_509273).sum := by decide
  have hdescent : baseEnd_509273 < baseStart_509273 := by decide
  rcases family_descends (prefixWord ++ tailWord_509273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509356 : List Nat := [2, 2, 1, 1, 1, 1, 6, 2, 4]
def baseStart_509356 : Nat := 118140960795 + 509356 * 2 ^ 59
def prefixEnd_509356 : Nat := 4983230072969 + 3 ^ 40 * 509356 * 2
def baseEnd_509356 : Nat := 232483957556990556451129

theorem tailTrace_509356 : CollatzResearch.WordTrace tailWord_509356 prefixEnd_509356 232483957556990556451129 := by
  unfold tailWord_509356
  simp only [CollatzResearch.WordTrace]
  refine ⟨9288869771348838962097961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12385159695131785282797281 9288869771348838962097961)
  ·
    refine ⟨6966652328511629221573471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9288869771348838962097961 6966652328511629221573471)
    ·
      refine ⟨10449978492767443832360207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6966652328511629221573471 10449978492767443832360207)
      ·
        refine ⟨15674967739151165748540311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10449978492767443832360207 15674967739151165748540311)
        ·
          refine ⟨23512451608726748622810467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15674967739151165748540311 23512451608726748622810467)
          ·
            refine ⟨35268677413090122934215701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23512451608726748622810467 35268677413090122934215701)
            ·
              refine ⟨1653219253738599512541361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35268677413090122934215701 1653219253738599512541361)
              ·
                refine ⟨1239914440303949634406021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1653219253738599512541361 1239914440303949634406021)
                ·
                  refine ⟨232483957556990556451129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1239914440303949634406021 232483957556990556451129)
                  ·
                    rfl

theorem cell20_509356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_509356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509356 prefixEnd_509356 := by exact prefixLift 509356
  have htrace : WordTrace (prefixWord ++ tailWord_509356) baseStart_509356 baseEnd_509356 := by
    simpa [prefixWord, tailWord_509356, baseEnd_509356] using wordTrace_append hprefix tailTrace_509356
  have hstable : (prefixWord ++ tailWord_509356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509356).length < 2 ^ (prefixWord ++ tailWord_509356).sum := by decide
  have hdescent : baseEnd_509356 < baseStart_509356 := by decide
  rcases family_descends (prefixWord ++ tailWord_509356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509369 : List Nat := [1, 2, 1, 4, 4, 2, 1, 3, 2]
def baseStart_509369 : Nat := 118140960795 + 509369 * 2 ^ 59
def prefixEnd_509369 : Nat := 4983230072969 + 3 ^ 40 * 509369 * 2
def baseEnd_509369 : Nat := 232489891111220289017743

theorem tailTrace_509369 : CollatzResearch.WordTrace tailWord_509369 prefixEnd_509369 232489891111220289017743 := by
  unfold tailWord_509369
  simp only [CollatzResearch.WordTrace]
  refine ⟨18578213691650581144419161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12385475794433720762946107 18578213691650581144419161)
  ·
    refine ⟨13933660268737935858314371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18578213691650581144419161 13933660268737935858314371)
    ·
      refine ⟨20900490403106903787471557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13933660268737935858314371 20900490403106903787471557)
      ·
        refine ⟨3918841950582544460150917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20900490403106903787471557 3918841950582544460150917)
        ·
          refine ⟨734782865734227086278297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3918841950582544460150917 734782865734227086278297)
          ·
            refine ⟨551087149300670314708723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 734782865734227086278297 551087149300670314708723)
            ·
              refine ⟨826630723951005472063085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551087149300670314708723 826630723951005472063085)
              ·
                refine ⟨309986521481627052023657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 826630723951005472063085 309986521481627052023657)
                ·
                  refine ⟨232489891111220289017743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309986521481627052023657 232489891111220289017743)
                  ·
                    rfl

theorem cell20_509369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 3, 2].length) (baseStart_509369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509369 prefixEnd_509369 := by exact prefixLift 509369
  have htrace : WordTrace (prefixWord ++ tailWord_509369) baseStart_509369 baseEnd_509369 := by
    simpa [prefixWord, tailWord_509369, baseEnd_509369] using wordTrace_append hprefix tailTrace_509369
  have hstable : (prefixWord ++ tailWord_509369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509369).length < 2 ^ (prefixWord ++ tailWord_509369).sum := by decide
  have hdescent : baseEnd_509369 < baseStart_509369 := by decide
  rcases family_descends (prefixWord ++ tailWord_509369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509380 : List Nat := [2, 3, 3, 2, 1, 1, 8]
def baseStart_509380 : Nat := 118140960795 + 509380 * 2 ^ 59
def prefixEnd_509380 : Nat := 4983230072969 + 3 ^ 40 * 509380 * 2
def baseEnd_509380 : Nat := 25832767978994793294559

theorem tailTrace_509380 : CollatzResearch.WordTrace tailWord_509380 prefixEnd_509380 25832767978994793294559 := by
  unfold tailWord_509380
  simp only [CollatzResearch.WordTrace]
  refine ⟨9289307447305365011534797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12385743263073820015379729 9289307447305365011534797)
  ·
    refine ⟨3483490292739511879325549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9289307447305365011534797 3483490292739511879325549)
    ·
      refine ⟨1306308859777316954747081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3483490292739511879325549 1306308859777316954747081)
      ·
        refine ⟨979731644832987716060311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1306308859777316954747081 979731644832987716060311)
        ·
          refine ⟨1469597467249481574090467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 979731644832987716060311 1469597467249481574090467)
          ·
            refine ⟨2204396200874222361135701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469597467249481574090467 2204396200874222361135701)
            ·
              refine ⟨25832767978994793294559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2204396200874222361135701 25832767978994793294559)
              ·
                rfl

theorem cell20_509380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 8].length) (baseStart_509380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509380 prefixEnd_509380 := by exact prefixLift 509380
  have htrace : WordTrace (prefixWord ++ tailWord_509380) baseStart_509380 baseEnd_509380 := by
    simpa [prefixWord, tailWord_509380, baseEnd_509380] using wordTrace_append hprefix tailTrace_509380
  have hstable : (prefixWord ++ tailWord_509380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509380).length < 2 ^ (prefixWord ++ tailWord_509380).sum := by decide
  have hdescent : baseEnd_509380 < baseStart_509380 := by decide
  rcases family_descends (prefixWord ++ tailWord_509380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509401 : List Nat := [1, 2, 1, 2, 4, 2, 1, 7]
def baseStart_509401 : Nat := 118140960795 + 509401 * 2 ^ 59
def prefixEnd_509401 : Nat := 4983230072969 + 3 ^ 40 * 509401 * 2
def baseEnd_509401 : Nat := 77501498927723466650315

theorem tailTrace_509401 : CollatzResearch.WordTrace tailWord_509401 prefixEnd_509401 77501498927723466650315 := by
  unfold tailWord_509401
  simp only [CollatzResearch.WordTrace]
  refine ⟨18579380827534650609584057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12386253885023100406389371 18579380827534650609584057)
  ·
    refine ⟨13934535620650987957188043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18579380827534650609584057 13934535620650987957188043)
    ·
      refine ⟨20901803430976481935782065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13934535620650987957188043 20901803430976481935782065)
      ·
        refine ⟨15676352573232361451836549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20901803430976481935782065 15676352573232361451836549)
        ·
          refine ⟨2939316107481067772219353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15676352573232361451836549 2939316107481067772219353)
          ·
            refine ⟨2204487080610800829164515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2939316107481067772219353 2204487080610800829164515)
            ·
              refine ⟨3306730620916201243746773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2204487080610800829164515 3306730620916201243746773)
              ·
                refine ⟨77501498927723466650315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3306730620916201243746773 77501498927723466650315)
                ·
                  rfl

theorem cell20_509401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 7].length) (baseStart_509401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509401 prefixEnd_509401 := by exact prefixLift 509401
  have htrace : WordTrace (prefixWord ++ tailWord_509401) baseStart_509401 baseEnd_509401 := by
    simpa [prefixWord, tailWord_509401, baseEnd_509401] using wordTrace_append hprefix tailTrace_509401
  have hstable : (prefixWord ++ tailWord_509401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509401).length < 2 ^ (prefixWord ++ tailWord_509401).sum := by decide
  have hdescent : baseEnd_509401 < baseStart_509401 := by decide
  rcases family_descends (prefixWord ++ tailWord_509401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509408 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 7]
def baseStart_509408 : Nat := 118140960795 + 509408 * 2 ^ 59
def prefixEnd_509408 : Nat := 4983230072969 + 3 ^ 40 * 509408 * 2
def baseEnd_509408 : Nat := 232507691773909486717583

theorem tailTrace_509408 : CollatzResearch.WordTrace tailWord_509408 prefixEnd_509408 232507691773909486717583 := by
  unfold tailWord_509408
  simp only [CollatzResearch.WordTrace]
  refine ⟨9289818069254645402544439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12386424092339527203392585 9289818069254645402544439)
  ·
    refine ⟨13934727103881968103816659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9289818069254645402544439 13934727103881968103816659)
    ·
      refine ⟨20902090655822952155724989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13934727103881968103816659 20902090655822952155724989)
      ·
        refine ⟨7838283995933607058396871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20902090655822952155724989 7838283995933607058396871)
        ·
          refine ⟨11757425993900410587595307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7838283995933607058396871 11757425993900410587595307)
          ·
            refine ⟨17636138990850615881392961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11757425993900410587595307 17636138990850615881392961)
            ·
              refine ⟨13227104243137961911044721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17636138990850615881392961 13227104243137961911044721)
              ·
                refine ⟨9920328182353471433283541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13227104243137961911044721 9920328182353471433283541)
                ·
                  refine ⟨232507691773909486717583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9920328182353471433283541 232507691773909486717583)
                  ·
                    rfl

theorem cell20_509408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_509408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509408 prefixEnd_509408 := by exact prefixLift 509408
  have htrace : WordTrace (prefixWord ++ tailWord_509408) baseStart_509408 baseEnd_509408 := by
    simpa [prefixWord, tailWord_509408, baseEnd_509408] using wordTrace_append hprefix tailTrace_509408
  have hstable : (prefixWord ++ tailWord_509408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509408).length < 2 ^ (prefixWord ++ tailWord_509408).sum := by decide
  have hdescent : baseEnd_509408 < baseStart_509408 := by decide
  rcases family_descends (prefixWord ++ tailWord_509408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509438 : List Nat := [4, 2, 2, 3, 1, 1, 2, 2, 3]
def baseStart_509438 : Nat := 118140960795 + 509438 * 2 ^ 59
def prefixEnd_509438 : Nat := 4983230072969 + 3 ^ 40 * 509438 * 2
def baseEnd_509438 : Nat := 232521384591362715717461

theorem tailTrace_509438 : CollatzResearch.WordTrace tailWord_509438 prefixEnd_509438 232521384591362715717461 := by
  unfold tailWord_509438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2322591291050075741085121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12387153552267070619120645 2322591291050075741085121)
  ·
    refine ⟨1741943468287556805813841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2322591291050075741085121 1741943468287556805813841)
    ·
      refine ⟨1306457601215667604360381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1741943468287556805813841 1306457601215667604360381)
      ·
        refine ⟨489921600455875351635143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1306457601215667604360381 489921600455875351635143)
        ·
          refine ⟨734882400683813027452715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 489921600455875351635143 734882400683813027452715)
          ·
            refine ⟨1102323601025719541179073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 734882400683813027452715 1102323601025719541179073)
            ·
              refine ⟨826742700769289655884305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1102323601025719541179073 826742700769289655884305)
              ·
                refine ⟨620057025576967241913229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826742700769289655884305 620057025576967241913229)
                ·
                  refine ⟨232521384591362715717461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620057025576967241913229 232521384591362715717461)
                  ·
                    rfl

theorem cell20_509438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_509438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509438 prefixEnd_509438 := by exact prefixLift 509438
  have htrace : WordTrace (prefixWord ++ tailWord_509438) baseStart_509438 baseEnd_509438 := by
    simpa [prefixWord, tailWord_509438, baseEnd_509438] using wordTrace_append hprefix tailTrace_509438
  have hstable : (prefixWord ++ tailWord_509438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509438).length < 2 ^ (prefixWord ++ tailWord_509438).sum := by decide
  have hdescent : baseEnd_509438 < baseStart_509438 := by decide
  rcases family_descends (prefixWord ++ tailWord_509438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509449 : List Nat := [1, 2, 1, 1, 3, 1, 5, 4, 2]
def baseStart_509449 : Nat := 118140960795 + 509449 * 2 ^ 59
def prefixEnd_509449 : Nat := 4983230072969 + 3 ^ 40 * 509449 * 2
def baseEnd_509449 : Nat := 232526405291095566350749

theorem tailTrace_509449 : CollatzResearch.WordTrace tailWord_509449 prefixEnd_509449 232526405291095566350749 := by
  unfold tailWord_509449
  simp only [CollatzResearch.WordTrace]
  refine ⟨18581131531360754807331401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12387421020907169871554267 18581131531360754807331401)
  ·
    refine ⟨13935848648520566105498551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18581131531360754807331401 13935848648520566105498551)
    ·
      refine ⟨20903772972780849158247827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13935848648520566105498551 20903772972780849158247827)
      ·
        refine ⟨31355659459171273737371741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20903772972780849158247827 31355659459171273737371741)
        ·
          refine ⟨11758372297189227651514403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31355659459171273737371741 11758372297189227651514403)
          ·
            refine ⟨17637558445783841477271605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11758372297189227651514403 17637558445783841477271605)
            ·
              refine ⟨1653521104292235138494213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17637558445783841477271605 1653521104292235138494213)
              ·
                refine ⟨310035207054794088467665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1653521104292235138494213 310035207054794088467665)
                ·
                  refine ⟨232526405291095566350749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310035207054794088467665 232526405291095566350749)
                  ·
                    rfl

theorem cell20_509449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 2].length) (baseStart_509449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509449 prefixEnd_509449 := by exact prefixLift 509449
  have htrace : WordTrace (prefixWord ++ tailWord_509449) baseStart_509449 baseEnd_509449 := by
    simpa [prefixWord, tailWord_509449, baseEnd_509449] using wordTrace_append hprefix tailTrace_509449
  have hstable : (prefixWord ++ tailWord_509449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509449).length < 2 ^ (prefixWord ++ tailWord_509449).sum := by decide
  have hdescent : baseEnd_509449 < baseStart_509449 := by decide
  rcases family_descends (prefixWord ++ tailWord_509449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509532 : List Nat := [2, 2, 4, 1, 2, 2, 1, 6]
def baseStart_509532 : Nat := 118140960795 + 509532 * 2 ^ 59
def prefixEnd_509532 : Nat := 4983230072969 + 3 ^ 40 * 509532 * 2
def baseEnd_509532 : Nat := 77521429584238722194581

theorem tailTrace_509532 : CollatzResearch.WordTrace tailWord_509532 prefixEnd_509532 77521429584238722194581 := by
  unfold tailWord_509532
  simp only [CollatzResearch.WordTrace]
  refine ⟨9292079395030029991301425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12389439193373373321735233 9292079395030029991301425)
  ·
    refine ⟨6969059546272522493476069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9292079395030029991301425 6969059546272522493476069)
    ·
      refine ⟨1306698664926097967526763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6969059546272522493476069 1306698664926097967526763)
      ·
        refine ⟨1960047997389146951290145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1306698664926097967526763 1960047997389146951290145)
        ·
          refine ⟨1470035998041860213467609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1960047997389146951290145 1470035998041860213467609)
          ·
            refine ⟨1102526998531395160100707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1470035998041860213467609 1102526998531395160100707)
            ·
              refine ⟨1653790497797092740151061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1102526998531395160100707 1653790497797092740151061)
              ·
                refine ⟨77521429584238722194581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1653790497797092740151061 77521429584238722194581)
                ·
                  rfl

theorem cell20_509532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_509532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509532 prefixEnd_509532 := by exact prefixLift 509532
  have htrace : WordTrace (prefixWord ++ tailWord_509532) baseStart_509532 baseEnd_509532 := by
    simpa [prefixWord, tailWord_509532, baseEnd_509532] using wordTrace_append hprefix tailTrace_509532
  have hstable : (prefixWord ++ tailWord_509532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509532).length < 2 ^ (prefixWord ++ tailWord_509532).sum := by decide
  have hdescent : baseEnd_509532 < baseStart_509532 := by decide
  rcases family_descends (prefixWord ++ tailWord_509532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509549 : List Nat := [1, 5, 1, 1, 5, 1, 6]
def baseStart_509549 : Nat := 118140960795 + 509549 * 2 ^ 59
def prefixEnd_509549 : Nat := 4983230072969 + 3 ^ 40 * 509549 * 2
def baseEnd_509549 : Nat := 25841338668437740335223

theorem tailTrace_509549 : CollatzResearch.WordTrace tailWord_509549 prefixEnd_509549 25841338668437740335223 := by
  unfold tailWord_509549
  simp only [CollatzResearch.WordTrace]
  refine ⟨18584778830998471885971701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12389852553998981257314467 18584778830998471885971701)
  ·
    refine ⟨1742323015406106739309847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18584778830998471885971701 1742323015406106739309847)
    ·
      refine ⟨2613484523109160108964771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1742323015406106739309847 2613484523109160108964771)
      ·
        refine ⟨3920226784663740163447157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2613484523109160108964771 3920226784663740163447157)
        ·
          refine ⟨367521261062225640323171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3920226784663740163447157 367521261062225640323171)
          ·
            refine ⟨551281891593338460484757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367521261062225640323171 551281891593338460484757)
            ·
              refine ⟨25841338668437740335223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 551281891593338460484757 25841338668437740335223)
              ·
                rfl

theorem cell20_509549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 6].length) (baseStart_509549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509549 prefixEnd_509549 := by exact prefixLift 509549
  have htrace : WordTrace (prefixWord ++ tailWord_509549) baseStart_509549 baseEnd_509549 := by
    simpa [prefixWord, tailWord_509549, baseEnd_509549] using wordTrace_append hprefix tailTrace_509549
  have hstable : (prefixWord ++ tailWord_509549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509549).length < 2 ^ (prefixWord ++ tailWord_509549).sum := by decide
  have hdescent : baseEnd_509549 < baseStart_509549 := by decide
  rcases family_descends (prefixWord ++ tailWord_509549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509591 : List Nat := [1, 1, 3, 3, 2, 2, 2, 6]
def baseStart_509591 : Nat := 118140960795 + 509591 * 2 ^ 59
def prefixEnd_509591 : Nat := 4983230072969 + 3 ^ 40 * 509591 * 2
def baseEnd_509591 : Nat := 77530405986791394538945

theorem tailTrace_509591 : CollatzResearch.WordTrace tailWord_509591 prefixEnd_509591 77530405986791394538945 := by
  unfold tailWord_509591
  simp only [CollatzResearch.WordTrace]
  refine ⟨18586310696846313059000627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12390873797897542039333751 18586310696846313059000627)
  ·
    refine ⟨27879466045269469588500941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18586310696846313059000627 27879466045269469588500941)
    ·
      refine ⟨10454799766976051095687853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27879466045269469588500941 10454799766976051095687853)
      ·
        refine ⟨3920549912616019160882945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10454799766976051095687853 3920549912616019160882945)
        ·
          refine ⟨2940412434462014370662209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3920549912616019160882945 2940412434462014370662209)
          ·
            refine ⟨2205309325846510777996657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2940412434462014370662209 2205309325846510777996657)
            ·
              refine ⟨1653981994384883083497493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2205309325846510777996657 1653981994384883083497493)
              ·
                refine ⟨77530405986791394538945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1653981994384883083497493 77530405986791394538945)
                ·
                  rfl

theorem cell20_509591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 6].length) (baseStart_509591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509591 prefixEnd_509591 := by exact prefixLift 509591
  have htrace : WordTrace (prefixWord ++ tailWord_509591) baseStart_509591 baseEnd_509591 := by
    simpa [prefixWord, tailWord_509591, baseEnd_509591] using wordTrace_append hprefix tailTrace_509591
  have hstable : (prefixWord ++ tailWord_509591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509591).length < 2 ^ (prefixWord ++ tailWord_509591).sum := by decide
  have hdescent : baseEnd_509591 < baseStart_509591 := by decide
  rcases family_descends (prefixWord ++ tailWord_509591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509615 : List Nat := [1, 1, 2, 1, 2, 4, 4, 2, 3]
def baseStart_509615 : Nat := 118140960795 + 509615 * 2 ^ 59
def prefixEnd_509615 : Nat := 4983230072969 + 3 ^ 40 * 509615 * 2
def baseEnd_509615 : Nat := 232602172214336766816737

theorem tailTrace_509615 : CollatzResearch.WordTrace tailWord_509615 prefixEnd_509615 232602172214336766816737 := by
  unfold tailWord_509615
  simp only [CollatzResearch.WordTrace]
  refine ⟨18587186048759365157874299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12391457365839576771916199 18587186048759365157874299)
  ·
    refine ⟨27880779073139047736811449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18587186048759365157874299 27880779073139047736811449)
    ·
      refine ⟨20910584304854285802608587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27880779073139047736811449 20910584304854285802608587)
      ·
        refine ⟨31365876457281428703912881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20910584304854285802608587 31365876457281428703912881)
        ·
          refine ⟨23524407342961071527934661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31365876457281428703912881 23524407342961071527934661)
          ·
            refine ⟨4410826376805200911487749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23524407342961071527934661 4410826376805200911487749)
            ·
              refine ⟨827029945650975170903953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4410826376805200911487749 827029945650975170903953)
              ·
                refine ⟨620272459238231378177965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827029945650975170903953 620272459238231378177965)
                ·
                  refine ⟨232602172214336766816737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620272459238231378177965 232602172214336766816737)
                  ·
                    rfl

theorem cell20_509615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 2, 3].length) (baseStart_509615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509615 prefixEnd_509615 := by exact prefixLift 509615
  have htrace : WordTrace (prefixWord ++ tailWord_509615) baseStart_509615 baseEnd_509615 := by
    simpa [prefixWord, tailWord_509615, baseEnd_509615] using wordTrace_append hprefix tailTrace_509615
  have hstable : (prefixWord ++ tailWord_509615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509615).length < 2 ^ (prefixWord ++ tailWord_509615).sum := by decide
  have hdescent : baseEnd_509615 < baseStart_509615 := by decide
  rcases family_descends (prefixWord ++ tailWord_509615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509618 : List Nat := [3, 2, 1, 1, 1, 2, 6, 2, 2]
def baseStart_509618 : Nat := 118140960795 + 509618 * 2 ^ 59
def prefixEnd_509618 : Nat := 4983230072969 + 3 ^ 40 * 509618 * 2
def baseEnd_509618 : Nat := 232603541496082089716725

theorem tailTrace_509618 : CollatzResearch.WordTrace tailWord_509618 prefixEnd_509618 232603541496082089716725 := by
  unfold tailWord_509618
  simp only [CollatzResearch.WordTrace]
  refine ⟨4646823866937124167558377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12391530311832331113489005 4646823866937124167558377)
  ·
    refine ⟨3485117900202843125668783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4646823866937124167558377 3485117900202843125668783)
    ·
      refine ⟨5227676850304264688503175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3485117900202843125668783 5227676850304264688503175)
      ·
        refine ⟨7841515275456397032754763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5227676850304264688503175 7841515275456397032754763)
        ·
          refine ⟨11762272913184595549132145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7841515275456397032754763 11762272913184595549132145)
          ·
            refine ⟨8821704684888446661849109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11762272913184595549132145 8821704684888446661849109)
            ·
              refine ⟨413517407104145937274177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8821704684888446661849109 413517407104145937274177)
              ·
                refine ⟨310138055328109452955633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413517407104145937274177 310138055328109452955633)
                ·
                  refine ⟨232603541496082089716725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310138055328109452955633 232603541496082089716725)
                  ·
                    rfl

theorem cell20_509618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_509618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509618 prefixEnd_509618 := by exact prefixLift 509618
  have htrace : WordTrace (prefixWord ++ tailWord_509618) baseStart_509618 baseEnd_509618 := by
    simpa [prefixWord, tailWord_509618, baseEnd_509618] using wordTrace_append hprefix tailTrace_509618
  have hstable : (prefixWord ++ tailWord_509618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509618).length < 2 ^ (prefixWord ++ tailWord_509618).sum := by decide
  have hdescent : baseEnd_509618 < baseStart_509618 := by decide
  rcases family_descends (prefixWord ++ tailWord_509618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509646 : List Nat := [4, 1, 1, 1, 3, 1, 5, 4]
def baseStart_509646 : Nat := 118140960795 + 509646 * 2 ^ 59
def prefixEnd_509646 : Nat := 4983230072969 + 3 ^ 40 * 509646 * 2
def baseEnd_509646 : Nat := 77538773819679478927759

theorem tailTrace_509646 : CollatzResearch.WordTrace tailWord_509646 prefixEnd_509646 77538773819679478927759 := by
  unfold tailWord_509646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2323539588955882181531599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12392211141098038301501861 2323539588955882181531599)
  ·
    refine ⟨3485309383433823272297399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2323539588955882181531599 3485309383433823272297399)
    ·
      refine ⟨5227964075150734908446099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3485309383433823272297399 5227964075150734908446099)
      ·
        refine ⟨7841946112726102362669149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5227964075150734908446099 7841946112726102362669149)
        ·
          refine ⟨2940729792272288386000931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7841946112726102362669149 2940729792272288386000931)
          ·
            refine ⟨4411094688408432579001397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940729792272288386000931 4411094688408432579001397)
            ·
              refine ⟨413540127038290554281381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4411094688408432579001397 413540127038290554281381)
              ·
                refine ⟨77538773819679478927759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 413540127038290554281381 77538773819679478927759)
                ·
                  rfl

theorem cell20_509646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_509646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509646 prefixEnd_509646 := by exact prefixLift 509646
  have htrace : WordTrace (prefixWord ++ tailWord_509646) baseStart_509646 baseEnd_509646 := by
    simpa [prefixWord, tailWord_509646, baseEnd_509646] using wordTrace_append hprefix tailTrace_509646
  have hstable : (prefixWord ++ tailWord_509646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509646).length < 2 ^ (prefixWord ++ tailWord_509646).sum := by decide
  have hdescent : baseEnd_509646 < baseStart_509646 := by decide
  rcases family_descends (prefixWord ++ tailWord_509646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509677 : List Nat := [1, 5, 1, 2, 1, 3, 2, 1, 4]
def baseStart_509677 : Nat := 118140960795 + 509677 * 2 ^ 59
def prefixEnd_509677 : Nat := 4983230072969 + 3 ^ 40 * 509677 * 2
def baseEnd_509677 : Nat := 232630470703740106749817

theorem tailTrace_509677 : CollatzResearch.WordTrace tailWord_509677 prefixEnd_509677 232630470703740106749817 := by
  unfold tailWord_509677
  simp only [CollatzResearch.WordTrace]
  refine ⟨18589447374534749746631285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12392964916356499831087523 18589447374534749746631285)
  ·
    refine ⟨1742760691362632788746683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18589447374534749746631285 1742760691362632788746683)
    ·
      refine ⟨2614141037043949183120025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1742760691362632788746683 2614141037043949183120025)
      ·
        refine ⟨1960605777782961887340019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2614141037043949183120025 1960605777782961887340019)
        ·
          refine ⟨2940908666674442831010029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1960605777782961887340019 2940908666674442831010029)
          ·
            refine ⟨1102840750002916061628761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2940908666674442831010029 1102840750002916061628761)
            ·
              refine ⟨827130562502187046221571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1102840750002916061628761 827130562502187046221571)
              ·
                refine ⟨1240695843753280569332357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 827130562502187046221571 1240695843753280569332357)
                ·
                  refine ⟨232630470703740106749817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1240695843753280569332357 232630470703740106749817)
                  ·
                    rfl

theorem cell20_509677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_509677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509677 prefixEnd_509677 := by exact prefixLift 509677
  have htrace : WordTrace (prefixWord ++ tailWord_509677) baseStart_509677 baseEnd_509677 := by
    simpa [prefixWord, tailWord_509677, baseEnd_509677] using wordTrace_append hprefix tailTrace_509677
  have hstable : (prefixWord ++ tailWord_509677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509677).length < 2 ^ (prefixWord ++ tailWord_509677).sum := by decide
  have hdescent : baseEnd_509677 < baseStart_509677 := by decide
  rcases family_descends (prefixWord ++ tailWord_509677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509742 : List Nat := [4, 1, 3, 2, 2, 2, 2, 1, 3]
def baseStart_509742 : Nat := 118140960795 + 509742 * 2 ^ 59
def prefixEnd_509742 : Nat := 4983230072969 + 3 ^ 40 * 509742 * 2
def baseEnd_509742 : Nat := 232660138474888769582885

theorem tailTrace_509742 : CollatzResearch.WordTrace tailWord_509742 prefixEnd_509742 232660138474888769582885 := by
  unfold tailWord_509742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2323977264912408230968435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12394545412866177231831653 2323977264912408230968435)
  ·
    refine ⟨3485965897368612346452653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2323977264912408230968435 3485965897368612346452653)
    ·
      refine ⟨1307237211513229629919745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3485965897368612346452653 1307237211513229629919745)
      ·
        refine ⟨980427908634922222439809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1307237211513229629919745 980427908634922222439809)
        ·
          refine ⟨735320931476191666829857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 980427908634922222439809 735320931476191666829857)
          ·
            refine ⟨551490698607143750122393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 735320931476191666829857 551490698607143750122393)
            ·
              refine ⟨413618023955357812591795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 551490698607143750122393 413618023955357812591795)
              ·
                refine ⟨620427035933036718887693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413618023955357812591795 620427035933036718887693)
                ·
                  refine ⟨232660138474888769582885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620427035933036718887693 232660138474888769582885)
                  ·
                    rfl

theorem cell20_509742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_509742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509742 prefixEnd_509742 := by exact prefixLift 509742
  have htrace : WordTrace (prefixWord ++ tailWord_509742) baseStart_509742 baseEnd_509742 := by
    simpa [prefixWord, tailWord_509742, baseEnd_509742] using wordTrace_append hprefix tailTrace_509742
  have hstable : (prefixWord ++ tailWord_509742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509742).length < 2 ^ (prefixWord ++ tailWord_509742).sum := by decide
  have hdescent : baseEnd_509742 < baseStart_509742 := by decide
  rcases family_descends (prefixWord ++ tailWord_509742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509746 : List Nat := [3, 2, 1, 1, 3, 2, 4, 1, 3]
def baseStart_509746 : Nat := 118140960795 + 509746 * 2 ^ 59
def prefixEnd_509746 : Nat := 4983230072969 + 3 ^ 40 * 509746 * 2
def baseEnd_509746 : Nat := 232661964183882533449535

theorem tailTrace_509746 : CollatzResearch.WordTrace tailWord_509746 prefixEnd_509746 232661964183882533449535 := by
  unfold tailWord_509746
  simp only [CollatzResearch.WordTrace]
  refine ⟨4647991002821193632723273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12394642674189849687262061 4647991002821193632723273)
  ·
    refine ⟨3485993252115895224542455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4647991002821193632723273 3485993252115895224542455)
    ·
      refine ⟨5228989878173842836813683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3485993252115895224542455 5228989878173842836813683)
      ·
        refine ⟨7843484817260764255220525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5228989878173842836813683 7843484817260764255220525)
        ·
          refine ⟨2941306806472786595707697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7843484817260764255220525 2941306806472786595707697)
          ·
            refine ⟨2205980104854589946780773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2941306806472786595707697 2205980104854589946780773)
            ·
              refine ⟨413621269660235615021395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2205980104854589946780773 413621269660235615021395)
              ·
                refine ⟨620431904490353422532093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413621269660235615021395 620431904490353422532093)
                ·
                  refine ⟨232661964183882533449535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620431904490353422532093 232661964183882533449535)
                  ·
                    rfl

theorem cell20_509746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_509746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509746 prefixEnd_509746 := by exact prefixLift 509746
  have htrace : WordTrace (prefixWord ++ tailWord_509746) baseStart_509746 baseEnd_509746 := by
    simpa [prefixWord, tailWord_509746, baseEnd_509746] using wordTrace_append hprefix tailTrace_509746
  have hstable : (prefixWord ++ tailWord_509746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509746).length < 2 ^ (prefixWord ++ tailWord_509746).sum := by decide
  have hdescent : baseEnd_509746 < baseStart_509746 := by decide
  rcases family_descends (prefixWord ++ tailWord_509746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509791 : List Nat := [1, 1, 2, 3, 1, 5, 1, 4, 2]
def baseStart_509791 : Nat := 118140960795 + 509791 * 2 ^ 59
def prefixEnd_509791 : Nat := 4983230072969 + 3 ^ 40 * 509791 * 2
def baseEnd_509791 : Nat := 232682503410062376949351

theorem tailTrace_509791 : CollatzResearch.WordTrace tailWord_509791 prefixEnd_509791 232682503410062376949351 := by
  unfold tailWord_509791
  simp only [CollatzResearch.WordTrace]
  refine ⟨18593605296121747216281227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12395736864081164810854151 18593605296121747216281227)
  ·
    refine ⟨27890407944182620824421841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18593605296121747216281227 27890407944182620824421841)
    ·
      refine ⟨20917805958136965618316381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27890407944182620824421841 20917805958136965618316381)
      ·
        refine ⟨7844177234301362106868643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20917805958136965618316381 7844177234301362106868643)
        ·
          refine ⟨11766265851452043160302965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7844177234301362106868643 11766265851452043160302965)
          ·
            refine ⟨1103087423573629046278403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11766265851452043160302965 1103087423573629046278403)
            ·
              refine ⟨1654631135360443569417605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103087423573629046278403 1654631135360443569417605)
              ·
                refine ⟨310243337880083169265801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1654631135360443569417605 310243337880083169265801)
                ·
                  refine ⟨232682503410062376949351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310243337880083169265801 232682503410062376949351)
                  ·
                    rfl

theorem cell20_509791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 2].length) (baseStart_509791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509791 prefixEnd_509791 := by exact prefixLift 509791
  have htrace : WordTrace (prefixWord ++ tailWord_509791) baseStart_509791 baseEnd_509791 := by
    simpa [prefixWord, tailWord_509791, baseEnd_509791] using wordTrace_append hprefix tailTrace_509791
  have hstable : (prefixWord ++ tailWord_509791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509791).length < 2 ^ (prefixWord ++ tailWord_509791).sum := by decide
  have hdescent : baseEnd_509791 < baseStart_509791 := by decide
  rcases family_descends (prefixWord ++ tailWord_509791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509805 : List Nat := [1, 5, 1, 1, 1, 1, 4, 3, 3]
def baseStart_509805 : Nat := 118140960795 + 509805 * 2 ^ 59
def prefixEnd_509805 : Nat := 4983230072969 + 3 ^ 40 * 509805 * 2
def baseEnd_509805 : Nat := 232688893391540550482627

theorem tailTrace_509805 : CollatzResearch.WordTrace tailWord_509805 prefixEnd_509805 232688893391540550482627 := by
  unfold tailWord_509805
  simp only [CollatzResearch.WordTrace]
  refine ⟨18594115918071027607290869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12396077278714018404860579 18594115918071027607290869)
  ·
    refine ⟨1743198367319158838183519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18594115918071027607290869 1743198367319158838183519)
    ·
      refine ⟨2614797550978738257275279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1743198367319158838183519 2614797550978738257275279)
      ·
        refine ⟨3922196326468107385912919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2614797550978738257275279 3922196326468107385912919)
        ·
          refine ⟨5883294489702161078869379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3922196326468107385912919 5883294489702161078869379)
          ·
            refine ⟨8824941734553241618304069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5883294489702161078869379 8824941734553241618304069)
            ·
              refine ⟨1654676575228732803432013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8824941734553241618304069 1654676575228732803432013)
              ·
                refine ⟨620503715710774801287005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1654676575228732803432013 620503715710774801287005)
                ·
                  refine ⟨232688893391540550482627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620503715710774801287005 232688893391540550482627)
                  ·
                    rfl

theorem cell20_509805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_509805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509805 prefixEnd_509805 := by exact prefixLift 509805
  have htrace : WordTrace (prefixWord ++ tailWord_509805) baseStart_509805 baseEnd_509805 := by
    simpa [prefixWord, tailWord_509805, baseEnd_509805] using wordTrace_append hprefix tailTrace_509805
  have hstable : (prefixWord ++ tailWord_509805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509805).length < 2 ^ (prefixWord ++ tailWord_509805).sum := by decide
  have hdescent : baseEnd_509805 < baseStart_509805 := by decide
  rcases family_descends (prefixWord ++ tailWord_509805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509825 : List Nat := [1, 2, 4, 4, 1, 1, 2, 3, 2]
def baseStart_509825 : Nat := 118140960795 + 509825 * 2 ^ 59
def prefixEnd_509825 : Nat := 4983230072969 + 3 ^ 40 * 509825 * 2
def baseEnd_509825 : Nat := 232698021936509369815879

theorem tailTrace_509825 : CollatzResearch.WordTrace tailWord_509825 prefixEnd_509825 232698021936509369815879 := by
  unfold tailWord_509825
  simp only [CollatzResearch.WordTrace]
  refine ⟨18594845377998571023018929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12396563585332380682012619 18594845377998571023018929)
  ·
    refine ⟨13946134033498928267264197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18594845377998571023018929 13946134033498928267264197)
    ·
      refine ⟨2614900131281049050112037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13946134033498928267264197 2614900131281049050112037)
      ·
        refine ⟨490293774615196696896007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2614900131281049050112037 490293774615196696896007)
        ·
          refine ⟨735440661922795045344011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490293774615196696896007 735440661922795045344011)
          ·
            refine ⟨1103160992884192568016017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735440661922795045344011 1103160992884192568016017)
            ·
              refine ⟨827370744663144426012013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103160992884192568016017 827370744663144426012013)
              ·
                refine ⟨310264029248679159754505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 827370744663144426012013 310264029248679159754505)
                ·
                  refine ⟨232698021936509369815879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310264029248679159754505 232698021936509369815879)
                  ·
                    rfl

theorem cell20_509825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 2].length) (baseStart_509825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509825 prefixEnd_509825 := by exact prefixLift 509825
  have htrace : WordTrace (prefixWord ++ tailWord_509825) baseStart_509825 baseEnd_509825 := by
    simpa [prefixWord, tailWord_509825, baseEnd_509825] using wordTrace_append hprefix tailTrace_509825
  have hstable : (prefixWord ++ tailWord_509825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509825).length < 2 ^ (prefixWord ++ tailWord_509825).sum := by decide
  have hdescent : baseEnd_509825 < baseStart_509825 := by decide
  rcases family_descends (prefixWord ++ tailWord_509825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509829 : List Nat := [1, 3, 1, 1, 3, 2, 4, 3, 2]
def baseStart_509829 : Nat := 118140960795 + 509829 * 2 ^ 59
def prefixEnd_509829 : Nat := 4983230072969 + 3 ^ 40 * 509829 * 2
def baseEnd_509829 : Nat := 232699847645503133682529

theorem tailTrace_509829 : CollatzResearch.WordTrace tailWord_509829 prefixEnd_509829 232699847645503133682529 := by
  unfold tailWord_509829
  simp only [CollatzResearch.WordTrace]
  refine ⟨18594991269984079706164541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12396660846656053137443027 18594991269984079706164541)
  ·
    refine ⟨6973121726244029889811703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18594991269984079706164541 6973121726244029889811703)
    ·
      refine ⟨10459682589366044834717555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6973121726244029889811703 10459682589366044834717555)
      ·
        refine ⟨15689523884049067252076333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10459682589366044834717555 15689523884049067252076333)
        ·
          refine ⟨5883571456518400219528625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15689523884049067252076333 5883571456518400219528625)
          ·
            refine ⟨4412678592388800164646469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5883571456518400219528625 4412678592388800164646469)
            ·
              refine ⟨827377236072900030871213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4412678592388800164646469 827377236072900030871213)
              ·
                refine ⟨310266463527337511576705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 827377236072900030871213 310266463527337511576705)
                ·
                  refine ⟨232699847645503133682529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310266463527337511576705 232699847645503133682529)
                  ·
                    rfl

theorem cell20_509829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_509829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509829 prefixEnd_509829 := by exact prefixLift 509829
  have htrace : WordTrace (prefixWord ++ tailWord_509829) baseStart_509829 baseEnd_509829 := by
    simpa [prefixWord, tailWord_509829, baseEnd_509829] using wordTrace_append hprefix tailTrace_509829
  have hstable : (prefixWord ++ tailWord_509829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509829).length < 2 ^ (prefixWord ++ tailWord_509829).sum := by decide
  have hdescent : baseEnd_509829 < baseStart_509829 := by decide
  rcases family_descends (prefixWord ++ tailWord_509829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509833 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 6]
def baseStart_509833 : Nat := 118140960795 + 509833 * 2 ^ 59
def prefixEnd_509833 : Nat := 4983230072969 + 3 ^ 40 * 509833 * 2
def baseEnd_509833 : Nat := 232701673354496897549179

theorem tailTrace_509833 : CollatzResearch.WordTrace tailWord_509833 prefixEnd_509833 232701673354496897549179 := by
  unfold tailWord_509833
  simp only [CollatzResearch.WordTrace]
  refine ⟨18595137161969588389310153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12396758107979725592873435 18595137161969588389310153)
  ·
    refine ⟨13946352871477191291982615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18595137161969588389310153 13946352871477191291982615)
    ·
      refine ⟨20919529307215786937973923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13946352871477191291982615 20919529307215786937973923)
      ·
        refine ⟨31379293960823680406960885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20919529307215786937973923 31379293960823680406960885)
        ·
          refine ⟨2941808808827220038152583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31379293960823680406960885 2941808808827220038152583)
          ·
            refine ⟨4412713213240830057228875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2941808808827220038152583 4412713213240830057228875)
            ·
              refine ⟨6619069819861245085843313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4412713213240830057228875 6619069819861245085843313)
              ·
                refine ⟨4964302364895933814382485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6619069819861245085843313 4964302364895933814382485)
                ·
                  refine ⟨232701673354496897549179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4964302364895933814382485 232701673354496897549179)
                  ·
                    rfl

theorem cell20_509833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_509833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509833 prefixEnd_509833 := by exact prefixLift 509833
  have htrace : WordTrace (prefixWord ++ tailWord_509833) baseStart_509833 baseEnd_509833 := by
    simpa [prefixWord, tailWord_509833, baseEnd_509833] using wordTrace_append hprefix tailTrace_509833
  have hstable : (prefixWord ++ tailWord_509833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509833).length < 2 ^ (prefixWord ++ tailWord_509833).sum := by decide
  have hdescent : baseEnd_509833 < baseStart_509833 := by decide
  rcases family_descends (prefixWord ++ tailWord_509833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509850 : List Nat := [3, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_509850 : Nat := 118140960795 + 509850 * 2 ^ 59
def prefixEnd_509850 : Nat := 4983230072969 + 3 ^ 40 * 509850 * 2
def baseEnd_509850 : Nat := 232709432617720393982443

theorem tailTrace_509850 : CollatzResearch.WordTrace tailWord_509850 prefixEnd_509850 232709432617720393982443 := by
  unfold tailWord_509850
  simp only [CollatzResearch.WordTrace]
  refine ⟨4648939300727000073169751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12397171468605333528452669 4648939300727000073169751)
  ·
    refine ⟨6973408951090500109754627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4648939300727000073169751 6973408951090500109754627)
    ·
      refine ⟨10460113426635750164631941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6973408951090500109754627 10460113426635750164631941)
      ·
        refine ⟨1961271267494203155868489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10460113426635750164631941 1961271267494203155868489)
        ·
          refine ⟨1470953450620652366901367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1961271267494203155868489 1470953450620652366901367)
          ·
            refine ⟨2206430175930978550352051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470953450620652366901367 2206430175930978550352051)
            ·
              refine ⟨3309645263896467825528077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206430175930978550352051 3309645263896467825528077)
              ·
                refine ⟨1241116973961175434573029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3309645263896467825528077 1241116973961175434573029)
                ·
                  refine ⟨232709432617720393982443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1241116973961175434573029 232709432617720393982443)
                  ·
                    rfl

theorem cell20_509850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_509850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509850 prefixEnd_509850 := by exact prefixLift 509850
  have htrace : WordTrace (prefixWord ++ tailWord_509850) baseStart_509850 baseEnd_509850 := by
    simpa [prefixWord, tailWord_509850, baseEnd_509850] using wordTrace_append hprefix tailTrace_509850
  have hstable : (prefixWord ++ tailWord_509850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509850).length < 2 ^ (prefixWord ++ tailWord_509850).sum := by decide
  have hdescent : baseEnd_509850 < baseStart_509850 := by decide
  rcases family_descends (prefixWord ++ tailWord_509850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509860 : List Nat := [2, 3, 1, 2, 1, 4, 3, 1, 3]
def baseStart_509860 : Nat := 118140960795 + 509860 * 2 ^ 59
def prefixEnd_509860 : Nat := 4983230072969 + 3 ^ 40 * 509860 * 2
def baseEnd_509860 : Nat := 232713996890204803649069

theorem tailTrace_509860 : CollatzResearch.WordTrace tailWord_509860 prefixEnd_509860 232713996890204803649069 := by
  unfold tailWord_509860
  simp only [CollatzResearch.WordTrace]
  refine ⟨9298060966435886000271517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12397414621914514667028689 9298060966435886000271517)
  ·
    refine ⟨3486772862413457250101819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9298060966435886000271517 3486772862413457250101819)
    ·
      refine ⟨5230159293620185875152729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3486772862413457250101819 5230159293620185875152729)
      ·
        refine ⟨3922619470215139406364547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5230159293620185875152729 3922619470215139406364547)
        ·
          refine ⟨5883929205322709109546821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3922619470215139406364547 5883929205322709109546821)
          ·
            refine ⟨1103236725998007958040029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5883929205322709109546821 1103236725998007958040029)
            ·
              refine ⟨413713772249252984265011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1103236725998007958040029 413713772249252984265011)
              ·
                refine ⟨620570658373879476397517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413713772249252984265011 620570658373879476397517)
                ·
                  refine ⟨232713996890204803649069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620570658373879476397517 232713996890204803649069)
                  ·
                    rfl

theorem cell20_509860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_509860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509860 prefixEnd_509860 := by exact prefixLift 509860
  have htrace : WordTrace (prefixWord ++ tailWord_509860) baseStart_509860 baseEnd_509860 := by
    simpa [prefixWord, tailWord_509860, baseEnd_509860] using wordTrace_append hprefix tailTrace_509860
  have hstable : (prefixWord ++ tailWord_509860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509860).length < 2 ^ (prefixWord ++ tailWord_509860).sum := by decide
  have hdescent : baseEnd_509860 < baseStart_509860 := by decide
  rcases family_descends (prefixWord ++ tailWord_509860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509870 : List Nat := [4, 1, 5, 1, 1, 1, 1, 6]
def baseStart_509870 : Nat := 118140960795 + 509870 * 2 ^ 59
def prefixEnd_509870 : Nat := 4983230072969 + 3 ^ 40 * 509870 * 2
def baseEnd_509870 : Nat := 77572853720896404438565

theorem tailTrace_509870 : CollatzResearch.WordTrace tailWord_509870 prefixEnd_509870 77572853720896404438565 := by
  unfold tailWord_509870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2324560832854442963550883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12397657775223695805604709 2324560832854442963550883)
  ·
    refine ⟨3486841249281664445326325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2324560832854442963550883 3486841249281664445326325)
    ·
      refine ⟨326891367120156041749343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3486841249281664445326325 326891367120156041749343)
      ·
        refine ⟨490337050680234062624015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 326891367120156041749343 490337050680234062624015)
        ·
          refine ⟨735505576020351093936023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490337050680234062624015 735505576020351093936023)
          ·
            refine ⟨1103258364030526640904035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735505576020351093936023 1103258364030526640904035)
            ·
              refine ⟨1654887546045789961356053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103258364030526640904035 1654887546045789961356053)
              ·
                refine ⟨77572853720896404438565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1654887546045789961356053 77572853720896404438565)
                ·
                  rfl

theorem cell20_509870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_509870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509870 prefixEnd_509870 := by exact prefixLift 509870
  have htrace : WordTrace (prefixWord ++ tailWord_509870) baseStart_509870 baseEnd_509870 := by
    simpa [prefixWord, tailWord_509870, baseEnd_509870] using wordTrace_append hprefix tailTrace_509870
  have hstable : (prefixWord ++ tailWord_509870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509870).length < 2 ^ (prefixWord ++ tailWord_509870).sum := by decide
  have hdescent : baseEnd_509870 < baseStart_509870 := by decide
  rcases family_descends (prefixWord ++ tailWord_509870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509871 : List Nat := [1, 1, 2, 1, 2, 2, 3, 4, 4]
def baseStart_509871 : Nat := 118140960795 + 509871 * 2 ^ 59
def prefixEnd_509871 : Nat := 4983230072969 + 3 ^ 40 * 509871 * 2
def baseEnd_509871 : Nat := 232719017589937654282357

theorem tailTrace_509871 : CollatzResearch.WordTrace tailWord_509871 prefixEnd_509871 232719017589937654282357 := by
  unfold tailWord_509871
  simp only [CollatzResearch.WordTrace]
  refine ⟨18596523135831920879193467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12397682090554613919462311 18596523135831920879193467)
  ·
    refine ⟨27894784703747881318790201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18596523135831920879193467 27894784703747881318790201)
    ·
      refine ⟨20921088527810910989092651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27894784703747881318790201 20921088527810910989092651)
      ·
        refine ⟨31381632791716366483638977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20921088527810910989092651 31381632791716366483638977)
        ·
          refine ⟨23536224593787274862729233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31381632791716366483638977 23536224593787274862729233)
          ·
            refine ⟨17652168445340456147046925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23536224593787274862729233 17652168445340456147046925)
            ·
              refine ⟨6619563167002671055142597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17652168445340456147046925 6619563167002671055142597)
              ·
                refine ⟨1241168093813000822839237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6619563167002671055142597 1241168093813000822839237)
                ·
                  refine ⟨232719017589937654282357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1241168093813000822839237 232719017589937654282357)
                  ·
                    rfl

theorem cell20_509871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 4].length) (baseStart_509871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509871 prefixEnd_509871 := by exact prefixLift 509871
  have htrace : WordTrace (prefixWord ++ tailWord_509871) baseStart_509871 baseEnd_509871 := by
    simpa [prefixWord, tailWord_509871, baseEnd_509871] using wordTrace_append hprefix tailTrace_509871
  have hstable : (prefixWord ++ tailWord_509871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509871).length < 2 ^ (prefixWord ++ tailWord_509871).sum := by decide
  have hdescent : baseEnd_509871 < baseStart_509871 := by decide
  rcases family_descends (prefixWord ++ tailWord_509871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509902 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_509902 : Nat := 118140960795 + 509902 * 2 ^ 59
def prefixEnd_509902 : Nat := 4983230072969 + 3 ^ 40 * 509902 * 2
def baseEnd_509902 : Nat := 232733166834639324248897

theorem tailTrace_509902 : CollatzResearch.WordTrace tailWord_509902 prefixEnd_509902 232733166834639324248897 := by
  unfold tailWord_509902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2324706724839951646696495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12398435865813075449047973 2324706724839951646696495)
  ·
    refine ⟨3487060087259927470044743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2324706724839951646696495 3487060087259927470044743)
    ·
      refine ⟨5230590130889891205067115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3487060087259927470044743 5230590130889891205067115)
      ·
        refine ⟨7845885196334836807600673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5230590130889891205067115 7845885196334836807600673)
        ·
          refine ⟨5884413897251127605700505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7845885196334836807600673 5884413897251127605700505)
          ·
            refine ⟨4413310422938345704275379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5884413897251127605700505 4413310422938345704275379)
            ·
              refine ⟨6619965634407518556413069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4413310422938345704275379 6619965634407518556413069)
              ·
                refine ⟨2482487112902819458654901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6619965634407518556413069 2482487112902819458654901)
                ·
                  refine ⟨232733166834639324248897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2482487112902819458654901 232733166834639324248897)
                  ·
                    rfl

theorem cell20_509902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_509902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509902 prefixEnd_509902 := by exact prefixLift 509902
  have htrace : WordTrace (prefixWord ++ tailWord_509902) baseStart_509902 baseEnd_509902 := by
    simpa [prefixWord, tailWord_509902, baseEnd_509902] using wordTrace_append hprefix tailTrace_509902
  have hstable : (prefixWord ++ tailWord_509902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509902).length < 2 ^ (prefixWord ++ tailWord_509902).sum := by decide
  have hdescent : baseEnd_509902 < baseStart_509902 := by decide
  rcases family_descends (prefixWord ++ tailWord_509902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509919 : List Nat := [1, 1, 2, 3, 4, 2, 1, 3, 3]
def baseStart_509919 : Nat := 118140960795 + 509919 * 2 ^ 59
def prefixEnd_509919 : Nat := 4983230072969 + 3 ^ 40 * 509919 * 2
def baseEnd_509919 : Nat := 232740926097862820682161

theorem tailTrace_509919 : CollatzResearch.WordTrace tailWord_509919 prefixEnd_509919 232740926097862820682161 := by
  unfold tailWord_509919
  simp only [CollatzResearch.WordTrace]
  refine ⟨18598273839658025076940811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12398849226438683384627207 18598273839658025076940811)
  ·
    refine ⟨27897410759487037615411217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18598273839658025076940811 27897410759487037615411217)
    ·
      refine ⟨20923058069615278211558413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27897410759487037615411217 20923058069615278211558413)
      ·
        refine ⟨7846146776105729329334405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20923058069615278211558413 7846146776105729329334405)
        ·
          refine ⟨1471152520519824249250201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7846146776105729329334405 1471152520519824249250201)
          ·
            refine ⟨1103364390389868186937651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1471152520519824249250201 1103364390389868186937651)
            ·
              refine ⟨1655046585584802280406477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103364390389868186937651 1655046585584802280406477)
              ·
                refine ⟨620642469594300855152429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1655046585584802280406477 620642469594300855152429)
                ·
                  refine ⟨232740926097862820682161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620642469594300855152429 232740926097862820682161)
                  ·
                    rfl

theorem cell20_509919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 3, 3].length) (baseStart_509919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509919 prefixEnd_509919 := by exact prefixLift 509919
  have htrace : WordTrace (prefixWord ++ tailWord_509919) baseStart_509919 baseEnd_509919 := by
    simpa [prefixWord, tailWord_509919, baseEnd_509919] using wordTrace_append hprefix tailTrace_509919
  have hstable : (prefixWord ++ tailWord_509919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509919).length < 2 ^ (prefixWord ++ tailWord_509919).sum := by decide
  have hdescent : baseEnd_509919 < baseStart_509919 := by decide
  rcases family_descends (prefixWord ++ tailWord_509919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509956 : List Nat := [2, 3, 2, 4, 1, 2, 2, 2, 2]
def baseStart_509956 : Nat := 118140960795 + 509956 * 2 ^ 59
def prefixEnd_509956 : Nat := 4983230072969 + 3 ^ 40 * 509956 * 2
def baseEnd_509956 : Nat := 232757813906055136448677

theorem tailTrace_509956 : CollatzResearch.WordTrace tailWord_509956 prefixEnd_509956 232757813906055136448677 := by
  unfold tailWord_509956
  simp only [CollatzResearch.WordTrace]
  refine ⟨9299811670261990198018861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12399748893682653597358481 9299811670261990198018861)
  ·
    refine ⟨3487429376348246324257073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9299811670261990198018861 3487429376348246324257073)
    ·
      refine ⟨2615572032261184743192805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3487429376348246324257073 2615572032261184743192805)
      ·
        refine ⟨490419756048972139348651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2615572032261184743192805 490419756048972139348651)
        ·
          refine ⟨735629634073458209022977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490419756048972139348651 735629634073458209022977)
          ·
            refine ⟨551722225555093656767233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 735629634073458209022977 551722225555093656767233)
            ·
              refine ⟨413791669166320242575425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 551722225555093656767233 413791669166320242575425)
              ·
                refine ⟨310343751874740181931569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413791669166320242575425 310343751874740181931569)
                ·
                  refine ⟨232757813906055136448677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310343751874740181931569 232757813906055136448677)
                  ·
                    rfl

theorem cell20_509956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_509956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509956 prefixEnd_509956 := by exact prefixLift 509956
  have htrace : WordTrace (prefixWord ++ tailWord_509956) baseStart_509956 baseEnd_509956 := by
    simpa [prefixWord, tailWord_509956, baseEnd_509956] using wordTrace_append hprefix tailTrace_509956
  have hstable : (prefixWord ++ tailWord_509956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509956).length < 2 ^ (prefixWord ++ tailWord_509956).sum := by decide
  have hdescent : baseEnd_509956 < baseStart_509956 := by decide
  rcases family_descends (prefixWord ++ tailWord_509956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509957 : List Nat := [1, 3, 1, 1, 2, 5, 2, 2, 3]
def baseStart_509957 : Nat := 118140960795 + 509957 * 2 ^ 59
def prefixEnd_509957 : Nat := 4983230072969 + 3 ^ 40 * 509957 * 2
def baseEnd_509957 : Nat := 232758270333303577415339

theorem tailTrace_509957 : CollatzResearch.WordTrace tailWord_509957 prefixEnd_509957 232758270333303577415339 := by
  unfold tailWord_509957
  simp only [CollatzResearch.WordTrace]
  refine ⟨18599659813520357566824125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12399773209013571711216083 18599659813520357566824125)
  ·
    refine ⟨6974872430070134087559047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18599659813520357566824125 6974872430070134087559047)
    ·
      refine ⟨10462308645105201131338571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6974872430070134087559047 10462308645105201131338571)
      ·
        refine ⟨15693462967657801697007857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10462308645105201131338571 15693462967657801697007857)
        ·
          refine ⟨11770097225743351272755893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15693462967657801697007857 11770097225743351272755893)
          ·
            refine ⟨1103446614913439181820865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11770097225743351272755893 1103446614913439181820865)
            ·
              refine ⟨827584961185079386365649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103446614913439181820865 827584961185079386365649)
              ·
                refine ⟨620688720888809539774237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827584961185079386365649 620688720888809539774237)
                ·
                  refine ⟨232758270333303577415339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620688720888809539774237 232758270333303577415339)
                  ·
                    rfl

theorem cell20_509957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 3].length) (baseStart_509957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509957 prefixEnd_509957 := by exact prefixLift 509957
  have htrace : WordTrace (prefixWord ++ tailWord_509957) baseStart_509957 baseEnd_509957 := by
    simpa [prefixWord, tailWord_509957, baseEnd_509957] using wordTrace_append hprefix tailTrace_509957
  have hstable : (prefixWord ++ tailWord_509957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509957).length < 2 ^ (prefixWord ++ tailWord_509957).sum := by decide
  have hdescent : baseEnd_509957 < baseStart_509957 := by decide
  rcases family_descends (prefixWord ++ tailWord_509957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_509998 : List Nat := [4, 1, 3, 1, 1, 3, 2, 3, 2]
def baseStart_509998 : Nat := 118140960795 + 509998 * 2 ^ 59
def prefixEnd_509998 : Nat := 4983230072969 + 3 ^ 40 * 509998 * 2
def baseEnd_509998 : Nat := 232776983850489657048505

theorem tailTrace_509998 : CollatzResearch.WordTrace tailWord_509998 prefixEnd_509998 232776983850489657048505 := by
  unfold tailWord_509998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2325144400796477696133331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12400770137581214379377765 2325144400796477696133331)
  ·
    refine ⟨3487716601194716544199997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2325144400796477696133331 3487716601194716544199997)
    ·
      refine ⟨1307893725448018704074999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3487716601194716544199997 1307893725448018704074999)
      ·
        refine ⟨1961840588172028056112499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1307893725448018704074999 1961840588172028056112499)
        ·
          refine ⟨2942760882258042084168749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1961840588172028056112499 2942760882258042084168749)
          ·
            refine ⟨1103535330846765781563281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2942760882258042084168749 1103535330846765781563281)
            ·
              refine ⟨827651498135074336172461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103535330846765781563281 827651498135074336172461)
              ·
                refine ⟨310369311800652876064673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 827651498135074336172461 310369311800652876064673)
                ·
                  refine ⟨232776983850489657048505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310369311800652876064673 232776983850489657048505)
                  ·
                    rfl

theorem cell20_509998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_509998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_509998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_509998 prefixEnd_509998 := by exact prefixLift 509998
  have htrace : WordTrace (prefixWord ++ tailWord_509998) baseStart_509998 baseEnd_509998 := by
    simpa [prefixWord, tailWord_509998, baseEnd_509998] using wordTrace_append hprefix tailTrace_509998
  have hstable : (prefixWord ++ tailWord_509998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_509998).length < 2 ^ (prefixWord ++ tailWord_509998).sum := by decide
  have hdescent : baseEnd_509998 < baseStart_509998 := by decide
  rcases family_descends (prefixWord ++ tailWord_509998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510009 : List Nat := [1, 2, 1, 5, 3, 1, 7]
def baseStart_510009 : Nat := 118140960795 + 510009 * 2 ^ 59
def prefixEnd_510009 : Nat := 4983230072969 + 3 ^ 40 * 510009 * 2
def baseEnd_510009 : Nat := 25864667172246945297977

theorem tailTrace_510009 : CollatzResearch.WordTrace tailWord_510009 prefixEnd_510009 25864667172246945297977 := by
  unfold tailWord_510009
  simp only [CollatzResearch.WordTrace]
  refine ⟨18601556409331970447717081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12401037606221313631811387 18601556409331970447717081)
  ·
    refine ⟨13951167306998977835787811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18601556409331970447717081 13951167306998977835787811)
    ·
      refine ⟨20926750960498466753681717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13951167306998977835787811 20926750960498466753681717)
      ·
        refine ⟨1961882902546731258157661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20926750960498466753681717 1961882902546731258157661)
        ·
          refine ⟨735706088455024221809123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1961882902546731258157661 735706088455024221809123)
          ·
            refine ⟨1103559132682536332713685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735706088455024221809123 1103559132682536332713685)
            ·
              refine ⟨25864667172246945297977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1103559132682536332713685 25864667172246945297977)
              ·
                rfl

theorem cell20_510009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 7].length) (baseStart_510009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510009 prefixEnd_510009 := by exact prefixLift 510009
  have htrace : WordTrace (prefixWord ++ tailWord_510009) baseStart_510009 baseEnd_510009 := by
    simpa [prefixWord, tailWord_510009, baseEnd_510009] using wordTrace_append hprefix tailTrace_510009
  have hstable : (prefixWord ++ tailWord_510009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510009).length < 2 ^ (prefixWord ++ tailWord_510009).sum := by decide
  have hdescent : baseEnd_510009 < baseStart_510009 := by decide
  rcases family_descends (prefixWord ++ tailWord_510009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510016 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 5]
def baseStart_510016 : Nat := 118140960795 + 510016 * 2 ^ 59
def prefixEnd_510016 : Nat := 4983230072969 + 3 ^ 40 * 510016 * 2
def baseEnd_510016 : Nat := 232785199540961594448431

theorem tailTrace_510016 : CollatzResearch.WordTrace tailWord_510016 prefixEnd_510016 232785199540961594448431 := by
  unfold tailWord_510016
  simp only [CollatzResearch.WordTrace]
  refine ⟨9300905860153305321610951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12401207813537740428814601 9300905860153305321610951)
  ·
    refine ⟨13951358790229957982416427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9300905860153305321610951 13951358790229957982416427)
    ·
      refine ⟨20927038185344936973624641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13951358790229957982416427 20927038185344936973624641)
      ·
        refine ⟨15695278639008702730218481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20927038185344936973624641 15695278639008702730218481)
        ·
          refine ⟨11771458979256527047663861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15695278639008702730218481 11771458979256527047663861)
          ·
            refine ⟨1103574279305299410718487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11771458979256527047663861 1103574279305299410718487)
            ·
              refine ⟨1655361418957949116077731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1103574279305299410718487 1655361418957949116077731)
              ·
                refine ⟨2483042128436923674116597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655361418957949116077731 2483042128436923674116597)
                ·
                  refine ⟨232785199540961594448431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2483042128436923674116597 232785199540961594448431)
                  ·
                    rfl

theorem cell20_510016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_510016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510016 prefixEnd_510016 := by exact prefixLift 510016
  have htrace : WordTrace (prefixWord ++ tailWord_510016) baseStart_510016 baseEnd_510016 := by
    simpa [prefixWord, tailWord_510016, baseEnd_510016] using wordTrace_append hprefix tailTrace_510016
  have hstable : (prefixWord ++ tailWord_510016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510016).length < 2 ^ (prefixWord ++ tailWord_510016).sum := by decide
  have hdescent : baseEnd_510016 < baseStart_510016 := by decide
  rcases family_descends (prefixWord ++ tailWord_510016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510085 : List Nat := [1, 3, 1, 1, 5, 2, 2, 5]
def baseStart_510085 : Nat := 118140960795 + 510085 * 2 ^ 59
def prefixEnd_510085 : Nat := 4983230072969 + 3 ^ 40 * 510085 * 2
def baseEnd_510085 : Nat := 77605564340368007049383

theorem tailTrace_510085 : CollatzResearch.WordTrace tailWord_510085 prefixEnd_510085 77605564340368007049383 := by
  unfold tailWord_510085
  simp only [CollatzResearch.WordTrace]
  refine ⟨18604328357056635427483709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12402885571371090284989139 18604328357056635427483709)
  ·
    refine ⟨6976623133896238285306391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18604328357056635427483709 6976623133896238285306391)
    ·
      refine ⟨10464934700844357427959587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6976623133896238285306391 10464934700844357427959587)
      ·
        refine ⟨15697402051266536141939381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10464934700844357427959587 15697402051266536141939381)
        ·
          refine ⟨1471631442306237763306817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15697402051266536141939381 1471631442306237763306817)
          ·
            refine ⟨1103723581729678322480113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1471631442306237763306817 1103723581729678322480113)
            ·
              refine ⟨827792686297258741860085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103723581729678322480113 827792686297258741860085)
              ·
                refine ⟨77605564340368007049383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 827792686297258741860085 77605564340368007049383)
                ·
                  rfl

theorem cell20_510085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 5].length) (baseStart_510085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510085 prefixEnd_510085 := by exact prefixLift 510085
  have htrace : WordTrace (prefixWord ++ tailWord_510085) baseStart_510085 baseEnd_510085 := by
    simpa [prefixWord, tailWord_510085, baseEnd_510085] using wordTrace_append hprefix tailTrace_510085
  have hstable : (prefixWord ++ tailWord_510085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510085).length < 2 ^ (prefixWord ++ tailWord_510085).sum := by decide
  have hdescent : baseEnd_510085 < baseStart_510085 := by decide
  rcases family_descends (prefixWord ++ tailWord_510085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510088 : List Nat := [2, 1, 3, 4, 1, 1, 4, 1, 3]
def baseStart_510088 : Nat := 118140960795 + 510088 * 2 ^ 59
def prefixEnd_510088 : Nat := 4983230072969 + 3 ^ 40 * 510088 * 2
def baseEnd_510088 : Nat := 232818062302849344048137

theorem tailTrace_510088 : CollatzResearch.WordTrace tailWord_510088 prefixEnd_510088 232818062302849344048137 := by
  unfold tailWord_510088
  simp only [CollatzResearch.WordTrace]
  refine ⟨9302218888022883469921459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12402958517363844626561945 9302218888022883469921459)
  ·
    refine ⟨13953328332034325204882189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9302218888022883469921459 13953328332034325204882189)
    ·
      refine ⟨5232498124512871951830821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13953328332034325204882189 5232498124512871951830821)
      ·
        refine ⟨981093398346163490968279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5232498124512871951830821 981093398346163490968279)
        ·
          refine ⟨1471640097519245236452419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 981093398346163490968279 1471640097519245236452419)
          ·
            refine ⟨2207460146278867854678629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1471640097519245236452419 2207460146278867854678629)
            ·
              refine ⟨413898777427287722752243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2207460146278867854678629 413898777427287722752243)
              ·
                refine ⟨620848166140931584128365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413898777427287722752243 620848166140931584128365)
                ·
                  refine ⟨232818062302849344048137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620848166140931584128365 232818062302849344048137)
                  ·
                    rfl

theorem cell20_510088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 3].length) (baseStart_510088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510088 prefixEnd_510088 := by exact prefixLift 510088
  have htrace : WordTrace (prefixWord ++ tailWord_510088) baseStart_510088 baseEnd_510088 := by
    simpa [prefixWord, tailWord_510088, baseEnd_510088] using wordTrace_append hprefix tailTrace_510088
  have hstable : (prefixWord ++ tailWord_510088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510088).length < 2 ^ (prefixWord ++ tailWord_510088).sum := by decide
  have hdescent : baseEnd_510088 < baseStart_510088 := by decide
  rcases family_descends (prefixWord ++ tailWord_510088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510129 : List Nat := [1, 2, 2, 5, 2, 2, 2, 2, 2]
def baseStart_510129 : Nat := 118140960795 + 510129 * 2 ^ 59
def prefixEnd_510129 : Nat := 4983230072969 + 3 ^ 40 * 510129 * 2
def baseEnd_510129 : Nat := 232836775820035423681303

theorem tailTrace_510129 : CollatzResearch.WordTrace tailWord_510129 prefixEnd_510129 232836775820035423681303 := by
  unfold tailWord_510129
  simp only [CollatzResearch.WordTrace]
  refine ⟨18605933168897230942085441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12403955445931487294723627 18605933168897230942085441)
  ·
    refine ⟨13954449876672923206564081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18605933168897230942085441 13954449876672923206564081)
    ·
      refine ⟨10465837407504692404923061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13954449876672923206564081 10465837407504692404923061)
      ·
        refine ⟨981172256953564912961537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10465837407504692404923061 981172256953564912961537)
        ·
          refine ⟨735879192715173684721153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 981172256953564912961537 735879192715173684721153)
          ·
            refine ⟨551909394536380263540865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 735879192715173684721153 551909394536380263540865)
            ·
              refine ⟨413932045902285197655649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 551909394536380263540865 413932045902285197655649)
              ·
                refine ⟨310449034426713898241737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413932045902285197655649 310449034426713898241737)
                ·
                  refine ⟨232836775820035423681303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310449034426713898241737 232836775820035423681303)
                  ·
                    rfl

theorem cell20_510129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 2].length) (baseStart_510129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510129 prefixEnd_510129 := by exact prefixLift 510129
  have htrace : WordTrace (prefixWord ++ tailWord_510129) baseStart_510129 baseEnd_510129 := by
    simpa [prefixWord, tailWord_510129, baseEnd_510129] using wordTrace_append hprefix tailTrace_510129
  have hstable : (prefixWord ++ tailWord_510129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510129).length < 2 ^ (prefixWord ++ tailWord_510129).sum := by decide
  have hdescent : baseEnd_510129 < baseStart_510129 := by decide
  rcases family_descends (prefixWord ++ tailWord_510129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510137 : List Nat := [1, 2, 1, 4, 1, 2, 2, 3, 4]
def baseStart_510137 : Nat := 118140960795 + 510137 * 2 ^ 59
def prefixEnd_510137 : Nat := 4983230072969 + 3 ^ 40 * 510137 * 2
def baseEnd_510137 : Nat := 232840427238022951414603

theorem tailTrace_510137 : CollatzResearch.WordTrace tailWord_510137 prefixEnd_510137 232840427238022951414603 := by
  unfold tailWord_510137
  simp only [CollatzResearch.WordTrace]
  refine ⟨18606224952868248308376665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12404149968578832205584443 18606224952868248308376665)
  ·
    refine ⟨13954668714651186231282499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18606224952868248308376665 13954668714651186231282499)
    ·
      refine ⟨20932003071976779346923749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13954668714651186231282499 20932003071976779346923749)
      ·
        refine ⟨3924750575995646127548203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20932003071976779346923749 3924750575995646127548203)
        ·
          refine ⟨5887125863993469191322305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3924750575995646127548203 5887125863993469191322305)
          ·
            refine ⟨4415344397995101893491729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5887125863993469191322305 4415344397995101893491729)
            ·
              refine ⟨3311508298496326420118797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4415344397995101893491729 3311508298496326420118797)
              ·
                refine ⟨1241815611936122407544549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3311508298496326420118797 1241815611936122407544549)
                ·
                  refine ⟨232840427238022951414603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1241815611936122407544549 232840427238022951414603)
                  ·
                    rfl

theorem cell20_510137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_510137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510137 prefixEnd_510137 := by exact prefixLift 510137
  have htrace : WordTrace (prefixWord ++ tailWord_510137) baseStart_510137 baseEnd_510137 := by
    simpa [prefixWord, tailWord_510137, baseEnd_510137] using wordTrace_append hprefix tailTrace_510137
  have hstable : (prefixWord ++ tailWord_510137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510137).length < 2 ^ (prefixWord ++ tailWord_510137).sum := by decide
  have hdescent : baseEnd_510137 < baseStart_510137 := by decide
  rcases family_descends (prefixWord ++ tailWord_510137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510140 : List Nat := [2, 2, 2, 3, 3, 2, 1, 5]
def baseStart_510140 : Nat := 118140960795 + 510140 * 2 ^ 59
def prefixEnd_510140 : Nat := 4983230072969 + 3 ^ 40 * 510140 * 2
def baseEnd_510140 : Nat := 77613932173256091438197

theorem tailTrace_510140 : CollatzResearch.WordTrace tailWord_510140 prefixEnd_510140 77613932173256091438197 := by
  unfold tailWord_510140
  simp only [CollatzResearch.WordTrace]
  refine ⟨9303167185928689910367937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12404222914571586547157249 9303167185928689910367937)
  ·
    refine ⟨6977375389446517432775953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9303167185928689910367937 6977375389446517432775953)
    ·
      refine ⟨5233031542084888074581965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6977375389446517432775953 5233031542084888074581965)
      ·
        refine ⟨1962386828281833027968237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5233031542084888074581965 1962386828281833027968237)
        ·
          refine ⟨735895060605687385488089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1962386828281833027968237 735895060605687385488089)
          ·
            refine ⟨551921295454265539116067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 735895060605687385488089 551921295454265539116067)
            ·
              refine ⟨827881943181398308674101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 551921295454265539116067 827881943181398308674101)
              ·
                refine ⟨77613932173256091438197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 827881943181398308674101 77613932173256091438197)
                ·
                  rfl

theorem cell20_510140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 5].length) (baseStart_510140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510140 prefixEnd_510140 := by exact prefixLift 510140
  have htrace : WordTrace (prefixWord ++ tailWord_510140) baseStart_510140 baseEnd_510140 := by
    simpa [prefixWord, tailWord_510140, baseEnd_510140] using wordTrace_append hprefix tailTrace_510140
  have hstable : (prefixWord ++ tailWord_510140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510140).length < 2 ^ (prefixWord ++ tailWord_510140).sum := by decide
  have hdescent : baseEnd_510140 < baseStart_510140 := by decide
  rcases family_descends (prefixWord ++ tailWord_510140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510151 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 9]
def baseStart_510151 : Nat := 118140960795 + 510151 * 2 ^ 59
def prefixEnd_510151 : Nat := 4983230072969 + 3 ^ 40 * 510151 * 2
def baseEnd_510151 : Nat := 232846817219501124947879

theorem tailTrace_510151 : CollatzResearch.WordTrace tailWord_510151 prefixEnd_510151 232846817219501124947879 := by
  unfold tailWord_510151
  simp only [CollatzResearch.WordTrace]
  refine ⟨18606735574817528699386307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12404490383211685799590871 18606735574817528699386307)
  ·
    refine ⟨27910103362226293049079461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18606735574817528699386307 27910103362226293049079461)
    ·
      refine ⟨5233144380417429946702399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27910103362226293049079461 5233144380417429946702399)
      ·
        refine ⟨7849716570626144920053599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5233144380417429946702399 7849716570626144920053599)
        ·
          refine ⟨11774574855939217380080399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7849716570626144920053599 11774574855939217380080399)
          ·
            refine ⟨17661862283908826070120599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11774574855939217380080399 17661862283908826070120599)
            ·
              refine ⟨26492793425863239105180899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17661862283908826070120599 26492793425863239105180899)
              ·
                refine ⟨39739190138794858657771349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26492793425863239105180899 39739190138794858657771349)
                ·
                  refine ⟨232846817219501124947879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39739190138794858657771349 232846817219501124947879)
                  ·
                    rfl

theorem cell20_510151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_510151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510151 prefixEnd_510151 := by exact prefixLift 510151
  have htrace : WordTrace (prefixWord ++ tailWord_510151) baseStart_510151 baseEnd_510151 := by
    simpa [prefixWord, tailWord_510151, baseEnd_510151] using wordTrace_append hprefix tailTrace_510151
  have hstable : (prefixWord ++ tailWord_510151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510151).length < 2 ^ (prefixWord ++ tailWord_510151).sum := by decide
  have hdescent : baseEnd_510151 < baseStart_510151 := by decide
  rcases family_descends (prefixWord ++ tailWord_510151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510216 : List Nat := [2, 1, 3, 2, 3, 3, 2, 4]
def baseStart_510216 : Nat := 118140960795 + 510216 * 2 ^ 59
def prefixEnd_510216 : Nat := 4983230072969 + 3 ^ 40 * 510216 * 2
def baseEnd_510216 : Nat := 77625494996883262593649

theorem tailTrace_510216 : CollatzResearch.WordTrace tailWord_510216 prefixEnd_510216 77625494996883262593649 := by
  unfold tailWord_510216
  simp only [CollatzResearch.WordTrace]
  refine ⟨9304553159791022400251251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12406070879721363200335001 9304553159791022400251251)
  ·
    refine ⟨13956829739686533600376877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9304553159791022400251251 13956829739686533600376877)
    ·
      refine ⟨5233811152382450100141329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13956829739686533600376877 5233811152382450100141329)
      ·
        refine ⟨3925358364286837575105997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5233811152382450100141329 3925358364286837575105997)
        ·
          refine ⟨1472009386607564090664749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3925358364286837575105997 1472009386607564090664749)
          ·
            refine ⟨552003519977836533999281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1472009386607564090664749 552003519977836533999281)
            ·
              refine ⟨414002639983377400499461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552003519977836533999281 414002639983377400499461)
              ·
                refine ⟨77625494996883262593649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 414002639983377400499461 77625494996883262593649)
                ·
                  rfl

theorem cell20_510216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 4].length) (baseStart_510216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510216 prefixEnd_510216 := by exact prefixLift 510216
  have htrace : WordTrace (prefixWord ++ tailWord_510216) baseStart_510216 baseEnd_510216 := by
    simpa [prefixWord, tailWord_510216, baseEnd_510216] using wordTrace_append hprefix tailTrace_510216
  have hstable : (prefixWord ++ tailWord_510216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510216).length < 2 ^ (prefixWord ++ tailWord_510216).sum := by decide
  have hdescent : baseEnd_510216 < baseStart_510216 := by decide
  rcases family_descends (prefixWord ++ tailWord_510216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510220 : List Nat := [2, 2, 1, 2, 2, 2, 3, 6]
def baseStart_510220 : Nat := 118140960795 + 510220 * 2 ^ 59
def prefixEnd_510220 : Nat := 4983230072969 + 3 ^ 40 * 510220 * 2
def baseEnd_510220 : Nat := 77626103566547850549199

theorem tailTrace_510220 : CollatzResearch.WordTrace tailWord_510220 prefixEnd_510220 77626103566547850549199 := by
  unfold tailWord_510220
  simp only [CollatzResearch.WordTrace]
  refine ⟨9304626105783776741824057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12406168141045035655765409 9304626105783776741824057)
  ·
    refine ⟨6978469579337832556368043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9304626105783776741824057 6978469579337832556368043)
    ·
      refine ⟨10467704369006748834552065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6978469579337832556368043 10467704369006748834552065)
      ·
        refine ⟨7850778276755061625914049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10467704369006748834552065 7850778276755061625914049)
        ·
          refine ⟨5888083707566296219435537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7850778276755061625914049 5888083707566296219435537)
          ·
            refine ⟨4416062780674722164576653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5888083707566296219435537 4416062780674722164576653)
            ·
              refine ⟨1656023542753020811716245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4416062780674722164576653 1656023542753020811716245)
              ·
                refine ⟨77626103566547850549199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1656023542753020811716245 77626103566547850549199)
                ·
                  rfl

theorem cell20_510220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_510220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510220 prefixEnd_510220 := by exact prefixLift 510220
  have htrace : WordTrace (prefixWord ++ tailWord_510220) baseStart_510220 baseEnd_510220 := by
    simpa [prefixWord, tailWord_510220, baseEnd_510220] using wordTrace_append hprefix tailTrace_510220
  have hstable : (prefixWord ++ tailWord_510220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510220).length < 2 ^ (prefixWord ++ tailWord_510220).sum := by decide
  have hdescent : baseEnd_510220 < baseStart_510220 := by decide
  rcases family_descends (prefixWord ++ tailWord_510220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510244 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 5]
def baseStart_510244 : Nat := 118140960795 + 510244 * 2 ^ 59
def prefixEnd_510244 : Nat := 4983230072969 + 3 ^ 40 * 510244 * 2
def baseEnd_510244 : Nat := 232889264953606134847499

theorem tailTrace_510244 : CollatzResearch.WordTrace tailWord_510244 prefixEnd_510244 232889264953606134847499 := by
  unfold tailWord_510244
  simp only [CollatzResearch.WordTrace]
  refine ⟨9305063781740302791260893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12406751708987070388347857 9305063781740302791260893)
  ·
    refine ⟨3489398918152613546722835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9305063781740302791260893 3489398918152613546722835)
    ·
      refine ⟨5234098377228920320084253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3489398918152613546722835 5234098377228920320084253)
      ·
        refine ⟨1962786891460845120031595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5234098377228920320084253 1962786891460845120031595)
        ·
          refine ⟨2944180337191267680047393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1962786891460845120031595 2944180337191267680047393)
          ·
            refine ⟨2208135252893450760035545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2944180337191267680047393 2208135252893450760035545)
            ·
              refine ⟨1656101439670088070026659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2208135252893450760035545 1656101439670088070026659)
              ·
                refine ⟨2484152159505132105039989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1656101439670088070026659 2484152159505132105039989)
                ·
                  refine ⟨232889264953606134847499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2484152159505132105039989 232889264953606134847499)
                  ·
                    rfl

theorem cell20_510244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_510244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510244 prefixEnd_510244 := by exact prefixLift 510244
  have htrace : WordTrace (prefixWord ++ tailWord_510244) baseStart_510244 baseEnd_510244 := by
    simpa [prefixWord, tailWord_510244, baseEnd_510244] using wordTrace_append hprefix tailTrace_510244
  have hstable : (prefixWord ++ tailWord_510244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510244).length < 2 ^ (prefixWord ++ tailWord_510244).sum := by decide
  have hdescent : baseEnd_510244 < baseStart_510244 := by decide
  rcases family_descends (prefixWord ++ tailWord_510244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510257 : List Nat := [1, 2, 2, 3, 5, 1, 2, 1, 3]
def baseStart_510257 : Nat := 118140960795 + 510257 * 2 ^ 59
def prefixEnd_510257 : Nat := 4983230072969 + 3 ^ 40 * 510257 * 2
def baseEnd_510257 : Nat := 232895198507835867414113

theorem tailTrace_510257 : CollatzResearch.WordTrace tailWord_510257 prefixEnd_510257 232895198507835867414113 := by
  unfold tailWord_510257
  simp only [CollatzResearch.WordTrace]
  refine ⟨18610601712433508802745025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12407067808289005868496683 18610601712433508802745025)
  ·
    refine ⟨13957951284325131602058769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18610601712433508802745025 13957951284325131602058769)
    ·
      refine ⟨10468463463243848701544077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13957951284325131602058769 10468463463243848701544077)
      ·
        refine ⟨3925673798716443263079029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10468463463243848701544077 3925673798716443263079029)
        ·
          refine ⟨368031918629666555913659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3925673798716443263079029 368031918629666555913659)
          ·
            refine ⟨552047877944499833870489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368031918629666555913659 552047877944499833870489)
            ·
              refine ⟨414035908458374875402867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552047877944499833870489 414035908458374875402867)
              ·
                refine ⟨621053862687562313104301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414035908458374875402867 621053862687562313104301)
                ·
                  refine ⟨232895198507835867414113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 621053862687562313104301 232895198507835867414113)
                  ·
                    rfl

theorem cell20_510257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 2, 1, 3].length) (baseStart_510257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510257 prefixEnd_510257 := by exact prefixLift 510257
  have htrace : WordTrace (prefixWord ++ tailWord_510257) baseStart_510257 baseEnd_510257 := by
    simpa [prefixWord, tailWord_510257, baseEnd_510257] using wordTrace_append hprefix tailTrace_510257
  have hstable : (prefixWord ++ tailWord_510257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510257).length < 2 ^ (prefixWord ++ tailWord_510257).sum := by decide
  have hdescent : baseEnd_510257 < baseStart_510257 := by decide
  rcases family_descends (prefixWord ++ tailWord_510257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510303 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 5]
def baseStart_510303 : Nat := 118140960795 + 510303 * 2 ^ 59
def prefixEnd_510303 : Nat := 4983230072969 + 3 ^ 40 * 510303 * 2
def baseEnd_510303 : Nat := 232916194161264151880591

theorem tailTrace_510303 : CollatzResearch.WordTrace tailWord_510303 prefixEnd_510303 232916194161264151880591 := by
  unfold tailWord_510303
  simp only [CollatzResearch.WordTrace]
  refine ⟨18612279470266858658919563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12408186313511239105946375 18612279470266858658919563)
  ·
    refine ⟨27918419205400287988379345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18612279470266858658919563 27918419205400287988379345)
    ·
      refine ⟨20938814404050215991284509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27918419205400287988379345 20938814404050215991284509)
      ·
        refine ⟨7852055401518830996731691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20938814404050215991284509 7852055401518830996731691)
        ·
          refine ⟨11778083102278246495097537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7852055401518830996731691 11778083102278246495097537)
          ·
            refine ⟨8833562326708684871323153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11778083102278246495097537 8833562326708684871323153)
            ·
              refine ⟨6625171745031513653492365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8833562326708684871323153 6625171745031513653492365)
              ·
                refine ⟨2484439404386817620059637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6625171745031513653492365 2484439404386817620059637)
                ·
                  refine ⟨232916194161264151880591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2484439404386817620059637 232916194161264151880591)
                  ·
                    rfl

theorem cell20_510303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_510303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510303 prefixEnd_510303 := by exact prefixLift 510303
  have htrace : WordTrace (prefixWord ++ tailWord_510303) baseStart_510303 baseEnd_510303 := by
    simpa [prefixWord, tailWord_510303, baseEnd_510303] using wordTrace_append hprefix tailTrace_510303
  have hstable : (prefixWord ++ tailWord_510303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510303).length < 2 ^ (prefixWord ++ tailWord_510303).sum := by decide
  have hdescent : baseEnd_510303 < baseStart_510303 := by decide
  rcases family_descends (prefixWord ++ tailWord_510303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510320 : List Nat := [2, 1, 1, 1, 4, 3, 2, 3, 3]
def baseStart_510320 : Nat := 118140960795 + 510320 * 2 ^ 59
def prefixEnd_510320 : Nat := 4983230072969 + 3 ^ 40 * 510320 * 2
def baseEnd_510320 : Nat := 232923953424487648313855

theorem tailTrace_510320 : CollatzResearch.WordTrace tailWord_510320 prefixEnd_510320 232923953424487648313855 := by
  unfold tailWord_510320
  simp only [CollatzResearch.WordTrace]
  refine ⟨9306449755602635281144207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12408599674136847041525609 9306449755602635281144207)
  ·
    refine ⟨13959674633403952921716311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9306449755602635281144207 13959674633403952921716311)
    ·
      refine ⟨20939511950105929382574467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13959674633403952921716311 20939511950105929382574467)
      ·
        refine ⟨31409267925158894073861701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20939511950105929382574467 31409267925158894073861701)
        ·
          refine ⟨5889237735967292638849069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31409267925158894073861701 5889237735967292638849069)
          ·
            refine ⟨2208464150987734739568401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5889237735967292638849069 2208464150987734739568401)
            ·
              refine ⟨1656348113240801054676301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2208464150987734739568401 1656348113240801054676301)
              ·
                refine ⟨621130542465300395503613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1656348113240801054676301 621130542465300395503613)
                ·
                  refine ⟨232923953424487648313855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 621130542465300395503613 232923953424487648313855)
                  ·
                    rfl

theorem cell20_510320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_510320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510320 prefixEnd_510320 := by exact prefixLift 510320
  have htrace : WordTrace (prefixWord ++ tailWord_510320) baseStart_510320 baseEnd_510320 := by
    simpa [prefixWord, tailWord_510320, baseEnd_510320] using wordTrace_append hprefix tailTrace_510320
  have hstable : (prefixWord ++ tailWord_510320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510320).length < 2 ^ (prefixWord ++ tailWord_510320).sum := by decide
  have hdescent : baseEnd_510320 < baseStart_510320 := by decide
  rcases family_descends (prefixWord ++ tailWord_510320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510341 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 5]
def baseStart_510341 : Nat := 118140960795 + 510341 * 2 ^ 59
def prefixEnd_510341 : Nat := 4983230072969 + 3 ^ 40 * 510341 * 2
def baseEnd_510341 : Nat := 232933538396704908613769

theorem tailTrace_510341 : CollatzResearch.WordTrace tailWord_510341 prefixEnd_510341 232933538396704908613769 := by
  unfold tailWord_510341
  simp only [CollatzResearch.WordTrace]
  refine ⟨18613665444129191148802877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12409110296086127432535251 18613665444129191148802877)
  ·
    refine ⟨6980124541548446680801079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18613665444129191148802877 6980124541548446680801079)
    ·
      refine ⟨10470186812322670021201619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6980124541548446680801079 10470186812322670021201619)
      ·
        refine ⟨15705280218484005031802429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10470186812322670021201619 15705280218484005031802429)
        ·
          refine ⟨5889480081931501886925911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15705280218484005031802429 5889480081931501886925911)
          ·
            refine ⟨8834220122897252830388867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5889480081931501886925911 8834220122897252830388867)
            ·
              refine ⟨13251330184345879245583301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8834220122897252830388867 13251330184345879245583301)
              ·
                refine ⟨2484624409564852358546869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13251330184345879245583301 2484624409564852358546869)
                ·
                  refine ⟨232933538396704908613769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2484624409564852358546869 232933538396704908613769)
                  ·
                    rfl

theorem cell20_510341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_510341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510341 prefixEnd_510341 := by exact prefixLift 510341
  have htrace : WordTrace (prefixWord ++ tailWord_510341) baseStart_510341 baseEnd_510341 := by
    simpa [prefixWord, tailWord_510341, baseEnd_510341] using wordTrace_append hprefix tailTrace_510341
  have hstable : (prefixWord ++ tailWord_510341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510341).length < 2 ^ (prefixWord ++ tailWord_510341).sum := by decide
  have hdescent : baseEnd_510341 < baseStart_510341 := by decide
  rcases family_descends (prefixWord ++ tailWord_510341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510389 : List Nat := [1, 3, 3, 2, 3, 1, 1, 6]
def baseStart_510389 : Nat := 118140960795 + 510389 * 2 ^ 59
def prefixEnd_510389 : Nat := 4983230072969 + 3 ^ 40 * 510389 * 2
def baseEnd_510389 : Nat := 77651815634876691671191

theorem tailTrace_510389 : CollatzResearch.WordTrace tailWord_510389 prefixEnd_510389 77651815634876691671191 := by
  unfold tailWord_510389
  simp only [CollatzResearch.WordTrace]
  refine ⟨18615416147955295346550221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12410277431970196897700147 18615416147955295346550221)
  ·
    refine ⟨6980781055483235754956333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18615416147955295346550221 6980781055483235754956333)
    ·
      refine ⟨2617792895806213408108625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6980781055483235754956333 2617792895806213408108625)
      ·
        refine ⟨1963344671854660056081469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2617792895806213408108625 1963344671854660056081469)
        ·
          refine ⟨736254251945497521030551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1963344671854660056081469 736254251945497521030551)
          ·
            refine ⟨1104381377918246281545827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736254251945497521030551 1104381377918246281545827)
            ·
              refine ⟨1656572066877369422318741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104381377918246281545827 1656572066877369422318741)
              ·
                refine ⟨77651815634876691671191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1656572066877369422318741 77651815634876691671191)
                ·
                  rfl

theorem cell20_510389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 6].length) (baseStart_510389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510389 prefixEnd_510389 := by exact prefixLift 510389
  have htrace : WordTrace (prefixWord ++ tailWord_510389) baseStart_510389 baseEnd_510389 := by
    simpa [prefixWord, tailWord_510389, baseEnd_510389] using wordTrace_append hprefix tailTrace_510389
  have hstable : (prefixWord ++ tailWord_510389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510389).length < 2 ^ (prefixWord ++ tailWord_510389).sum := by decide
  have hdescent : baseEnd_510389 < baseStart_510389 := by decide
  rcases family_descends (prefixWord ++ tailWord_510389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510396 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 5]
def baseStart_510396 : Nat := 118140960795 + 510396 * 2 ^ 59
def prefixEnd_510396 : Nat := 4983230072969 + 3 ^ 40 * 510396 * 2
def baseEnd_510396 : Nat := 232958641895369161780211

theorem tailTrace_510396 : CollatzResearch.WordTrace tailWord_510396 prefixEnd_510396 232958641895369161780211 := by
  unfold tailWord_510396
  simp only [CollatzResearch.WordTrace]
  refine ⟨9307835729464967771027521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12410447639286623694703361 9307835729464967771027521)
  ·
    refine ⟨6980876797098725828270641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9307835729464967771027521 6980876797098725828270641)
    ·
      refine ⟨5235657597824044371202981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6980876797098725828270641 5235657597824044371202981)
      ·
        refine ⟨981685799592008319600559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5235657597824044371202981 981685799592008319600559)
        ·
          refine ⟨1472528699388012479400839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 981685799592008319600559 1472528699388012479400839)
          ·
            refine ⟨2208793049082018719101259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1472528699388012479400839 2208793049082018719101259)
            ·
              refine ⟨3313189573623028078651889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2208793049082018719101259 3313189573623028078651889)
              ·
                refine ⟨2484892180217271058988917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3313189573623028078651889 2484892180217271058988917)
                ·
                  refine ⟨232958641895369161780211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2484892180217271058988917 232958641895369161780211)
                  ·
                    rfl

theorem cell20_510396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_510396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510396 prefixEnd_510396 := by exact prefixLift 510396
  have htrace : WordTrace (prefixWord ++ tailWord_510396) baseStart_510396 baseEnd_510396 := by
    simpa [prefixWord, tailWord_510396, baseEnd_510396] using wordTrace_append hprefix tailTrace_510396
  have hstable : (prefixWord ++ tailWord_510396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510396).length < 2 ^ (prefixWord ++ tailWord_510396).sum := by decide
  have hdescent : baseEnd_510396 < baseStart_510396 := by decide
  rcases family_descends (prefixWord ++ tailWord_510396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510420 : List Nat := [2, 4, 1, 2, 2, 1, 3, 1, 4]
def baseStart_510420 : Nat := 118140960795 + 510420 * 2 ^ 59
def prefixEnd_510420 : Nat := 4983230072969 + 3 ^ 40 * 510420 * 2
def baseEnd_510420 : Nat := 232969596149331744980113

theorem tailTrace_510420 : CollatzResearch.WordTrace tailWord_510420 prefixEnd_510420 232969596149331744980113 := by
  unfold tailWord_510420
  simp only [CollatzResearch.WordTrace]
  refine ⟨9308273405421493820464357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12411031207228658427285809 9308273405421493820464357)
  ·
    refine ⟨1745301263516530091337067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9308273405421493820464357 1745301263516530091337067)
    ·
      refine ⟨2617951895274795137005601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1745301263516530091337067 2617951895274795137005601)
      ·
        refine ⟨1963463921456096352754201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2617951895274795137005601 1963463921456096352754201)
        ·
          refine ⟨1472597941092072264565651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1963463921456096352754201 1472597941092072264565651)
          ·
            refine ⟨2208896911638108396848477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1472597941092072264565651 2208896911638108396848477)
            ·
              refine ⟨828336341864290648818179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2208896911638108396848477 828336341864290648818179)
              ·
                refine ⟨1242504512796435973227269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828336341864290648818179 1242504512796435973227269)
                ·
                  refine ⟨232969596149331744980113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1242504512796435973227269 232969596149331744980113)
                  ·
                    rfl

theorem cell20_510420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_510420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510420 prefixEnd_510420 := by exact prefixLift 510420
  have htrace : WordTrace (prefixWord ++ tailWord_510420) baseStart_510420 baseEnd_510420 := by
    simpa [prefixWord, tailWord_510420, baseEnd_510420] using wordTrace_append hprefix tailTrace_510420
  have hstable : (prefixWord ++ tailWord_510420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510420).length < 2 ^ (prefixWord ++ tailWord_510420).sum := by decide
  have hdescent : baseEnd_510420 < baseStart_510420 := by decide
  rcases family_descends (prefixWord ++ tailWord_510420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510471 : List Nat := [1, 1, 4, 3, 4, 1, 2, 2, 2]
def baseStart_510471 : Nat := 118140960795 + 510471 * 2 ^ 59
def prefixEnd_510471 : Nat := 4983230072969 + 3 ^ 40 * 510471 * 2
def baseEnd_510471 : Nat := 232992873939002234279905

theorem tailTrace_510471 : CollatzResearch.WordTrace tailWord_510471 prefixEnd_510471 232992873939002234279905 := by
  unfold tailWord_510471
  simp only [CollatzResearch.WordTrace]
  refine ⟨18618406933658223351035267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12412271289105482234023511 18618406933658223351035267)
  ·
    refine ⟨27927610400487335026552901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18618406933658223351035267 27927610400487335026552901)
    ·
      refine ⟨5236426950091375317478669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27927610400487335026552901 5236426950091375317478669)
      ·
        refine ⟨1963660106284265744054501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5236426950091375317478669 1963660106284265744054501)
        ·
          refine ⟨368186269928299827010219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1963660106284265744054501 368186269928299827010219)
          ·
            refine ⟨552279404892449740515329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368186269928299827010219 552279404892449740515329)
            ·
              refine ⟨414209553669337305386497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552279404892449740515329 414209553669337305386497)
              ·
                refine ⟨310657165252002979039873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414209553669337305386497 310657165252002979039873)
                ·
                  refine ⟨232992873939002234279905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310657165252002979039873 232992873939002234279905)
                  ·
                    rfl

theorem cell20_510471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2, 2].length) (baseStart_510471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510471 prefixEnd_510471 := by exact prefixLift 510471
  have htrace : WordTrace (prefixWord ++ tailWord_510471) baseStart_510471 baseEnd_510471 := by
    simpa [prefixWord, tailWord_510471, baseEnd_510471] using wordTrace_append hprefix tailTrace_510471
  have hstable : (prefixWord ++ tailWord_510471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510471).length < 2 ^ (prefixWord ++ tailWord_510471).sum := by decide
  have hdescent : baseEnd_510471 < baseStart_510471 := by decide
  rcases family_descends (prefixWord ++ tailWord_510471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510475 : List Nat := [1, 1, 1, 1, 7, 1, 4, 2, 2]
def baseStart_510475 : Nat := 118140960795 + 510475 * 2 ^ 59
def prefixEnd_510475 : Nat := 4983230072969 + 3 ^ 40 * 510475 * 2
def baseEnd_510475 : Nat := 232994699647995998146555

theorem tailTrace_510475 : CollatzResearch.WordTrace tailWord_510475 prefixEnd_510475 232994699647995998146555 := by
  unfold tailWord_510475
  simp only [CollatzResearch.WordTrace]
  refine ⟨18618552825643732034180879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12412368550429154689453919 18618552825643732034180879)
  ·
    refine ⟨27927829238465598051271319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18618552825643732034180879 27927829238465598051271319)
    ·
      refine ⟨41891743857698397076906979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27927829238465598051271319 41891743857698397076906979)
      ·
        refine ⟨62837615786547595615360469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41891743857698397076906979 62837615786547595615360469)
        ·
          refine ⟨1472756619997209272235011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 62837615786547595615360469 1472756619997209272235011)
          ·
            refine ⟨2209134929995813908352517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1472756619997209272235011 2209134929995813908352517)
            ·
              refine ⟨414212799374215107816097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2209134929995813908352517 414212799374215107816097)
              ·
                refine ⟨310659599530661330862073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414212799374215107816097 310659599530661330862073)
                ·
                  refine ⟨232994699647995998146555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310659599530661330862073 232994699647995998146555)
                  ·
                    rfl

theorem cell20_510475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 2, 2].length) (baseStart_510475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510475 prefixEnd_510475 := by exact prefixLift 510475
  have htrace : WordTrace (prefixWord ++ tailWord_510475) baseStart_510475 baseEnd_510475 := by
    simpa [prefixWord, tailWord_510475, baseEnd_510475] using wordTrace_append hprefix tailTrace_510475
  have hstable : (prefixWord ++ tailWord_510475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510475).length < 2 ^ (prefixWord ++ tailWord_510475).sum := by decide
  have hdescent : baseEnd_510475 < baseStart_510475 := by decide
  rcases family_descends (prefixWord ++ tailWord_510475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510496 : List Nat := [2, 1, 1, 6, 2, 1, 1, 2, 4]
def baseStart_510496 : Nat := 118140960795 + 510496 * 2 ^ 59
def prefixEnd_510496 : Nat := 4983230072969 + 3 ^ 40 * 510496 * 2
def baseEnd_510496 : Nat := 233004284620213258446469

theorem tailTrace_510496 : CollatzResearch.WordTrace tailWord_510496 prefixEnd_510496 233004284620213258446469 := by
  unfold tailWord_510496
  simp only [CollatzResearch.WordTrace]
  refine ⟨9309659379283826310347671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12412879172378435080463561 9309659379283826310347671)
  ·
    refine ⟨13964489068925739465521507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9309659379283826310347671 13964489068925739465521507)
    ·
      refine ⟨20946733603388609198282261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13964489068925739465521507 20946733603388609198282261)
      ·
        refine ⟨981878137658841056169481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20946733603388609198282261 981878137658841056169481)
        ·
          refine ⟨736408603244130792127111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 981878137658841056169481 736408603244130792127111)
          ·
            refine ⟨1104612904866196188190667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736408603244130792127111 1104612904866196188190667)
            ·
              refine ⟨1656919357299294282286001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1104612904866196188190667 1656919357299294282286001)
              ·
                refine ⟨1242689517974470711714501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1656919357299294282286001 1242689517974470711714501)
                ·
                  refine ⟨233004284620213258446469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1242689517974470711714501 233004284620213258446469)
                  ·
                    rfl

theorem cell20_510496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_510496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510496 prefixEnd_510496 := by exact prefixLift 510496
  have htrace : WordTrace (prefixWord ++ tailWord_510496) baseStart_510496 baseEnd_510496 := by
    simpa [prefixWord, tailWord_510496, baseEnd_510496] using wordTrace_append hprefix tailTrace_510496
  have hstable : (prefixWord ++ tailWord_510496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510496).length < 2 ^ (prefixWord ++ tailWord_510496).sum := by decide
  have hdescent : baseEnd_510496 < baseStart_510496 := by decide
  rcases family_descends (prefixWord ++ tailWord_510496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510507 : List Nat := [1, 1, 1, 1, 2, 1, 3, 10]
def baseStart_510507 : Nat := 118140960795 + 510507 * 2 ^ 59
def prefixEnd_510507 : Nat := 4983230072969 + 3 ^ 40 * 510507 * 2
def baseEnd_510507 : Nat := 77669768439982036359919

theorem tailTrace_510507 : CollatzResearch.WordTrace tailWord_510507 prefixEnd_510507 77669768439982036359919 := by
  unfold tailWord_510507
  simp only [CollatzResearch.WordTrace]
  refine ⟨18619719961527801499345775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12413146641018534332897183 18619719961527801499345775)
  ·
    refine ⟨27929579942291702249018663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18619719961527801499345775 27929579942291702249018663)
    ·
      refine ⟨41894369913437553373527995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27929579942291702249018663 41894369913437553373527995)
      ·
        refine ⟨62841554870156330060291993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41894369913437553373527995 62841554870156330060291993)
        ·
          refine ⟨47131166152617247545218995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62841554870156330060291993 47131166152617247545218995)
          ·
            refine ⟨70696749228925871317828493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47131166152617247545218995 70696749228925871317828493)
            ·
              refine ⟨26511280960847201744185685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70696749228925871317828493 26511280960847201744185685)
              ·
                refine ⟨77669768439982036359919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26511280960847201744185685 77669768439982036359919)
                ·
                  rfl

theorem cell20_510507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 10].length) (baseStart_510507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510507 prefixEnd_510507 := by exact prefixLift 510507
  have htrace : WordTrace (prefixWord ++ tailWord_510507) baseStart_510507 baseEnd_510507 := by
    simpa [prefixWord, tailWord_510507, baseEnd_510507] using wordTrace_append hprefix tailTrace_510507
  have hstable : (prefixWord ++ tailWord_510507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510507).length < 2 ^ (prefixWord ++ tailWord_510507).sum := by decide
  have hdescent : baseEnd_510507 < baseStart_510507 := by decide
  rcases family_descends (prefixWord ++ tailWord_510507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510524 : List Nat := [2, 2, 2, 2, 3, 2, 7]
def baseStart_510524 : Nat := 118140960795 + 510524 * 2 ^ 59
def prefixEnd_510524 : Nat := 4983230072969 + 3 ^ 40 * 510524 * 2
def baseEnd_510524 : Nat := 25890784953685511723669

theorem tailTrace_510524 : CollatzResearch.WordTrace tailWord_510524 prefixEnd_510524 25890784953685511723669 := by
  unfold tailWord_510524
  simp only [CollatzResearch.WordTrace]
  refine ⟨9310170001233106701357313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12413560001644142268476417 9310170001233106701357313)
  ·
    refine ⟨6982627500924830026017985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9310170001233106701357313 6982627500924830026017985)
    ·
      refine ⟨5236970625693622519513489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6982627500924830026017985 5236970625693622519513489)
      ·
        refine ⟨3927727969270216889635117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5236970625693622519513489 3927727969270216889635117)
        ·
          refine ⟨1472897988476331333613169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3927727969270216889635117 1472897988476331333613169)
          ·
            refine ⟨1104673491357248500209877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1472897988476331333613169 1104673491357248500209877)
            ·
              refine ⟨25890784953685511723669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1104673491357248500209877 25890784953685511723669)
              ·
                rfl

theorem cell20_510524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 7].length) (baseStart_510524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510524 prefixEnd_510524 := by exact prefixLift 510524
  have htrace : WordTrace (prefixWord ++ tailWord_510524) baseStart_510524 baseEnd_510524 := by
    simpa [prefixWord, tailWord_510524, baseEnd_510524] using wordTrace_append hprefix tailTrace_510524
  have hstable : (prefixWord ++ tailWord_510524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510524).length < 2 ^ (prefixWord ++ tailWord_510524).sum := by decide
  have hdescent : baseEnd_510524 < baseStart_510524 := by decide
  rcases family_descends (prefixWord ++ tailWord_510524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510568 : List Nat := [2, 1, 4, 3, 2, 2, 1, 3, 2]
def baseStart_510568 : Nat := 118140960795 + 510568 * 2 ^ 59
def prefixEnd_510568 : Nat := 4983230072969 + 3 ^ 40 * 510568 * 2
def baseEnd_510568 : Nat := 233037147382101008046175

theorem tailTrace_510568 : CollatzResearch.WordTrace tailWord_510568 prefixEnd_510568 233037147382101008046175 := by
  unfold tailWord_510568
  simp only [CollatzResearch.WordTrace]
  refine ⟨9310972407153404458658179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12414629876204539278210905 9310972407153404458658179)
  ·
    refine ⟨13966458610730106687987269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9310972407153404458658179 13966458610730106687987269)
    ·
      refine ⟨2618710989511895003997613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13966458610730106687987269 2618710989511895003997613)
      ·
        refine ⟨982016621066960626499105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2618710989511895003997613 982016621066960626499105)
        ·
          refine ⟨736512465800220469874329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 982016621066960626499105 736512465800220469874329)
          ·
            refine ⟨552384349350165352405747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 736512465800220469874329 552384349350165352405747)
            ·
              refine ⟨828576524025248028608621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552384349350165352405747 828576524025248028608621)
              ·
                refine ⟨310716196509468010728233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 828576524025248028608621 310716196509468010728233)
                ·
                  refine ⟨233037147382101008046175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310716196509468010728233 233037147382101008046175)
                  ·
                    rfl

theorem cell20_510568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 2].length) (baseStart_510568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510568 prefixEnd_510568 := by exact prefixLift 510568
  have htrace : WordTrace (prefixWord ++ tailWord_510568) baseStart_510568 baseEnd_510568 := by
    simpa [prefixWord, tailWord_510568, baseEnd_510568] using wordTrace_append hprefix tailTrace_510568
  have hstable : (prefixWord ++ tailWord_510568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510568).length < 2 ^ (prefixWord ++ tailWord_510568).sum := by decide
  have hdescent : baseEnd_510568 < baseStart_510568 := by decide
  rcases family_descends (prefixWord ++ tailWord_510568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510572 : List Nat := [2, 2, 1, 1, 3, 1, 5, 3, 2]
def baseStart_510572 : Nat := 118140960795 + 510572 * 2 ^ 59
def prefixEnd_510572 : Nat := 4983230072969 + 3 ^ 40 * 510572 * 2
def baseEnd_510572 : Nat := 233038973091094771912825

theorem tailTrace_510572 : CollatzResearch.WordTrace tailWord_510572 prefixEnd_510572 233038973091094771912825 := by
  unfold tailWord_510572
  simp only [CollatzResearch.WordTrace]
  refine ⟨9311045353146158800230985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12414727137528211733641313 9311045353146158800230985)
  ·
    refine ⟨6983284014859619100173239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9311045353146158800230985 6983284014859619100173239)
    ·
      refine ⟨10474926022289428650259859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6983284014859619100173239 10474926022289428650259859)
      ·
        refine ⟨15712389033434142975389789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10474926022289428650259859 15712389033434142975389789)
        ·
          refine ⟨5892145887537803615771171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15712389033434142975389789 5892145887537803615771171)
          ·
            refine ⟨8838218831306705423656757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5892145887537803615771171 8838218831306705423656757)
            ·
              refine ⟨828583015435003633467821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8838218831306705423656757 828583015435003633467821)
              ·
                refine ⟨310718630788126362550433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 828583015435003633467821 310718630788126362550433)
                ·
                  refine ⟨233038973091094771912825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310718630788126362550433 233038973091094771912825)
                  ·
                    rfl

theorem cell20_510572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_510572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510572 prefixEnd_510572 := by exact prefixLift 510572
  have htrace : WordTrace (prefixWord ++ tailWord_510572) baseStart_510572 baseEnd_510572 := by
    simpa [prefixWord, tailWord_510572, baseEnd_510572] using wordTrace_append hprefix tailTrace_510572
  have hstable : (prefixWord ++ tailWord_510572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510572).length < 2 ^ (prefixWord ++ tailWord_510572).sum := by decide
  have hdescent : baseEnd_510572 < baseStart_510572 := by decide
  rcases family_descends (prefixWord ++ tailWord_510572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510583 : List Nat := [1, 1, 3, 1, 1, 3, 10]
def baseStart_510583 : Nat := 118140960795 + 510583 * 2 ^ 59
def prefixEnd_510583 : Nat := 4983230072969 + 3 ^ 40 * 510583 * 2
def baseEnd_510583 : Nat := 25893777087869735838457

theorem tailTrace_510583 : CollatzResearch.WordTrace tailWord_510583 prefixEnd_510583 25893777087869735838457 := by
  unfold tailWord_510583
  simp only [CollatzResearch.WordTrace]
  refine ⟨18622491909252466479112403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12414994606168310986074935 18622491909252466479112403)
  ·
    refine ⟨27933737863878699718668605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18622491909252466479112403 27933737863878699718668605)
    ·
      refine ⟨10475151698954512394500727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27933737863878699718668605 10475151698954512394500727)
      ·
        refine ⟨15712727548431768591751091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10475151698954512394500727 15712727548431768591751091)
        ·
          refine ⟨23569091322647652887626637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15712727548431768591751091 23569091322647652887626637)
          ·
            refine ⟨8838409245992869832859989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23569091322647652887626637 8838409245992869832859989)
            ·
              refine ⟨25893777087869735838457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8838409245992869832859989 25893777087869735838457)
              ·
                rfl

theorem cell20_510583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 10].length) (baseStart_510583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510583 prefixEnd_510583 := by exact prefixLift 510583
  have htrace : WordTrace (prefixWord ++ tailWord_510583) baseStart_510583 baseEnd_510583 := by
    simpa [prefixWord, tailWord_510583, baseEnd_510583] using wordTrace_append hprefix tailTrace_510583
  have hstable : (prefixWord ++ tailWord_510583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510583).length < 2 ^ (prefixWord ++ tailWord_510583).sum := by decide
  have hdescent : baseEnd_510583 < baseStart_510583 := by decide
  rcases family_descends (prefixWord ++ tailWord_510583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510589 : List Nat := [1, 4, 1, 1, 6, 1, 1, 1, 4]
def baseStart_510589 : Nat := 118140960795 + 510589 * 2 ^ 59
def prefixEnd_510589 : Nat := 4983230072969 + 3 ^ 40 * 510589 * 2
def baseEnd_510589 : Nat := 233046732354318268346089

theorem tailTrace_510589 : CollatzResearch.WordTrace tailWord_510589 prefixEnd_510589 233046732354318268346089 := by
  unfold tailWord_510589
  simp only [CollatzResearch.WordTrace]
  refine ⟨18622710747230729503830821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12415140498153819669220547 18622710747230729503830821)
  ·
    refine ⟨3491758265105761781968279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18622710747230729503830821 3491758265105761781968279)
    ·
      refine ⟨5237637397658642672952419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3491758265105761781968279 5237637397658642672952419)
      ·
        refine ⟨7856456096487964009428629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5237637397658642672952419 7856456096487964009428629)
        ·
          refine ⟨368271379522873312941967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7856456096487964009428629 368271379522873312941967)
          ·
            refine ⟨552407069284309969412951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368271379522873312941967 552407069284309969412951)
            ·
              refine ⟨828610603926464954119427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552407069284309969412951 828610603926464954119427)
              ·
                refine ⟨1242915905889697431179141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828610603926464954119427 1242915905889697431179141)
                ·
                  refine ⟨233046732354318268346089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1242915905889697431179141 233046732354318268346089)
                  ·
                    rfl

theorem cell20_510589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_510589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510589 prefixEnd_510589 := by exact prefixLift 510589
  have htrace : WordTrace (prefixWord ++ tailWord_510589) baseStart_510589 baseEnd_510589 := by
    simpa [prefixWord, tailWord_510589, baseEnd_510589] using wordTrace_append hprefix tailTrace_510589
  have hstable : (prefixWord ++ tailWord_510589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510589).length < 2 ^ (prefixWord ++ tailWord_510589).sum := by decide
  have hdescent : baseEnd_510589 < baseStart_510589 := by decide
  rcases family_descends (prefixWord ++ tailWord_510589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510607 : List Nat := [1, 1, 2, 1, 1, 1, 1, 9, 3]
def baseStart_510607 : Nat := 118140960795 + 510607 * 2 ^ 59
def prefixEnd_510607 : Nat := 4983230072969 + 3 ^ 40 * 510607 * 2
def baseEnd_510607 : Nat := 233054948044790205746015

theorem tailTrace_510607 : CollatzResearch.WordTrace tailWord_510607 prefixEnd_510607 233054948044790205746015 := by
  unfold tailWord_510607
  simp only [CollatzResearch.WordTrace]
  refine ⟨18623367261165518577986075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12415578174110345718657383 18623367261165518577986075)
  ·
    refine ⟨27935050891748277866979113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18623367261165518577986075 27935050891748277866979113)
    ·
      refine ⟨20951288168811208400234335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27935050891748277866979113 20951288168811208400234335)
      ·
        refine ⟨31426932253216812600351503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20951288168811208400234335 31426932253216812600351503)
        ·
          refine ⟨47140398379825218900527255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31426932253216812600351503 47140398379825218900527255)
          ·
            refine ⟨70710597569737828350790883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47140398379825218900527255 70710597569737828350790883)
            ·
              refine ⟨106065896354606742526186325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70710597569737828350790883 106065896354606742526186325)
              ·
                refine ⟨621479861452773881989373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 106065896354606742526186325 621479861452773881989373)
                ·
                  refine ⟨233054948044790205746015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 621479861452773881989373 233054948044790205746015)
                  ·
                    rfl

theorem cell20_510607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 9, 3].length) (baseStart_510607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510607 prefixEnd_510607 := by exact prefixLift 510607
  have htrace : WordTrace (prefixWord ++ tailWord_510607) baseStart_510607 baseEnd_510607 := by
    simpa [prefixWord, tailWord_510607, baseEnd_510607] using wordTrace_append hprefix tailTrace_510607
  have hstable : (prefixWord ++ tailWord_510607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510607).length < 2 ^ (prefixWord ++ tailWord_510607).sum := by decide
  have hdescent : baseEnd_510607 < baseStart_510607 := by decide
  rcases family_descends (prefixWord ++ tailWord_510607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510634 : List Nat := [3, 1, 5, 2, 2, 7]
def baseStart_510634 : Nat := 118140960795 + 510634 * 2 ^ 59
def prefixEnd_510634 : Nat := 4983230072969 + 3 ^ 40 * 510634 * 2
def baseEnd_510634 : Nat := 8632121169648078216515

theorem tailTrace_510634 : CollatzResearch.WordTrace tailWord_510634 prefixEnd_510634 8632121169648078216515 := by
  unfold tailWord_510634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4656088008016925547304739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12416234688045134792812637 4656088008016925547304739)
  ·
    refine ⟨6984132012025388320957109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4656088008016925547304739 6984132012025388320957109)
    ·
      refine ⟨654762376127380155089729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6984132012025388320957109 654762376127380155089729)
      ·
        refine ⟨491071782095535116317297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 654762376127380155089729 491071782095535116317297)
        ·
          refine ⟨368303836571651337237973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 491071782095535116317297 368303836571651337237973)
          ·
            refine ⟨8632121169648078216515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 368303836571651337237973 8632121169648078216515)
            ·
              rfl

theorem cell20_510634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 7].length) (baseStart_510634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510634 prefixEnd_510634 := by exact prefixLift 510634
  have htrace : WordTrace (prefixWord ++ tailWord_510634) baseStart_510634 baseEnd_510634 := by
    simpa [prefixWord, tailWord_510634, baseEnd_510634] using wordTrace_append hprefix tailTrace_510634
  have hstable : (prefixWord ++ tailWord_510634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510634).length < 2 ^ (prefixWord ++ tailWord_510634).sum := by decide
  have hdescent : baseEnd_510634 < baseStart_510634 := by decide
  rcases family_descends (prefixWord ++ tailWord_510634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510696 : List Nat := [2, 1, 4, 1, 5, 1, 1, 2, 3]
def baseStart_510696 : Nat := 118140960795 + 510696 * 2 ^ 59
def prefixEnd_510696 : Nat := 4983230072969 + 3 ^ 40 * 510696 * 2
def baseEnd_510696 : Nat := 233095570069901451778985

theorem tailTrace_510696 : CollatzResearch.WordTrace tailWord_510696 prefixEnd_510696 233095570069901451778985 := by
  unfold tailWord_510696
  simp only [CollatzResearch.WordTrace]
  refine ⟨9313306678921543388987971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12417742238562057851983961 9313306678921543388987971)
  ·
    refine ⟨13969960018382315083481957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9313306678921543388987971 13969960018382315083481957)
    ·
      refine ⟨2619367503446684078152867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13969960018382315083481957 2619367503446684078152867)
      ·
        refine ⟨3929051255170026117229301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2619367503446684078152867 3929051255170026117229301)
        ·
          refine ⟨368348555172189948490247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3929051255170026117229301 368348555172189948490247)
          ·
            refine ⟨552522832758284922735371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368348555172189948490247 552522832758284922735371)
            ·
              refine ⟨828784249137427384103057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552522832758284922735371 828784249137427384103057)
              ·
                refine ⟨621588186853070538077293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 828784249137427384103057 621588186853070538077293)
                ·
                  refine ⟨233095570069901451778985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 621588186853070538077293 233095570069901451778985)
                  ·
                    rfl

theorem cell20_510696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 3].length) (baseStart_510696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510696 prefixEnd_510696 := by exact prefixLift 510696
  have htrace : WordTrace (prefixWord ++ tailWord_510696) baseStart_510696 baseEnd_510696 := by
    simpa [prefixWord, tailWord_510696, baseEnd_510696] using wordTrace_append hprefix tailTrace_510696
  have hstable : (prefixWord ++ tailWord_510696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510696).length < 2 ^ (prefixWord ++ tailWord_510696).sum := by decide
  have hdescent : baseEnd_510696 < baseStart_510696 := by decide
  rcases family_descends (prefixWord ++ tailWord_510696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510735 : List Nat := [1, 1, 2, 1, 1, 1, 7, 6]
def baseStart_510735 : Nat := 118140960795 + 510735 * 2 ^ 59
def prefixEnd_510735 : Nat := 4983230072969 + 3 ^ 40 * 510735 * 2
def baseEnd_510735 : Nat := 77704456910863549826275

theorem tailTrace_510735 : CollatzResearch.WordTrace tailWord_510735 prefixEnd_510735 77704456910863549826275 := by
  unfold tailWord_510735
  simp only [CollatzResearch.WordTrace]
  refine ⟨18628035804701796438645659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12418690536467864292430439 18628035804701796438645659)
  ·
    refine ⟨27942053707052694657968489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18628035804701796438645659 27942053707052694657968489)
    ·
      refine ⟨20956540280289520993476367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27942053707052694657968489 20956540280289520993476367)
      ·
        refine ⟨31434810420434281490214551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20956540280289520993476367 31434810420434281490214551)
        ·
          refine ⟨47152215630651422235321827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31434810420434281490214551 47152215630651422235321827)
          ·
            refine ⟨70728323445977133352982741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47152215630651422235321827 70728323445977133352982741)
            ·
              refine ⟨1657695080765089062960533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 70728323445977133352982741 1657695080765089062960533)
              ·
                refine ⟨77704456910863549826275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1657695080765089062960533 77704456910863549826275)
                ·
                  rfl

theorem cell20_510735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 6].length) (baseStart_510735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510735 prefixEnd_510735 := by exact prefixLift 510735
  have htrace : WordTrace (prefixWord ++ tailWord_510735) baseStart_510735 baseEnd_510735 := by
    simpa [prefixWord, tailWord_510735, baseEnd_510735] using wordTrace_append hprefix tailTrace_510735
  have hstable : (prefixWord ++ tailWord_510735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510735).length < 2 ^ (prefixWord ++ tailWord_510735).sum := by decide
  have hdescent : baseEnd_510735 < baseStart_510735 := by decide
  rcases family_descends (prefixWord ++ tailWord_510735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510745 : List Nat := [1, 2, 1, 2, 1, 1, 1, 9, 2]
def baseStart_510745 : Nat := 118140960795 + 510745 * 2 ^ 59
def prefixEnd_510745 : Nat := 4983230072969 + 3 ^ 40 * 510745 * 2
def baseEnd_510745 : Nat := 233117935005075059145451

theorem tailTrace_510745 : CollatzResearch.WordTrace tailWord_510745 prefixEnd_510745 233117935005075059145451 := by
  unfold tailWord_510745
  simp only [CollatzResearch.WordTrace]
  refine ⟨18628400534665568146509689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12418933689777045431006459 18628400534665568146509689)
  ·
    refine ⟨13971300400999176109882267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18628400534665568146509689 13971300400999176109882267)
    ·
      refine ⟨20956950601498764164823401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13971300400999176109882267 20956950601498764164823401)
      ·
        refine ⟨15717712951124073123617551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20956950601498764164823401 15717712951124073123617551)
        ·
          refine ⟨23576569426686109685426327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15717712951124073123617551 23576569426686109685426327)
          ·
            refine ⟨35364854140029164528139491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23576569426686109685426327 35364854140029164528139491)
            ·
              refine ⟨53047281210043746792209237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35364854140029164528139491 53047281210043746792209237)
              ·
                refine ⟨310823913340100078860601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 53047281210043746792209237 310823913340100078860601)
                ·
                  refine ⟨233117935005075059145451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310823913340100078860601 233117935005075059145451)
                  ·
                    rfl

theorem cell20_510745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 9, 2].length) (baseStart_510745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510745 prefixEnd_510745 := by exact prefixLift 510745
  have htrace : WordTrace (prefixWord ++ tailWord_510745) baseStart_510745 baseEnd_510745 := by
    simpa [prefixWord, tailWord_510745, baseEnd_510745] using wordTrace_append hprefix tailTrace_510745
  have hstable : (prefixWord ++ tailWord_510745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510745).length < 2 ^ (prefixWord ++ tailWord_510745).sum := by decide
  have hdescent : baseEnd_510745 < baseStart_510745 := by decide
  rcases family_descends (prefixWord ++ tailWord_510745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510752 : List Nat := [2, 1, 1, 5, 1, 4, 6]
def baseStart_510752 : Nat := 118140960795 + 510752 * 2 ^ 59
def prefixEnd_510752 : Nat := 4983230072969 + 3 ^ 40 * 510752 * 2
def baseEnd_510752 : Nat := 25902347777312682879121

theorem tailTrace_510752 : CollatzResearch.WordTrace tailWord_510752 prefixEnd_510752 25902347777312682879121 := by
  unfold tailWord_510752
  simp only [CollatzResearch.WordTrace]
  refine ⟨9314327922820104171007255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12419103897093472228009673 9314327922820104171007255)
  ·
    refine ⟨13971491884230156256510883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9314327922820104171007255 13971491884230156256510883)
    ·
      refine ⟨20957237826345234384766325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13971491884230156256510883 20957237826345234384766325)
      ·
        refine ⟨1964741046219865723571843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20957237826345234384766325 1964741046219865723571843)
        ·
          refine ⟨2947111569329798585357765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1964741046219865723571843 2947111569329798585357765)
          ·
            refine ⟨552583419249337234754581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2947111569329798585357765 552583419249337234754581)
            ·
              refine ⟨25902347777312682879121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 552583419249337234754581 25902347777312682879121)
              ·
                rfl

theorem cell20_510752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 6].length) (baseStart_510752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510752 prefixEnd_510752 := by exact prefixLift 510752
  have htrace : WordTrace (prefixWord ++ tailWord_510752) baseStart_510752 baseEnd_510752 := by
    simpa [prefixWord, tailWord_510752, baseEnd_510752] using wordTrace_append hprefix tailTrace_510752
  have hstable : (prefixWord ++ tailWord_510752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510752).length < 2 ^ (prefixWord ++ tailWord_510752).sum := by decide
  have hdescent : baseEnd_510752 < baseStart_510752 := by decide
  rcases family_descends (prefixWord ++ tailWord_510752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510835 : List Nat := [1, 1, 1, 2, 2, 1, 6, 3, 3]
def baseStart_510835 : Nat := 118140960795 + 510835 * 2 ^ 59
def prefixEnd_510835 : Nat := 4983230072969 + 3 ^ 40 * 510835 * 2
def baseEnd_510835 : Nat := 233159013457434746145083

theorem tailTrace_510835 : CollatzResearch.WordTrace tailWord_510835 prefixEnd_510835 233159013457434746145083 := by
  unfold tailWord_510835
  simp only [CollatzResearch.WordTrace]
  refine ⟨18631683104339513517285959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12421122069559675678190639 18631683104339513517285959)
  ·
    refine ⟨27947524656509270275928939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18631683104339513517285959 27947524656509270275928939)
    ·
      refine ⟨41921286984763905413893409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27947524656509270275928939 41921286984763905413893409)
      ·
        refine ⟨31440965238572929060420057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41921286984763905413893409 31440965238572929060420057)
        ·
          refine ⟨23580723928929696795315043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31440965238572929060420057 23580723928929696795315043)
          ·
            refine ⟨35371085893394545192972565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23580723928929696795315043 35371085893394545192972565)
            ·
              refine ⟨1658019651252869305920589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35371085893394545192972565 1658019651252869305920589)
              ·
                refine ⟨621757369219825989720221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1658019651252869305920589 621757369219825989720221)
                ·
                  refine ⟨233159013457434746145083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 621757369219825989720221 233159013457434746145083)
                  ·
                    rfl

theorem cell20_510835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 3].length) (baseStart_510835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510835 prefixEnd_510835 := by exact prefixLift 510835
  have htrace : WordTrace (prefixWord ++ tailWord_510835) baseStart_510835 baseEnd_510835 := by
    simpa [prefixWord, tailWord_510835, baseEnd_510835] using wordTrace_append hprefix tailTrace_510835
  have hstable : (prefixWord ++ tailWord_510835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510835).length < 2 ^ (prefixWord ++ tailWord_510835).sum := by decide
  have hdescent : baseEnd_510835 < baseStart_510835 := by decide
  rcases family_descends (prefixWord ++ tailWord_510835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510838 : List Nat := [5, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_510838 : Nat := 118140960795 + 510838 * 2 ^ 59
def prefixEnd_510838 : Nat := 4983230072969 + 3 ^ 40 * 510838 * 2
def baseEnd_510838 : Nat := 233160382739180069045071

theorem tailTrace_510838 : CollatzResearch.WordTrace tailWord_510838 prefixEnd_510838 233160382739180069045071 := by
  unfold tailWord_510838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1164487032708040314352823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12421195015552430019763445 1164487032708040314352823)
  ·
    refine ⟨1746730549062060471529235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1164487032708040314352823 1746730549062060471529235)
    ·
      refine ⟨2620095823593090707293853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1746730549062060471529235 2620095823593090707293853)
      ·
        refine ⟨982535933847409015235195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2620095823593090707293853 982535933847409015235195)
        ·
          refine ⟨1473803900771113522852793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982535933847409015235195 1473803900771113522852793)
          ·
            refine ⟨1105352925578335142139595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1473803900771113522852793 1105352925578335142139595)
            ·
              refine ⟨1658029388367502713209393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105352925578335142139595 1658029388367502713209393)
              ·
                refine ⟨1243522041275627034907045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1658029388367502713209393 1243522041275627034907045)
                ·
                  refine ⟨233160382739180069045071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1243522041275627034907045 233160382739180069045071)
                  ·
                    rfl

theorem cell20_510838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_510838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510838 prefixEnd_510838 := by exact prefixLift 510838
  have htrace : WordTrace (prefixWord ++ tailWord_510838) baseStart_510838 baseEnd_510838 := by
    simpa [prefixWord, tailWord_510838, baseEnd_510838] using wordTrace_append hprefix tailTrace_510838
  have hstable : (prefixWord ++ tailWord_510838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510838).length < 2 ^ (prefixWord ++ tailWord_510838).sum := by decide
  have hdescent : baseEnd_510838 < baseStart_510838 := by decide
  rcases family_descends (prefixWord ++ tailWord_510838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510859 : List Nat := [1, 1, 1, 1, 4, 2, 3, 5, 2]
def baseStart_510859 : Nat := 118140960795 + 510859 * 2 ^ 59
def prefixEnd_510859 : Nat := 4983230072969 + 3 ^ 40 * 510859 * 2
def baseEnd_510859 : Nat := 233169967711397329344985

theorem tailTrace_510859 : CollatzResearch.WordTrace tailWord_510859 prefixEnd_510859 233169967711397329344985 := by
  unfold tailWord_510859
  simp only [CollatzResearch.WordTrace]
  refine ⟨18632558456252565616159631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12421705637501710410773087 18632558456252565616159631)
  ·
    refine ⟨27948837684378848424239447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18632558456252565616159631 27948837684378848424239447)
    ·
      refine ⟨41923256526568272636359171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27948837684378848424239447 41923256526568272636359171)
      ·
        refine ⟨62884884789852408954538757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41923256526568272636359171 62884884789852408954538757)
        ·
          refine ⟨11790915898097326678976017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62884884789852408954538757 11790915898097326678976017)
          ·
            refine ⟨8843186923572995009232013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11790915898097326678976017 8843186923572995009232013)
            ·
              refine ⟨3316195096339873128462005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8843186923572995009232013 3316195096339873128462005)
              ·
                refine ⟨310893290281863105793313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3316195096339873128462005 310893290281863105793313)
                ·
                  refine ⟨233169967711397329344985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310893290281863105793313 233169967711397329344985)
                  ·
                    rfl

theorem cell20_510859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 2].length) (baseStart_510859 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510859 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510859 prefixEnd_510859 := by exact prefixLift 510859
  have htrace : WordTrace (prefixWord ++ tailWord_510859) baseStart_510859 baseEnd_510859 := by
    simpa [prefixWord, tailWord_510859, baseEnd_510859] using wordTrace_append hprefix tailTrace_510859
  have hstable : (prefixWord ++ tailWord_510859).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510859).length < 2 ^ (prefixWord ++ tailWord_510859).sum := by decide
  have hdescent : baseEnd_510859 < baseStart_510859 := by decide
  rcases family_descends (prefixWord ++ tailWord_510859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510876 : List Nat := [2, 2, 3, 3, 2, 1, 2, 1, 4]
def baseStart_510876 : Nat := 118140960795 + 510876 * 2 ^ 59
def prefixEnd_510876 : Nat := 4983230072969 + 3 ^ 40 * 510876 * 2
def baseEnd_510876 : Nat := 233177726974620825778249

theorem tailTrace_510876 : CollatzResearch.WordTrace tailWord_510876 prefixEnd_510876 233177726974620825778249 := by
  unfold tailWord_510876
  simp only [CollatzResearch.WordTrace]
  refine ⟨9316589248595488759764241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12422118998127318346352321 9316589248595488759764241)
  ·
    refine ⟨6987441936446616569823181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9316589248595488759764241 6987441936446616569823181)
    ·
      refine ⟨2620290726167481213683693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6987441936446616569823181 2620290726167481213683693)
      ·
        refine ⟨982609022312805455131385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2620290726167481213683693 982609022312805455131385)
        ·
          refine ⟨736956766734604091348539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 982609022312805455131385 736956766734604091348539)
          ·
            refine ⟨1105435150101906137022809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736956766734604091348539 1105435150101906137022809)
            ·
              refine ⟨829076362576429602767107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1105435150101906137022809 829076362576429602767107)
              ·
                refine ⟨1243614543864644404150661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 829076362576429602767107 1243614543864644404150661)
                ·
                  refine ⟨233177726974620825778249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1243614543864644404150661 233177726974620825778249)
                  ·
                    rfl

theorem cell20_510876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_510876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510876 prefixEnd_510876 := by exact prefixLift 510876
  have htrace : WordTrace (prefixWord ++ tailWord_510876) baseStart_510876 baseEnd_510876 := by
    simpa [prefixWord, tailWord_510876, baseEnd_510876] using wordTrace_append hprefix tailTrace_510876
  have hstable : (prefixWord ++ tailWord_510876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510876).length < 2 ^ (prefixWord ++ tailWord_510876).sum := by decide
  have hdescent : baseEnd_510876 < baseStart_510876 := by decide
  rcases family_descends (prefixWord ++ tailWord_510876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510880 : List Nat := [2, 1, 1, 4, 1, 1, 3, 3, 4]
def baseStart_510880 : Nat := 118140960795 + 510880 * 2 ^ 59
def prefixEnd_510880 : Nat := 4983230072969 + 3 ^ 40 * 510880 * 2
def baseEnd_510880 : Nat := 233179552683614589644899

theorem tailTrace_510880 : CollatzResearch.WordTrace tailWord_510880 prefixEnd_510880 233179552683614589644899 := by
  unfold tailWord_510880
  simp only [CollatzResearch.WordTrace]
  refine ⟨9316662194588243101337047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12422216259450990801782729 9316662194588243101337047)
  ·
    refine ⟨13974993291882364652005571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9316662194588243101337047 13974993291882364652005571)
    ·
      refine ⟨20962489937823546978008357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13974993291882364652005571 20962489937823546978008357)
      ·
        refine ⟨3930466863341915058376567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20962489937823546978008357 3930466863341915058376567)
        ·
          refine ⟨5895700295012872587564851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3930466863341915058376567 5895700295012872587564851)
          ·
            refine ⟨8843550442519308881347277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5895700295012872587564851 8843550442519308881347277)
            ·
              refine ⟨3316331415944740830505229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8843550442519308881347277 3316331415944740830505229)
              ·
                refine ⟨1243624280979277811439461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3316331415944740830505229 1243624280979277811439461)
                ·
                  refine ⟨233179552683614589644899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1243624280979277811439461 233179552683614589644899)
                  ·
                    rfl

theorem cell20_510880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_510880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510880 prefixEnd_510880 := by exact prefixLift 510880
  have htrace : WordTrace (prefixWord ++ tailWord_510880) baseStart_510880 baseEnd_510880 := by
    simpa [prefixWord, tailWord_510880, baseEnd_510880] using wordTrace_append hprefix tailTrace_510880
  have hstable : (prefixWord ++ tailWord_510880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510880).length < 2 ^ (prefixWord ++ tailWord_510880).sum := by decide
  have hdescent : baseEnd_510880 < baseStart_510880 := by decide
  rcases family_descends (prefixWord ++ tailWord_510880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510900 : List Nat := [2, 5, 2, 1, 1, 1, 4, 4]
def baseStart_510900 : Nat := 118140960795 + 510900 * 2 ^ 59
def prefixEnd_510900 : Nat := 4983230072969 + 3 ^ 40 * 510900 * 2
def baseEnd_510900 : Nat := 77729560409527802992717

theorem tailTrace_510900 : CollatzResearch.WordTrace tailWord_510900 prefixEnd_510900 77729560409527802992717 := by
  unfold tailWord_510900
  simp only [CollatzResearch.WordTrace]
  refine ⟨9317026924552014809201077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12422702566069353078934769 9317026924552014809201077)
  ·
    refine ⟨873471274176751388362601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9317026924552014809201077 873471274176751388362601)
    ·
      refine ⟨655103455632563541271951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 873471274176751388362601 655103455632563541271951)
      ·
        refine ⟨982655183448845311907927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655103455632563541271951 982655183448845311907927)
        ·
          refine ⟨1473982775173267967861891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982655183448845311907927 1473982775173267967861891)
          ·
            refine ⟨2210974162759901951792837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473982775173267967861891 2210974162759901951792837)
            ·
              refine ⟨414557655517481615961157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2210974162759901951792837 414557655517481615961157)
              ·
                refine ⟨77729560409527802992717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 414557655517481615961157 77729560409527802992717)
                ·
                  rfl

theorem cell20_510900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 4, 4].length) (baseStart_510900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510900 prefixEnd_510900 := by exact prefixLift 510900
  have htrace : WordTrace (prefixWord ++ tailWord_510900) baseStart_510900 baseEnd_510900 := by
    simpa [prefixWord, tailWord_510900, baseEnd_510900] using wordTrace_append hprefix tailTrace_510900
  have hstable : (prefixWord ++ tailWord_510900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510900).length < 2 ^ (prefixWord ++ tailWord_510900).sum := by decide
  have hdescent : baseEnd_510900 < baseStart_510900 := by decide
  rcases family_descends (prefixWord ++ tailWord_510900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510904 : List Nat := [2, 1, 2, 1, 2, 4, 4, 4]
def baseStart_510904 : Nat := 118140960795 + 510904 * 2 ^ 59
def prefixEnd_510904 : Nat := 4983230072969 + 3 ^ 40 * 510904 * 2
def baseEnd_510904 : Nat := 77730168979192390948267

theorem tailTrace_510904 : CollatzResearch.WordTrace tailWord_510904 prefixEnd_510904 77730168979192390948267 := by
  unfold tailWord_510904
  simp only [CollatzResearch.WordTrace]
  refine ⟨9317099870544769150773883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12422799827393025534365177 9317099870544769150773883)
  ·
    refine ⟨13975649805817153726160825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9317099870544769150773883 13975649805817153726160825)
    ·
      refine ⟨10481737354362865294620619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13975649805817153726160825 10481737354362865294620619)
      ·
        refine ⟨15722606031544297941930929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10481737354362865294620619 15722606031544297941930929)
        ·
          refine ⟨11791954523658223456448197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15722606031544297941930929 11791954523658223456448197)
          ·
            refine ⟨2210991473185916898084037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11791954523658223456448197 2210991473185916898084037)
            ·
              refine ⟨414560901222359418390757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2210991473185916898084037 414560901222359418390757)
              ·
                refine ⟨77730168979192390948267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 414560901222359418390757 77730168979192390948267)
                ·
                  rfl

theorem cell20_510904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 4].length) (baseStart_510904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510904 prefixEnd_510904 := by exact prefixLift 510904
  have htrace : WordTrace (prefixWord ++ tailWord_510904) baseStart_510904 baseEnd_510904 := by
    simpa [prefixWord, tailWord_510904, baseEnd_510904] using wordTrace_append hprefix tailTrace_510904
  have hstable : (prefixWord ++ tailWord_510904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510904).length < 2 ^ (prefixWord ++ tailWord_510904).sum := by decide
  have hdescent : baseEnd_510904 < baseStart_510904 := by decide
  rcases family_descends (prefixWord ++ tailWord_510904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510970 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_510970 : Nat := 118140960795 + 510970 * 2 ^ 59
def prefixEnd_510970 : Nat := 4983230072969 + 3 ^ 40 * 510970 * 2
def baseEnd_510970 : Nat := 233220631135974276644531

theorem tailTrace_510970 : CollatzResearch.WordTrace tailWord_510970 prefixEnd_510970 233220631135974276644531 := by
  unfold tailWord_510970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4659151739712607893362591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12424404639233621048966909 4659151739712607893362591)
  ·
    refine ⟨6988727609568911840043887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4659151739712607893362591 6988727609568911840043887)
    ·
      refine ⟨10483091414353367760065831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6988727609568911840043887 10483091414353367760065831)
      ·
        refine ⟨15724637121530051640098747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10483091414353367760065831 15724637121530051640098747)
        ·
          refine ⟨23586955682295077460148121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15724637121530051640098747 23586955682295077460148121)
          ·
            refine ⟨17690216761721308095111091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23586955682295077460148121 17690216761721308095111091)
            ·
              refine ⟨26535325142581962142666637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17690216761721308095111091 26535325142581962142666637)
              ·
                refine ⟨9950746928468235803499989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26535325142581962142666637 9950746928468235803499989)
                ·
                  refine ⟨233220631135974276644531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9950746928468235803499989 233220631135974276644531)
                  ·
                    rfl

theorem cell20_510970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_510970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510970 prefixEnd_510970 := by exact prefixLift 510970
  have htrace : WordTrace (prefixWord ++ tailWord_510970) baseStart_510970 baseEnd_510970 := by
    simpa [prefixWord, tailWord_510970, baseEnd_510970] using wordTrace_append hprefix tailTrace_510970
  have hstable : (prefixWord ++ tailWord_510970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510970).length < 2 ^ (prefixWord ++ tailWord_510970).sum := by decide
  have hdescent : baseEnd_510970 < baseStart_510970 := by decide
  rcases family_descends (prefixWord ++ tailWord_510970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510973 : List Nat := [1, 4, 1, 1, 1, 2, 1, 7, 2]
def baseStart_510973 : Nat := 118140960795 + 510973 * 2 ^ 59
def prefixEnd_510973 : Nat := 4983230072969 + 3 ^ 40 * 510973 * 2
def baseEnd_510973 : Nat := 233222000417719599544519

theorem tailTrace_510973 : CollatzResearch.WordTrace tailWord_510973 prefixEnd_510973 233222000417719599544519 := by
  unfold tailWord_510973
  simp only [CollatzResearch.WordTrace]
  refine ⟨18636716377839563085809573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12424477585226375390539715 18636716377839563085809573)
  ·
    refine ⟨3494384320844918078589295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18636716377839563085809573 3494384320844918078589295)
    ·
      refine ⟨5241576481267377117883943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3494384320844918078589295 5241576481267377117883943)
      ·
        refine ⟨7862364721901065676825915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5241576481267377117883943 7862364721901065676825915)
        ·
          refine ⟨11793547082851598515238873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7862364721901065676825915 11793547082851598515238873)
          ·
            refine ⟨8845160312138698886429155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11793547082851598515238873 8845160312138698886429155)
            ·
              refine ⟨13267740468208048329643733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8845160312138698886429155 13267740468208048329643733)
              ·
                refine ⟨310962667223626132726025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13267740468208048329643733 310962667223626132726025)
                ·
                  refine ⟨233222000417719599544519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310962667223626132726025 233222000417719599544519)
                  ·
                    rfl

theorem cell20_510973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_510973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510973 prefixEnd_510973 := by exact prefixLift 510973
  have htrace : WordTrace (prefixWord ++ tailWord_510973) baseStart_510973 baseEnd_510973 := by
    simpa [prefixWord, tailWord_510973, baseEnd_510973] using wordTrace_append hprefix tailTrace_510973
  have hstable : (prefixWord ++ tailWord_510973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510973).length < 2 ^ (prefixWord ++ tailWord_510973).sum := by decide
  have hdescent : baseEnd_510973 < baseStart_510973 := by decide
  rcases family_descends (prefixWord ++ tailWord_510973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510987 : List Nat := [1, 1, 1, 1, 6, 2, 1, 4, 3]
def baseStart_510987 : Nat := 118140960795 + 510987 * 2 ^ 59
def prefixEnd_510987 : Nat := 4983230072969 + 3 ^ 40 * 510987 * 2
def baseEnd_510987 : Nat := 233228390399197773077795

theorem tailTrace_510987 : CollatzResearch.WordTrace tailWord_510987 prefixEnd_510987 233228390399197773077795 := by
  unfold tailWord_510987
  simp only [CollatzResearch.WordTrace]
  refine ⟨18637226999788843476819215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12424817999859228984546143 18637226999788843476819215)
  ·
    refine ⟨27955840499683265215228823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18637226999788843476819215 27955840499683265215228823)
    ·
      refine ⟨41933760749524897822843235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27955840499683265215228823 41933760749524897822843235)
      ·
        refine ⟨62900641124287346734264853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41933760749524897822843235 62900641124287346734264853)
        ·
          refine ⟨2948467552700969378168665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62900641124287346734264853 2948467552700969378168665)
          ·
            refine ⟨2211350664525727033626499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2948467552700969378168665 2211350664525727033626499)
            ·
              refine ⟨3317025996788590550439749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2211350664525727033626499 3317025996788590550439749)
              ·
                refine ⟨621942374397860728207453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3317025996788590550439749 621942374397860728207453)
                ·
                  refine ⟨233228390399197773077795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 621942374397860728207453 233228390399197773077795)
                  ·
                    rfl

theorem cell20_510987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 3].length) (baseStart_510987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510987 prefixEnd_510987 := by exact prefixLift 510987
  have htrace : WordTrace (prefixWord ++ tailWord_510987) baseStart_510987 baseEnd_510987 := by
    simpa [prefixWord, tailWord_510987, baseEnd_510987] using wordTrace_append hprefix tailTrace_510987
  have hstable : (prefixWord ++ tailWord_510987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510987).length < 2 ^ (prefixWord ++ tailWord_510987).sum := by decide
  have hdescent : baseEnd_510987 < baseStart_510987 := by decide
  rcases family_descends (prefixWord ++ tailWord_510987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_510990 : List Nat := [4, 1, 1, 2, 2, 3, 1, 4, 2]
def baseStart_510990 : Nat := 118140960795 + 510990 * 2 ^ 59
def prefixEnd_510990 : Nat := 4983230072969 + 3 ^ 40 * 510990 * 2
def baseEnd_510990 : Nat := 233229759680943095977783

theorem tailTrace_510990 : CollatzResearch.WordTrace tailWord_510990 prefixEnd_510990 233229759680943095977783 := by
  unfold tailWord_510990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2329667052347246873647303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12424890945851983326118949 2329667052347246873647303)
  ·
    refine ⟨3494500578520870310470955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2329667052347246873647303 3494500578520870310470955)
    ·
      refine ⟨5241750867781305465706433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3494500578520870310470955 5241750867781305465706433)
      ·
        refine ⟨3931313150835979099279825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5241750867781305465706433 3931313150835979099279825)
        ·
          refine ⟨2948484863126984324459869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3931313150835979099279825 2948484863126984324459869)
          ·
            refine ⟨1105681823672619121672451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2948484863126984324459869 1105681823672619121672451)
            ·
              refine ⟨1658522735508928682508677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1105681823672619121672451 1658522735508928682508677)
              ·
                refine ⟨310973012907924127970377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1658522735508928682508677 310973012907924127970377)
                ·
                  refine ⟨233229759680943095977783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 310973012907924127970377 233229759680943095977783)
                  ·
                    rfl

theorem cell20_510990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_510990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_510990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_510990 prefixEnd_510990 := by exact prefixLift 510990
  have htrace : WordTrace (prefixWord ++ tailWord_510990) baseStart_510990 baseEnd_510990 := by
    simpa [prefixWord, tailWord_510990, baseEnd_510990] using wordTrace_append hprefix tailTrace_510990
  have hstable : (prefixWord ++ tailWord_510990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_510990).length < 2 ^ (prefixWord ++ tailWord_510990).sum := by decide
  have hdescent : baseEnd_510990 < baseStart_510990 := by decide
  rcases family_descends (prefixWord ++ tailWord_510990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511001 : List Nat := [1, 2, 1, 2, 1, 1, 7, 5]
def baseStart_511001 : Nat := 118140960795 + 511001 * 2 ^ 59
def prefixEnd_511001 : Nat := 4983230072969 + 3 ^ 40 * 511001 * 2
def baseEnd_511001 : Nat := 77744926793558648870357

theorem tailTrace_511001 : CollatzResearch.WordTrace tailWord_511001 prefixEnd_511001 77744926793558648870357 := by
  unfold tailWord_511001
  simp only [CollatzResearch.WordTrace]
  refine ⟨18637737621738123867828857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12425158414492082578552571 18637737621738123867828857)
  ·
    refine ⟨13978303216303592900871643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18637737621738123867828857 13978303216303592900871643)
    ·
      refine ⟨20967454824455389351307465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13978303216303592900871643 20967454824455389351307465)
      ·
        refine ⟨15725591118341542013480599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20967454824455389351307465 15725591118341542013480599)
        ·
          refine ⟨23588386677512313020220899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15725591118341542013480599 23588386677512313020220899)
          ·
            refine ⟨35382580016268469530331349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23588386677512313020220899 35382580016268469530331349)
            ·
              refine ⟨829279219131292254617141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 35382580016268469530331349 829279219131292254617141)
              ·
                refine ⟨77744926793558648870357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 829279219131292254617141 77744926793558648870357)
                ·
                  rfl

theorem cell20_511001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 5].length) (baseStart_511001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511001 prefixEnd_511001 := by exact prefixLift 511001
  have htrace : WordTrace (prefixWord ++ tailWord_511001) baseStart_511001 baseEnd_511001 := by
    simpa [prefixWord, tailWord_511001, baseEnd_511001] using wordTrace_append hprefix tailTrace_511001
  have hstable : (prefixWord ++ tailWord_511001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511001).length < 2 ^ (prefixWord ++ tailWord_511001).sum := by decide
  have hdescent : baseEnd_511001 < baseStart_511001 := by decide
  rcases family_descends (prefixWord ++ tailWord_511001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_511069 : List Nat := [1, 4, 4, 1, 3, 1, 2, 4]
def baseStart_511069 : Nat := 118140960795 + 511069 * 2 ^ 59
def prefixEnd_511069 : Nat := 4983230072969 + 3 ^ 40 * 511069 * 2
def baseEnd_511069 : Nat := 77755272477856644114709

theorem tailTrace_511069 : CollatzResearch.WordTrace tailWord_511069 prefixEnd_511069 77755272477856644114709 := by
  unfold tailWord_511069
  simp only [CollatzResearch.WordTrace]
  refine ⟨18640217785491771481304261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12426811856994514320869507 18640217785491771481304261)
  ·
    refine ⟨3495040834779707152744549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18640217785491771481304261 3495040834779707152744549)
    ·
      refine ⟨655320156521195091139603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3495040834779707152744549 655320156521195091139603)
      ·
        refine ⟨982980234781792636709405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 655320156521195091139603 982980234781792636709405)
        ·
          refine ⟨368617588043172238766027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 982980234781792636709405 368617588043172238766027)
          ·
            refine ⟨552926382064758358149041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368617588043172238766027 552926382064758358149041)
            ·
              refine ⟨414694786548568768611781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552926382064758358149041 414694786548568768611781)
              ·
                refine ⟨77755272477856644114709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 414694786548568768611781 77755272477856644114709)
                ·
                  rfl

theorem cell20_511069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 2, 4].length) (baseStart_511069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_511069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_511069 prefixEnd_511069 := by exact prefixLift 511069
  have htrace : WordTrace (prefixWord ++ tailWord_511069) baseStart_511069 baseEnd_511069 := by
    simpa [prefixWord, tailWord_511069, baseEnd_511069] using wordTrace_append hprefix tailTrace_511069
  have hstable : (prefixWord ++ tailWord_511069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_511069).length < 2 ^ (prefixWord ++ tailWord_511069).sum := by decide
  have hdescent : baseEnd_511069 < baseStart_511069 := by decide
  rcases family_descends (prefixWord ++ tailWord_511069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
