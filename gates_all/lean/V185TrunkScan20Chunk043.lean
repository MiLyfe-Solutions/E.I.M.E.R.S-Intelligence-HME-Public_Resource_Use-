import V185TrunkScan20Chunk042

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_260847 : List Nat := [1, 1, 2, 1, 5, 2, 4, 2, 2]
def baseStart_260847 : Nat := 118140960795 + 260847 * 2 ^ 59
def prefixEnd_260847 : Nat := 4983230072969 + 3 ^ 40 * 260847 * 2
def baseEnd_260847 : Nat := 119057678474174372100349

theorem tailTrace_260847 : CollatzResearch.WordTrace tailWord_260847 prefixEnd_260847 119057678474174372100349 := by
  unfold tailWord_260847
  simp only [CollatzResearch.WordTrace]
  refine ⟨9513871686003342965972795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6342581124002228643981863 9513871686003342965972795)
  ·
    refine ⟨14270807529005014448959193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9513871686003342965972795 14270807529005014448959193)
    ·
      refine ⟨10703105646753760836719395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14270807529005014448959193 10703105646753760836719395)
      ·
        refine ⟨16054658470130641255079093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10703105646753760836719395 16054658470130641255079093)
        ·
          refine ⟨1505124231574747617663665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16054658470130641255079093 1505124231574747617663665)
          ·
            refine ⟨1128843173681060713247749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1505124231574747617663665 1128843173681060713247749)
            ·
              refine ⟨211658095065198883733953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1128843173681060713247749 211658095065198883733953)
              ·
                refine ⟨158743571298899162800465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211658095065198883733953 158743571298899162800465)
                ·
                  refine ⟨119057678474174372100349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158743571298899162800465 119057678474174372100349)
                  ·
                    rfl

theorem cell20_260847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 2, 2].length) (baseStart_260847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260847 prefixEnd_260847 := by exact prefixLift 260847
  have htrace : WordTrace (prefixWord ++ tailWord_260847) baseStart_260847 baseEnd_260847 := by
    simpa [prefixWord, tailWord_260847, baseEnd_260847] using wordTrace_append hprefix tailTrace_260847
  have hstable : (prefixWord ++ tailWord_260847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260847).length < 2 ^ (prefixWord ++ tailWord_260847).sum := by decide
  have hdescent : baseEnd_260847 < baseStart_260847 := by decide
  rcases family_descends (prefixWord ++ tailWord_260847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260858 : List Nat := [3, 1, 1, 1, 1, 3, 5, 5]
def baseStart_260858 : Nat := 118140960795 + 260858 * 2 ^ 59
def prefixEnd_260858 : Nat := 4983230072969 + 3 ^ 40 * 260858 * 2
def baseEnd_260858 : Nat := 39687566391302407577879

theorem tailTrace_260858 : CollatzResearch.WordTrace tailWord_260858 prefixEnd_260858 39687566391302407577879 := by
  unfold tailWord_260858
  simp only [CollatzResearch.WordTrace]
  refine ⟨2378568222240872961155807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6342848592642327896415485 2378568222240872961155807)
  ·
    refine ⟨3567852333361309441733711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2378568222240872961155807 3567852333361309441733711)
    ·
      refine ⟨5351778500041964162600567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3567852333361309441733711 5351778500041964162600567)
      ·
        refine ⟨8027667750062946243900851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5351778500041964162600567 8027667750062946243900851)
        ·
          refine ⟨12041501625094419365851277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8027667750062946243900851 12041501625094419365851277)
          ·
            refine ⟨4515563109410407262194229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12041501625094419365851277 4515563109410407262194229)
            ·
              refine ⟨423334041507225680830709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4515563109410407262194229 423334041507225680830709)
              ·
                refine ⟨39687566391302407577879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 423334041507225680830709 39687566391302407577879)
                ·
                  rfl

theorem cell20_260858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_260858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260858 prefixEnd_260858 := by exact prefixLift 260858
  have htrace : WordTrace (prefixWord ++ tailWord_260858) baseStart_260858 baseEnd_260858 := by
    simpa [prefixWord, tailWord_260858, baseEnd_260858] using wordTrace_append hprefix tailTrace_260858
  have hstable : (prefixWord ++ tailWord_260858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260858).length < 2 ^ (prefixWord ++ tailWord_260858).sum := by decide
  have hdescent : baseEnd_260858 < baseStart_260858 := by decide
  rcases family_descends (prefixWord ++ tailWord_260858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260865 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 7]
def baseStart_260865 : Nat := 118140960795 + 260865 * 2 ^ 59
def prefixEnd_260865 : Nat := 4983230072969 + 3 ^ 40 * 260865 * 2
def baseEnd_260865 : Nat := 119065894164646309500275

theorem tailTrace_260865 : CollatzResearch.WordTrace tailWord_260865 prefixEnd_260865 119065894164646309500275 := by
  unfold tailWord_260865
  simp only [CollatzResearch.WordTrace]
  refine ⟨9514528199938132040128049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6343018799958754693418699 9514528199938132040128049)
  ·
    refine ⟨7135896149953599030096037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9514528199938132040128049 7135896149953599030096037)
    ·
      refine ⟨1337980528116299818143007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7135896149953599030096037 1337980528116299818143007)
      ·
        refine ⟨2006970792174449727214511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1337980528116299818143007 2006970792174449727214511)
        ·
          refine ⟨3010456188261674590821767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2006970792174449727214511 3010456188261674590821767)
          ·
            refine ⟨4515684282392511886232651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3010456188261674590821767 4515684282392511886232651)
            ·
              refine ⟨6773526423588767829348977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4515684282392511886232651 6773526423588767829348977)
              ·
                refine ⟨5080144817691575872011733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6773526423588767829348977 5080144817691575872011733)
                ·
                  refine ⟨119065894164646309500275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5080144817691575872011733 119065894164646309500275)
                  ·
                    rfl

theorem cell20_260865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_260865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260865 prefixEnd_260865 := by exact prefixLift 260865
  have htrace : WordTrace (prefixWord ++ tailWord_260865) baseStart_260865 baseEnd_260865 := by
    simpa [prefixWord, tailWord_260865, baseEnd_260865] using wordTrace_append hprefix tailTrace_260865
  have hstable : (prefixWord ++ tailWord_260865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260865).length < 2 ^ (prefixWord ++ tailWord_260865).sum := by decide
  have hdescent : baseEnd_260865 < baseStart_260865 := by decide
  rcases family_descends (prefixWord ++ tailWord_260865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260896 : List Nat := [2, 1, 1, 5, 1, 3, 7]
def baseStart_260896 : Nat := 118140960795 + 260896 * 2 ^ 59
def prefixEnd_260896 : Nat := 4983230072969 + 3 ^ 40 * 260896 * 2
def baseEnd_260896 : Nat := 13231115934371997718535

theorem tailTrace_260896 : CollatzResearch.WordTrace tailWord_260896 prefixEnd_260896 13231115934371997718535 := by
  unfold tailWord_260896
  simp only [CollatzResearch.WordTrace]
  refine ⟨4757829431412912167253271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6343772575217216223004361 4757829431412912167253271)
  ·
    refine ⟨7136744147119368250879907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4757829431412912167253271 7136744147119368250879907)
    ·
      refine ⟨10705116220679052376319861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7136744147119368250879907 10705116220679052376319861)
      ·
        refine ⟨1003604645688661160279987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10705116220679052376319861 1003604645688661160279987)
        ·
          refine ⟨1505406968532991740419981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1003604645688661160279987 1505406968532991740419981)
          ·
            refine ⟨564527613199871902657493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1505406968532991740419981 564527613199871902657493)
            ·
              refine ⟨13231115934371997718535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 564527613199871902657493 13231115934371997718535)
              ·
                rfl

theorem cell20_260896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 7].length) (baseStart_260896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260896 prefixEnd_260896 := by exact prefixLift 260896
  have htrace : WordTrace (prefixWord ++ tailWord_260896) baseStart_260896 baseEnd_260896 := by
    simpa [prefixWord, tailWord_260896, baseEnd_260896] using wordTrace_append hprefix tailTrace_260896
  have hstable : (prefixWord ++ tailWord_260896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260896).length < 2 ^ (prefixWord ++ tailWord_260896).sum := by decide
  have hdescent : baseEnd_260896 < baseStart_260896 := by decide
  rcases family_descends (prefixWord ++ tailWord_260896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260927 : List Nat := [1, 1, 2, 2, 5, 1, 2, 2, 4]
def baseStart_260927 : Nat := 118140960795 + 260927 * 2 ^ 59
def prefixEnd_260927 : Nat := 4983230072969 + 3 ^ 40 * 260927 * 2
def baseEnd_260927 : Nat := 119094192654049649433355

theorem tailTrace_260927 : CollatzResearch.WordTrace tailWord_260927 prefixEnd_260927 119094192654049649433355 := by
  unfold tailWord_260927
  simp only [CollatzResearch.WordTrace]
  refine ⟨9516789525713516628885035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6344526350475677752590023 9516789525713516628885035)
  ·
    refine ⟨14275184288570274943327553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9516789525713516628885035 14275184288570274943327553)
    ·
      refine ⟨10706388216427706207495665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14275184288570274943327553 10706388216427706207495665)
      ·
        refine ⟨8029791162320779655621749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10706388216427706207495665 8029791162320779655621749)
        ·
          refine ⟨752792921467573092714539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8029791162320779655621749 752792921467573092714539)
          ·
            refine ⟨1129189382201359639071809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752792921467573092714539 1129189382201359639071809)
            ·
              refine ⟨846892036651019729303857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1129189382201359639071809 846892036651019729303857)
              ·
                refine ⟨635169027488264796977893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 846892036651019729303857 635169027488264796977893)
                ·
                  refine ⟨119094192654049649433355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 635169027488264796977893 119094192654049649433355)
                  ·
                    rfl

theorem cell20_260927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 4].length) (baseStart_260927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260927 prefixEnd_260927 := by exact prefixLift 260927
  have htrace : WordTrace (prefixWord ++ tailWord_260927) baseStart_260927 baseEnd_260927 := by
    simpa [prefixWord, tailWord_260927, baseEnd_260927] using wordTrace_append hprefix tailTrace_260927
  have hstable : (prefixWord ++ tailWord_260927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260927).length < 2 ^ (prefixWord ++ tailWord_260927).sum := by decide
  have hdescent : baseEnd_260927 < baseStart_260927 := by decide
  rcases family_descends (prefixWord ++ tailWord_260927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260944 : List Nat := [2, 1, 1, 1, 1, 4, 5, 3, 2]
def baseStart_260944 : Nat := 118140960795 + 260944 * 2 ^ 59
def prefixEnd_260944 : Nat := 4983230072969 + 3 ^ 40 * 260944 * 2
def baseEnd_260944 : Nat := 119101951917273145866619

theorem tailTrace_260944 : CollatzResearch.WordTrace tailWord_260944 prefixEnd_260944 119101951917273145866619 := by
  unfold tailWord_260944
  simp only [CollatzResearch.WordTrace]
  refine ⟨4758704783325964266126943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6344939711101285688169257 4758704783325964266126943)
  ·
    refine ⟨7138057174988946399190415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4758704783325964266126943 7138057174988946399190415)
    ·
      refine ⟨10707085762483419598785623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7138057174988946399190415 10707085762483419598785623)
      ·
        refine ⟨16060628643725129398178435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10707085762483419598785623 16060628643725129398178435)
        ·
          refine ⟨24090942965587694097267653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16060628643725129398178435 24090942965587694097267653)
          ·
            refine ⟨4517051806047692643237685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24090942965587694097267653 4517051806047692643237685)
            ·
              refine ⟨423473606816971185303533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4517051806047692643237685 423473606816971185303533)
              ·
                refine ⟨158802602556364194488825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 423473606816971185303533 158802602556364194488825)
                ·
                  refine ⟨119101951917273145866619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158802602556364194488825 119101951917273145866619)
                  ·
                    rfl

theorem cell20_260944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 2].length) (baseStart_260944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260944 prefixEnd_260944 := by exact prefixLift 260944
  have htrace : WordTrace (prefixWord ++ tailWord_260944) baseStart_260944 baseEnd_260944 := by
    simpa [prefixWord, tailWord_260944, baseEnd_260944] using wordTrace_append hprefix tailTrace_260944
  have hstable : (prefixWord ++ tailWord_260944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260944).length < 2 ^ (prefixWord ++ tailWord_260944).sum := by decide
  have hdescent : baseEnd_260944 < baseStart_260944 := by decide
  rcases family_descends (prefixWord ++ tailWord_260944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260965 : List Nat := [1, 3, 1, 3, 1, 1, 5, 1, 4]
def baseStart_260965 : Nat := 118140960795 + 260965 * 2 ^ 59
def prefixEnd_260965 : Nat := 4983230072969 + 3 ^ 40 * 260965 * 2
def baseEnd_260965 : Nat := 119111536889490406166533

theorem tailTrace_260965 : CollatzResearch.WordTrace tailWord_260965 prefixEnd_260965 119111536889490406166533 := by
  unfold tailWord_260965
  simp only [CollatzResearch.WordTrace]
  refine ⟨9518175499575849118768349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6345450333050566079178899 9518175499575849118768349)
  ·
    refine ⟨3569315812340943419538131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9518175499575849118768349 3569315812340943419538131)
    ·
      refine ⟨5353973718511415129307197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3569315812340943419538131 5353973718511415129307197)
      ·
        refine ⟨2007740144441780673490199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5353973718511415129307197 2007740144441780673490199)
        ·
          refine ⟨3011610216662671010235299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2007740144441780673490199 3011610216662671010235299)
          ·
            refine ⟨4517415324994006515352949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3011610216662671010235299 4517415324994006515352949)
            ·
              refine ⟨423507686718188110814339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4517415324994006515352949 423507686718188110814339)
              ·
                refine ⟨635261530077282166221509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423507686718188110814339 635261530077282166221509)
                ·
                  refine ⟨119111536889490406166533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 635261530077282166221509 119111536889490406166533)
                  ·
                    rfl

theorem cell20_260965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_260965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260965 prefixEnd_260965 := by exact prefixLift 260965
  have htrace : WordTrace (prefixWord ++ tailWord_260965) baseStart_260965 baseEnd_260965 := by
    simpa [prefixWord, tailWord_260965, baseEnd_260965] using wordTrace_append hprefix tailTrace_260965
  have hstable : (prefixWord ++ tailWord_260965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260965).length < 2 ^ (prefixWord ++ tailWord_260965).sum := by decide
  have hdescent : baseEnd_260965 < baseStart_260965 := by decide
  rcases family_descends (prefixWord ++ tailWord_260965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260972 : List Nat := [2, 2, 1, 1, 4, 1, 4, 5]
def baseStart_260972 : Nat := 118140960795 + 260972 * 2 ^ 59
def prefixEnd_260972 : Nat := 4983230072969 + 3 ^ 40 * 260972 * 2
def baseEnd_260972 : Nat := 39704910626743164311057

theorem tailTrace_260972 : CollatzResearch.WordTrace tailWord_260972 prefixEnd_260972 39704910626743164311057 := by
  unfold tailWord_260972
  simp only [CollatzResearch.WordTrace]
  refine ⟨4759215405275244657136585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6345620540366992876182113 4759215405275244657136585)
  ·
    refine ⟨3569411553956433492852439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4759215405275244657136585 3569411553956433492852439)
    ·
      refine ⟨5354117330934650239278659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3569411553956433492852439 5354117330934650239278659)
      ·
        refine ⟨8031175996401975358917989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5354117330934650239278659 8031175996401975358917989)
        ·
          refine ⟨1505845499325370379797123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8031175996401975358917989 1505845499325370379797123)
          ·
            refine ⟨2258768248988055569695685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1505845499325370379797123 2258768248988055569695685)
            ·
              refine ⟨423519046685260419317941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2258768248988055569695685 423519046685260419317941)
              ·
                refine ⟨39704910626743164311057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 423519046685260419317941 39704910626743164311057)
                ·
                  rfl

theorem cell20_260972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_260972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260972 prefixEnd_260972 := by exact prefixLift 260972
  have htrace : WordTrace (prefixWord ++ tailWord_260972) baseStart_260972 baseEnd_260972 := by
    simpa [prefixWord, tailWord_260972, baseEnd_260972] using wordTrace_append hprefix tailTrace_260972
  have hstable : (prefixWord ++ tailWord_260972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260972).length < 2 ^ (prefixWord ++ tailWord_260972).sum := by decide
  have hdescent : baseEnd_260972 < baseStart_260972 := by decide
  rcases family_descends (prefixWord ++ tailWord_260972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_260986 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_260986 : Nat := 118140960795 + 260986 * 2 ^ 59
def prefixEnd_260986 : Nat := 4983230072969 + 3 ^ 40 * 260986 * 2
def baseEnd_260986 : Nat := 119121121861707666466447

theorem tailTrace_260986 : CollatzResearch.WordTrace tailWord_260986 prefixEnd_260986 119121121861707666466447 := by
  unfold tailWord_260986
  simp only [CollatzResearch.WordTrace]
  refine ⟨2379735358124942426320703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6345960954999846470188541 2379735358124942426320703)
  ·
    refine ⟨3569603037187413639481055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2379735358124942426320703 3569603037187413639481055)
    ·
      refine ⟨5354404555781120459221583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3569603037187413639481055 5354404555781120459221583)
      ·
        refine ⟨8031606833671680688832375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5354404555781120459221583 8031606833671680688832375)
        ·
          refine ⟨12047410250507521033248563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8031606833671680688832375 12047410250507521033248563)
          ·
            refine ⟨18071115375761281549872845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12047410250507521033248563 18071115375761281549872845)
            ·
              refine ⟨6776668265910480581202317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18071115375761281549872845 6776668265910480581202317)
              ·
                refine ⟨2541250599716430217950869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6776668265910480581202317 2541250599716430217950869)
                ·
                  refine ⟨119121121861707666466447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2541250599716430217950869 119121121861707666466447)
                  ·
                    rfl

theorem cell20_260986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_260986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_260986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_260986 prefixEnd_260986 := by exact prefixLift 260986
  have htrace : WordTrace (prefixWord ++ tailWord_260986) baseStart_260986 baseEnd_260986 := by
    simpa [prefixWord, tailWord_260986, baseEnd_260986] using wordTrace_append hprefix tailTrace_260986
  have hstable : (prefixWord ++ tailWord_260986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_260986).length < 2 ^ (prefixWord ++ tailWord_260986).sum := by decide
  have hdescent : baseEnd_260986 < baseStart_260986 := by decide
  rcases family_descends (prefixWord ++ tailWord_260986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261010 : List Nat := [3, 2, 3, 2, 10]
def baseStart_261010 : Nat := 118140960795 + 261010 * 2 ^ 59
def prefixEnd_261010 : Nat := 4983230072969 + 3 ^ 40 * 261010 * 2
def baseEnd_261010 : Nat := 1470766371798398144029

theorem tailTrace_261010 : CollatzResearch.WordTrace tailWord_261010 prefixEnd_261010 1470766371798398144029 := by
  unfold tailWord_261010
  simp only [CollatzResearch.WordTrace]
  refine ⟨2379954196103205451039121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6346544522941881202770989 2379954196103205451039121)
  ·
    refine ⟨1784965647077404088279341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2379954196103205451039121 1784965647077404088279341)
    ·
      refine ⟨669362117654026533104753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1784965647077404088279341 669362117654026533104753)
      ·
        refine ⟨502021588240519899828565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 669362117654026533104753 502021588240519899828565)
        ·
          refine ⟨1470766371798398144029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 502021588240519899828565 1470766371798398144029)
          ·
            rfl

theorem cell20_261010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 10].length) (baseStart_261010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261010 prefixEnd_261010 := by exact prefixLift 261010
  have htrace : WordTrace (prefixWord ++ tailWord_261010) baseStart_261010 baseEnd_261010 := by
    simpa [prefixWord, tailWord_261010, baseEnd_261010] using wordTrace_append hprefix tailTrace_261010
  have hstable : (prefixWord ++ tailWord_261010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261010).length < 2 ^ (prefixWord ++ tailWord_261010).sum := by decide
  have hdescent : baseEnd_261010 < baseStart_261010 := by decide
  rcases family_descends (prefixWord ++ tailWord_261010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261037 : List Nat := [1, 5, 2, 3, 1, 1, 1, 2, 4]
def baseStart_261037 : Nat := 118140960795 + 261037 * 2 ^ 59
def prefixEnd_261037 : Nat := 4983230072969 + 3 ^ 40 * 261037 * 2
def baseEnd_261037 : Nat := 119144399651378155766239

theorem tailTrace_261037 : CollatzResearch.WordTrace tailWord_261037 prefixEnd_261037 119144399651378155766239 := by
  unfold tailWord_261037
  simp only [CollatzResearch.WordTrace]
  refine ⟨9520801555315005415389365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6347201036876670276926243 9520801555315005415389365)
  ·
    refine ⟨892575145810781757692753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9520801555315005415389365 892575145810781757692753)
    ·
      refine ⟨669431359358086318269565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 892575145810781757692753 669431359358086318269565)
      ·
        refine ⟨251036759759282369351087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 669431359358086318269565 251036759759282369351087)
        ·
          refine ⟨376555139638923554026631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251036759759282369351087 376555139638923554026631)
          ·
            refine ⟨564832709458385331039947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376555139638923554026631 564832709458385331039947)
            ·
              refine ⟨847249064187577996559921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564832709458385331039947 847249064187577996559921)
              ·
                refine ⟨635436798140683497419941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 847249064187577996559921 635436798140683497419941)
                ·
                  refine ⟨119144399651378155766239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 635436798140683497419941 119144399651378155766239)
                  ·
                    rfl

theorem cell20_261037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_261037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261037 prefixEnd_261037 := by exact prefixLift 261037
  have htrace : WordTrace (prefixWord ++ tailWord_261037) baseStart_261037 baseEnd_261037 := by
    simpa [prefixWord, tailWord_261037, baseEnd_261037] using wordTrace_append hprefix tailTrace_261037
  have hstable : (prefixWord ++ tailWord_261037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261037).length < 2 ^ (prefixWord ++ tailWord_261037).sum := by decide
  have hdescent : baseEnd_261037 < baseStart_261037 := by decide
  rcases family_descends (prefixWord ++ tailWord_261037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261103 : List Nat := [1, 1, 2, 1, 4, 5, 2, 4]
def baseStart_261103 : Nat := 118140960795 + 261103 * 2 ^ 59
def prefixEnd_261103 : Nat := 4983230072969 + 3 ^ 40 * 261103 * 2
def baseEnd_261103 : Nat := 39724841283258419855323

theorem tailTrace_261103 : CollatzResearch.WordTrace tailWord_261103 prefixEnd_261103 39724841283258419855323 := by
  unfold tailWord_261103
  simp only [CollatzResearch.WordTrace]
  refine ⟨9523208773075898687291963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6348805848717265791527975 9523208773075898687291963)
  ·
    refine ⟨14284813159613848030937945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9523208773075898687291963 14284813159613848030937945)
    ·
      refine ⟨10713609869710386023203459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14284813159613848030937945 10713609869710386023203459)
      ·
        refine ⟨16070414804565579034805189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10713609869710386023203459 16070414804565579034805189)
        ·
          refine ⟨3013202775856046069025973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16070414804565579034805189 3013202775856046069025973)
          ·
            refine ⟨282487760236504318971185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3013202775856046069025973 282487760236504318971185)
            ·
              refine ⟨211865820177378239228389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282487760236504318971185 211865820177378239228389)
              ·
                refine ⟨39724841283258419855323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211865820177378239228389 39724841283258419855323)
                ·
                  rfl

theorem cell20_261103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 4].length) (baseStart_261103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261103 prefixEnd_261103 := by exact prefixLift 261103
  have htrace : WordTrace (prefixWord ++ tailWord_261103) baseStart_261103 baseEnd_261103 := by
    simpa [prefixWord, tailWord_261103, baseEnd_261103] using wordTrace_append hprefix tailTrace_261103
  have hstable : (prefixWord ++ tailWord_261103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261103).length < 2 ^ (prefixWord ++ tailWord_261103).sum := by decide
  have hdescent : baseEnd_261103 < baseStart_261103 := by decide
  rcases family_descends (prefixWord ++ tailWord_261103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261109 : List Nat := [1, 3, 5, 2, 1, 2, 1, 3, 2]
def baseStart_261109 : Nat := 118140960795 + 261109 * 2 ^ 59
def prefixEnd_261109 : Nat := 4983230072969 + 3 ^ 40 * 261109 * 2
def baseEnd_261109 : Nat := 119177262413265905365945

theorem tailTrace_261109 : CollatzResearch.WordTrace tailWord_261109 prefixEnd_261109 119177262413265905365945 := by
  unfold tailWord_261109
  simp only [CollatzResearch.WordTrace]
  refine ⟨9523427611054161712010381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6348951740702774474673587 9523427611054161712010381)
  ·
    refine ⟨3571285354145310642003893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9523427611054161712010381 3571285354145310642003893)
    ·
      refine ⟨334808001951122872687865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3571285354145310642003893 334808001951122872687865)
      ·
        refine ⟨251106001463342154515899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334808001951122872687865 251106001463342154515899)
        ·
          refine ⟨376659002195013231773849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251106001463342154515899 376659002195013231773849)
          ·
            refine ⟨282494251646259923830387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376659002195013231773849 282494251646259923830387)
            ·
              refine ⟨423741377469389885745581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282494251646259923830387 423741377469389885745581)
              ·
                refine ⟨158903016551021207154593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 423741377469389885745581 158903016551021207154593)
                ·
                  refine ⟨119177262413265905365945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158903016551021207154593 119177262413265905365945)
                  ·
                    rfl

theorem cell20_261109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_261109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261109 prefixEnd_261109 := by exact prefixLift 261109
  have htrace : WordTrace (prefixWord ++ tailWord_261109) baseStart_261109 baseEnd_261109 := by
    simpa [prefixWord, tailWord_261109, baseEnd_261109] using wordTrace_append hprefix tailTrace_261109
  have hstable : (prefixWord ++ tailWord_261109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261109).length < 2 ^ (prefixWord ++ tailWord_261109).sum := by decide
  have hdescent : baseEnd_261109 < baseStart_261109 := by decide
  rcases family_descends (prefixWord ++ tailWord_261109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261110 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_261110 : Nat := 118140960795 + 261110 * 2 ^ 59
def prefixEnd_261110 : Nat := 4983230072969 + 3 ^ 40 * 261110 * 2
def baseEnd_261110 : Nat := 119177718840514346332607

theorem tailTrace_261110 : CollatzResearch.WordTrace tailWord_261110 prefixEnd_261110 119177718840514346332607 := by
  unfold tailWord_261110
  simp only [CollatzResearch.WordTrace]
  refine ⟨595216505253158680174799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6348976056033692588531189 595216505253158680174799)
  ·
    refine ⟨892824757879738020262199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 595216505253158680174799 892824757879738020262199)
    ·
      refine ⟨1339237136819607030393299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 892824757879738020262199 1339237136819607030393299)
      ·
        refine ⟨2008855705229410545589949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1339237136819607030393299 2008855705229410545589949)
        ·
          refine ⟨753320889461028954596231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2008855705229410545589949 753320889461028954596231)
          ·
            refine ⟨1129981334191543431894347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 753320889461028954596231 1129981334191543431894347)
            ·
              refine ⟨1694972001287315147841521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1129981334191543431894347 1694972001287315147841521)
              ·
                refine ⟨1271229000965486360881141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1694972001287315147841521 1271229000965486360881141)
                ·
                  refine ⟨119177718840514346332607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1271229000965486360881141 119177718840514346332607)
                  ·
                    rfl

theorem cell20_261110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_261110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261110 prefixEnd_261110 := by exact prefixLift 261110
  have htrace : WordTrace (prefixWord ++ tailWord_261110) baseStart_261110 baseEnd_261110 := by
    simpa [prefixWord, tailWord_261110, baseEnd_261110] using wordTrace_append hprefix tailTrace_261110
  have hstable : (prefixWord ++ tailWord_261110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261110).length < 2 ^ (prefixWord ++ tailWord_261110).sum := by decide
  have hdescent : baseEnd_261110 < baseStart_261110 := by decide
  rcases family_descends (prefixWord ++ tailWord_261110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261131 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 5]
def baseStart_261131 : Nat := 118140960795 + 261131 * 2 ^ 59
def prefixEnd_261131 : Nat := 4983230072969 + 3 ^ 40 * 261131 * 2
def baseEnd_261131 : Nat := 119187303812731606632521

theorem tailTrace_261131 : CollatzResearch.WordTrace tailWord_261131 prefixEnd_261131 119187303812731606632521 := by
  unfold tailWord_261131
  simp only [CollatzResearch.WordTrace]
  refine ⟨9524230016974459469311247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6349486677982972979540831 9524230016974459469311247)
  ·
    refine ⟨14286345025461689203966871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9524230016974459469311247 14286345025461689203966871)
    ·
      refine ⟨21429517538192533805950307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14286345025461689203966871 21429517538192533805950307)
      ·
        refine ⟨32144276307288800708925461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21429517538192533805950307 32144276307288800708925461)
        ·
          refine ⟨1506762951904162533230881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32144276307288800708925461 1506762951904162533230881)
          ·
            refine ⟨1130072213928121899923161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1506762951904162533230881 1130072213928121899923161)
            ·
              refine ⟨847554160446091424942371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1130072213928121899923161 847554160446091424942371)
              ·
                refine ⟨1271331240669137137413557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 847554160446091424942371 1271331240669137137413557)
                ·
                  refine ⟨119187303812731606632521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1271331240669137137413557 119187303812731606632521)
                  ·
                    rfl

theorem cell20_261131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 5].length) (baseStart_261131 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261131 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261131 prefixEnd_261131 := by exact prefixLift 261131
  have htrace : WordTrace (prefixWord ++ tailWord_261131) baseStart_261131 baseEnd_261131 := by
    simpa [prefixWord, tailWord_261131, baseEnd_261131] using wordTrace_append hprefix tailTrace_261131
  have hstable : (prefixWord ++ tailWord_261131).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261131).length < 2 ^ (prefixWord ++ tailWord_261131).sum := by decide
  have hdescent : baseEnd_261131 < baseStart_261131 := by decide
  rcases family_descends (prefixWord ++ tailWord_261131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261134 : List Nat := [4, 1, 1, 2, 2, 4, 1, 1, 4]
def baseStart_261134 : Nat := 118140960795 + 261134 * 2 ^ 59
def prefixEnd_261134 : Nat := 4983230072969 + 3 ^ 40 * 261134 * 2
def baseEnd_261134 : Nat := 119188673094476929532509

theorem tailTrace_261134 : CollatzResearch.WordTrace tailWord_261134 prefixEnd_261134 119188673094476929532509 := by
  unfold tailWord_261134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1190542429495448872708807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6349559623975727321113637 1190542429495448872708807)
  ·
    refine ⟨1785813644243173309063211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1190542429495448872708807 1785813644243173309063211)
    ·
      refine ⟨2678720466364759963594817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1785813644243173309063211 2678720466364759963594817)
      ·
        refine ⟨2009040349773569972696113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2678720466364759963594817 2009040349773569972696113)
        ·
          refine ⟨1506780262330177479522085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2009040349773569972696113 1506780262330177479522085)
          ·
            refine ⟨282521299186908277410391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1506780262330177479522085 282521299186908277410391)
            ·
              refine ⟨423781948780362416115587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282521299186908277410391 423781948780362416115587)
              ·
                refine ⟨635672923170543624173381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423781948780362416115587 635672923170543624173381)
                ·
                  refine ⟨119188673094476929532509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 635672923170543624173381 119188673094476929532509)
                  ·
                    rfl

theorem cell20_261134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_261134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261134 prefixEnd_261134 := by exact prefixLift 261134
  have htrace : WordTrace (prefixWord ++ tailWord_261134) baseStart_261134 baseEnd_261134 := by
    simpa [prefixWord, tailWord_261134, baseEnd_261134] using wordTrace_append hprefix tailTrace_261134
  have hstable : (prefixWord ++ tailWord_261134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261134).length < 2 ^ (prefixWord ++ tailWord_261134).sum := by decide
  have hdescent : baseEnd_261134 < baseStart_261134 := by decide
  rcases family_descends (prefixWord ++ tailWord_261134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261145 : List Nat := [1, 2, 1, 2, 1, 1, 5, 7]
def baseStart_261145 : Nat := 118140960795 + 261145 * 2 ^ 59
def prefixEnd_261145 : Nat := 4983230072969 + 3 ^ 40 * 261145 * 2
def baseEnd_261145 : Nat := 39731231264736593388599

theorem tailTrace_261145 : CollatzResearch.WordTrace tailWord_261145 prefixEnd_261145 39731231264736593388599 := by
  unfold tailWord_261145
  simp only [CollatzResearch.WordTrace]
  refine ⟨9524740638923739860320889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6349827092615826573547259 9524740638923739860320889)
  ·
    refine ⟨7143555479192804895240667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9524740638923739860320889 7143555479192804895240667)
    ·
      refine ⟨10715333218789207342861001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7143555479192804895240667 10715333218789207342861001)
      ·
        refine ⟨8036499914091905507145751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10715333218789207342861001 8036499914091905507145751)
        ·
          refine ⟨12054749871137858260718627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8036499914091905507145751 12054749871137858260718627)
          ·
            refine ⟨18082124806706787391077941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12054749871137858260718627 18082124806706787391077941)
            ·
              refine ⟨1695199200628761317913557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18082124806706787391077941 1695199200628761317913557)
              ·
                refine ⟨39731231264736593388599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1695199200628761317913557 39731231264736593388599)
                ·
                  rfl

theorem cell20_261145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 7].length) (baseStart_261145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261145 prefixEnd_261145 := by exact prefixLift 261145
  have htrace : WordTrace (prefixWord ++ tailWord_261145) baseStart_261145 baseEnd_261145 := by
    simpa [prefixWord, tailWord_261145, baseEnd_261145] using wordTrace_append hprefix tailTrace_261145
  have hstable : (prefixWord ++ tailWord_261145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261145).length < 2 ^ (prefixWord ++ tailWord_261145).sum := by decide
  have hdescent : baseEnd_261145 < baseStart_261145 := by decide
  rcases family_descends (prefixWord ++ tailWord_261145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261185 : List Nat := [1, 2, 5, 1, 4, 1, 2, 2, 2]
def baseStart_261185 : Nat := 118140960795 + 261185 * 2 ^ 59
def prefixEnd_261185 : Nat := 4983230072969 + 3 ^ 40 * 261185 * 2
def baseEnd_261185 : Nat := 119211950884147418832301

theorem tailTrace_261185 : CollatzResearch.WordTrace tailWord_261185 prefixEnd_261185 119211950884147418832301 := by
  unfold tailWord_261185
  simp only [CollatzResearch.WordTrace]
  refine ⟨9526199558778826691777009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6350799705852551127851339 9526199558778826691777009)
  ·
    refine ⟨7144649669084120018832757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9526199558778826691777009 7144649669084120018832757)
    ·
      refine ⟨669810906476636251765571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7144649669084120018832757 669810906476636251765571)
      ·
        refine ⟨1004716359714954377648357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 669810906476636251765571 1004716359714954377648357)
        ·
          refine ⟨188384317446553945809067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1004716359714954377648357 188384317446553945809067)
          ·
            refine ⟨282576476169830918713601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188384317446553945809067 282576476169830918713601)
            ·
              refine ⟨211932357127373189035201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282576476169830918713601 211932357127373189035201)
              ·
                refine ⟨158949267845529891776401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211932357127373189035201 158949267845529891776401)
                ·
                  refine ⟨119211950884147418832301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158949267845529891776401 119211950884147418832301)
                  ·
                    rfl

theorem cell20_261185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 2, 2].length) (baseStart_261185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261185 prefixEnd_261185 := by exact prefixLift 261185
  have htrace : WordTrace (prefixWord ++ tailWord_261185) baseStart_261185 baseEnd_261185 := by
    simpa [prefixWord, tailWord_261185, baseEnd_261185] using wordTrace_append hprefix tailTrace_261185
  have hstable : (prefixWord ++ tailWord_261185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261185).length < 2 ^ (prefixWord ++ tailWord_261185).sum := by decide
  have hdescent : baseEnd_261185 < baseStart_261185 := by decide
  rcases family_descends (prefixWord ++ tailWord_261185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261237 : List Nat := [1, 3, 4, 3, 2, 1, 1, 2, 3]
def baseStart_261237 : Nat := 118140960795 + 261237 * 2 ^ 59
def prefixEnd_261237 : Nat := 4983230072969 + 3 ^ 40 * 261237 * 2
def baseEnd_261237 : Nat := 119235685101066349098755

theorem tailTrace_261237 : CollatzResearch.WordTrace tailWord_261237 prefixEnd_261237 119235685101066349098755 := by
  unfold tailWord_261237
  simp only [CollatzResearch.WordTrace]
  refine ⟨9528096154590439572669965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6352064103060293048446643 9528096154590439572669965)
  ·
    refine ⟨3573036057971414839751237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9528096154590439572669965 3573036057971414839751237)
    ·
      refine ⟨669944260869640282453357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3573036057971414839751237 669944260869640282453357)
      ·
        refine ⟨251229097826115105920009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 669944260869640282453357 251229097826115105920009)
        ·
          refine ⟨188421823369586329440007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251229097826115105920009 188421823369586329440007)
          ·
            refine ⟨282632735054379494160011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188421823369586329440007 282632735054379494160011)
            ·
              refine ⟨423949102581569241240017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282632735054379494160011 423949102581569241240017)
              ·
                refine ⟨317961826936176930930013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423949102581569241240017 317961826936176930930013)
                ·
                  refine ⟨119235685101066349098755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 317961826936176930930013 119235685101066349098755)
                  ·
                    rfl

theorem cell20_261237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_261237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261237 prefixEnd_261237 := by exact prefixLift 261237
  have htrace : WordTrace (prefixWord ++ tailWord_261237) baseStart_261237 baseEnd_261237 := by
    simpa [prefixWord, tailWord_261237, baseEnd_261237] using wordTrace_append hprefix tailTrace_261237
  have hstable : (prefixWord ++ tailWord_261237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261237).length < 2 ^ (prefixWord ++ tailWord_261237).sum := by decide
  have hdescent : baseEnd_261237 < baseStart_261237 := by decide
  rcases family_descends (prefixWord ++ tailWord_261237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261238 : List Nat := [5, 1, 1, 2, 1, 1, 9]
def baseStart_261238 : Nat := 118140960795 + 261238 * 2 ^ 59
def prefixEnd_261238 : Nat := 4983230072969 + 3 ^ 40 * 261238 * 2
def baseEnd_261238 : Nat := 13248460169812754451713

theorem tailTrace_261238 : CollatzResearch.WordTrace tailWord_261238 prefixEnd_261238 13248460169812754451713 := by
  unfold tailWord_261238
  simp only [CollatzResearch.WordTrace]
  refine ⟨595508289224176046466023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6352088418391211162304245 595508289224176046466023)
  ·
    refine ⟨893262433836264069699035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 595508289224176046466023 893262433836264069699035)
    ·
      refine ⟨1339893650754396104548553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 893262433836264069699035 1339893650754396104548553)
      ·
        refine ⟨1004920238065797078411415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1339893650754396104548553 1004920238065797078411415)
        ·
          refine ⟨1507380357098695617617123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1004920238065797078411415 1507380357098695617617123)
          ·
            refine ⟨2261070535648043426425685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1507380357098695617617123 2261070535648043426425685)
            ·
              refine ⟨13248460169812754451713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2261070535648043426425685 13248460169812754451713)
              ·
                rfl

theorem cell20_261238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 9].length) (baseStart_261238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261238 prefixEnd_261238 := by exact prefixLift 261238
  have htrace : WordTrace (prefixWord ++ tailWord_261238) baseStart_261238 baseEnd_261238 := by
    simpa [prefixWord, tailWord_261238, baseEnd_261238] using wordTrace_append hprefix tailTrace_261238
  have hstable : (prefixWord ++ tailWord_261238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261238).length < 2 ^ (prefixWord ++ tailWord_261238).sum := by decide
  have hdescent : baseEnd_261238 < baseStart_261238 := by decide
  rcases family_descends (prefixWord ++ tailWord_261238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261241 : List Nat := [1, 2, 1, 3, 5, 2, 1, 2, 3]
def baseStart_261241 : Nat := 118140960795 + 261241 * 2 ^ 59
def prefixEnd_261241 : Nat := 4983230072969 + 3 ^ 40 * 261241 * 2
def baseEnd_261241 : Nat := 119237510810060112965405

theorem tailTrace_261241 : CollatzResearch.WordTrace tailWord_261241 prefixEnd_261241 119237510810060112965405 := by
  unfold tailWord_261241
  simp only [CollatzResearch.WordTrace]
  refine ⟨9528242046575948255815577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6352161364383965503877051 9528242046575948255815577)
  ·
    refine ⟨7146181534931961191861683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9528242046575948255815577 7146181534931961191861683)
    ·
      refine ⟨10719272302397941787792525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7146181534931961191861683 10719272302397941787792525)
      ·
        refine ⟨4019727113399228170422197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10719272302397941787792525 4019727113399228170422197)
        ·
          refine ⟨376849416881177640977081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4019727113399228170422197 376849416881177640977081)
          ·
            refine ⟨282637062660883230732811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376849416881177640977081 282637062660883230732811)
            ·
              refine ⟨423955593991324846099217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282637062660883230732811 423955593991324846099217)
              ·
                refine ⟨317966695493493634574413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 423955593991324846099217 317966695493493634574413)
                ·
                  refine ⟨119237510810060112965405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 317966695493493634574413 119237510810060112965405)
                  ·
                    rfl

theorem cell20_261241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 1, 2, 3].length) (baseStart_261241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261241 prefixEnd_261241 := by exact prefixLift 261241
  have htrace : WordTrace (prefixWord ++ tailWord_261241) baseStart_261241 baseEnd_261241 := by
    simpa [prefixWord, tailWord_261241, baseEnd_261241] using wordTrace_append hprefix tailTrace_261241
  have hstable : (prefixWord ++ tailWord_261241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261241).length < 2 ^ (prefixWord ++ tailWord_261241).sum := by decide
  have hdescent : baseEnd_261241 < baseStart_261241 := by decide
  rcases family_descends (prefixWord ++ tailWord_261241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261245 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 5]
def baseStart_261245 : Nat := 118140960795 + 261245 * 2 ^ 59
def prefixEnd_261245 : Nat := 4983230072969 + 3 ^ 40 * 261245 * 2
def baseEnd_261245 : Nat := 119239336519053876832055

theorem tailTrace_261245 : CollatzResearch.WordTrace tailWord_261245 prefixEnd_261245 119239336519053876832055 := by
  unfold tailWord_261245
  simp only [CollatzResearch.WordTrace]
  refine ⟨9528387938561456938961189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6352258625707637959307459 9528387938561456938961189)
  ·
    refine ⟨1786572738480273176055223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9528387938561456938961189 1786572738480273176055223)
    ·
      refine ⟨2679859107720409764082835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1786572738480273176055223 2679859107720409764082835)
      ·
        refine ⟨4019788661580614646124253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2679859107720409764082835 4019788661580614646124253)
        ·
          refine ⟨1507420748092730492296595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4019788661580614646124253 1507420748092730492296595)
          ·
            refine ⟨2261131122139095738444893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1507420748092730492296595 2261131122139095738444893)
            ·
              refine ⟨847924170802160901916835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2261131122139095738444893 847924170802160901916835)
              ·
                refine ⟨1271886256203241352875253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 847924170802160901916835 1271886256203241352875253)
                ·
                  refine ⟨119239336519053876832055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1271886256203241352875253 119239336519053876832055)
                  ·
                    rfl

theorem cell20_261245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_261245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261245 prefixEnd_261245 := by exact prefixLift 261245
  have htrace : WordTrace (prefixWord ++ tailWord_261245) baseStart_261245 baseEnd_261245 := by
    simpa [prefixWord, tailWord_261245, baseEnd_261245] using wordTrace_append hprefix tailTrace_261245
  have hstable : (prefixWord ++ tailWord_261245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261245).length < 2 ^ (prefixWord ++ tailWord_261245).sum := by decide
  have hdescent : baseEnd_261245 < baseStart_261245 := by decide
  rcases family_descends (prefixWord ++ tailWord_261245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261276 : List Nat := [2, 2, 3, 2, 1, 3, 1, 6]
def baseStart_261276 : Nat := 118140960795 + 261276 * 2 ^ 59
def prefixEnd_261276 : Nat := 4983230072969 + 3 ^ 40 * 261276 * 2
def baseEnd_261276 : Nat := 39751161921251848932865

theorem tailTrace_261276 : CollatzResearch.WordTrace tailWord_261276 prefixEnd_261276 39751161921251848932865 := by
  unfold tailWord_261276
  simp only [CollatzResearch.WordTrace]
  refine ⟨4764759300724574616669841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6353012400966099488893121 4764759300724574616669841)
  ·
    refine ⟨3573569475543430962502381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4764759300724574616669841 3573569475543430962502381)
    ·
      refine ⟨1340088553328786610938393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3573569475543430962502381 1340088553328786610938393)
      ·
        refine ⟨1005066414996589958203795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1340088553328786610938393 1005066414996589958203795)
        ·
          refine ⟨1507599622494884937305693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005066414996589958203795 1507599622494884937305693)
          ·
            refine ⟨565349858435581851489635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1507599622494884937305693 565349858435581851489635)
            ·
              refine ⟨848024787653372777234453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565349858435581851489635 848024787653372777234453)
              ·
                refine ⟨39751161921251848932865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 848024787653372777234453 39751161921251848932865)
                ·
                  rfl

theorem cell20_261276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_261276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261276 prefixEnd_261276 := by exact prefixLift 261276
  have htrace : WordTrace (prefixWord ++ tailWord_261276) baseStart_261276 baseEnd_261276 := by
    simpa [prefixWord, tailWord_261276, baseEnd_261276] using wordTrace_append hprefix tailTrace_261276
  have hstable : (prefixWord ++ tailWord_261276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261276).length < 2 ^ (prefixWord ++ tailWord_261276).sum := by decide
  have hdescent : baseEnd_261276 < baseStart_261276 := by decide
  rcases family_descends (prefixWord ++ tailWord_261276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261282 : List Nat := [3, 3, 1, 3, 2, 2, 1, 3, 2]
def baseStart_261282 : Nat := 118140960795 + 261282 * 2 ^ 59
def prefixEnd_261282 : Nat := 4983230072969 + 3 ^ 40 * 261282 * 2
def baseEnd_261282 : Nat := 119256224327246192598571

theorem tailTrace_261282 : CollatzResearch.WordTrace tailWord_261282 prefixEnd_261282 119256224327246192598571 := by
  unfold tailWord_261282
  simp only [CollatzResearch.WordTrace]
  refine ⟨2382434359856853064514525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6353158292951608172038733 2382434359856853064514525)
  ·
    refine ⟨893412884946319899192947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2382434359856853064514525 893412884946319899192947)
    ·
      refine ⟨1340119327419479848789421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 893412884946319899192947 1340119327419479848789421)
      ·
        refine ⟨502544747782304943296033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1340119327419479848789421 502544747782304943296033)
        ·
          refine ⟨376908560836728707472025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502544747782304943296033 376908560836728707472025)
          ·
            refine ⟨282681420627546530604019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376908560836728707472025 282681420627546530604019)
            ·
              refine ⟨424022130941319795906029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282681420627546530604019 424022130941319795906029)
              ·
                refine ⟨159008299102994923464761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 424022130941319795906029 159008299102994923464761)
                ·
                  refine ⟨119256224327246192598571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159008299102994923464761 119256224327246192598571)
                  ·
                    rfl

theorem cell20_261282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_261282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261282 prefixEnd_261282 := by exact prefixLift 261282
  have htrace : WordTrace (prefixWord ++ tailWord_261282) baseStart_261282 baseEnd_261282 := by
    simpa [prefixWord, tailWord_261282, baseEnd_261282] using wordTrace_append hprefix tailTrace_261282
  have hstable : (prefixWord ++ tailWord_261282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261282).length < 2 ^ (prefixWord ++ tailWord_261282).sum := by decide
  have hdescent : baseEnd_261282 < baseStart_261282 := by decide
  rcases family_descends (prefixWord ++ tailWord_261282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261293 : List Nat := [1, 5, 2, 1, 3, 2, 6]
def baseStart_261293 : Nat := 118140960795 + 261293 * 2 ^ 59
def prefixEnd_261293 : Nat := 4983230072969 + 3 ^ 40 * 261293 * 2
def baseEnd_261293 : Nat := 13251249447442115914651

theorem tailTrace_261293 : CollatzResearch.WordTrace tailWord_261293 prefixEnd_261293 13251249447442115914651 := by
  unfold tailWord_261293
  simp only [CollatzResearch.WordTrace]
  refine ⟨9530138642387561136708533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6353425761591707424472355 9530138642387561136708533)
  ·
    refine ⟨893450497723833856566425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9530138642387561136708533 893450497723833856566425)
    ·
      refine ⟨670087873292875392424819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 893450497723833856566425 670087873292875392424819)
      ·
        refine ⟨1005131809939313088637229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670087873292875392424819 1005131809939313088637229)
        ·
          refine ⟨376924428727242408238961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1005131809939313088637229 376924428727242408238961)
          ·
            refine ⟨282693321545431806179221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376924428727242408238961 282693321545431806179221)
            ·
              refine ⟨13251249447442115914651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 282693321545431806179221 13251249447442115914651)
              ·
                rfl

theorem cell20_261293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 2, 6].length) (baseStart_261293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261293 prefixEnd_261293 := by exact prefixLift 261293
  have htrace : WordTrace (prefixWord ++ tailWord_261293) baseStart_261293 baseEnd_261293 := by
    simpa [prefixWord, tailWord_261293, baseEnd_261293] using wordTrace_append hprefix tailTrace_261293
  have hstable : (prefixWord ++ tailWord_261293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261293).length < 2 ^ (prefixWord ++ tailWord_261293).sum := by decide
  have hdescent : baseEnd_261293 < baseStart_261293 := by decide
  rcases family_descends (prefixWord ++ tailWord_261293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261335 : List Nat := [1, 1, 3, 2, 1, 2, 4, 6]
def baseStart_261335 : Nat := 118140960795 + 261335 * 2 ^ 59
def prefixEnd_261335 : Nat := 4983230072969 + 3 ^ 40 * 261335 * 2
def baseEnd_261335 : Nat := 39760138323804521277229

theorem tailTrace_261335 : CollatzResearch.WordTrace tailWord_261335 prefixEnd_261335 39760138323804521277229 := by
  unfold tailWord_261335
  simp only [CollatzResearch.WordTrace]
  refine ⟨9531670508235402309737459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6354447005490268206491639 9531670508235402309737459)
  ·
    refine ⟨14297505762353103464606189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9531670508235402309737459 14297505762353103464606189)
    ·
      refine ⟨5361564660882413799227321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14297505762353103464606189 5361564660882413799227321)
      ·
        refine ⟨4021173495661810349420491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5361564660882413799227321 4021173495661810349420491)
        ·
          refine ⟨6031760243492715524130737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4021173495661810349420491 6031760243492715524130737)
          ·
            refine ⟨4523820182619536643098053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6031760243492715524130737 4523820182619536643098053)
            ·
              refine ⟨848216284241163120580885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4523820182619536643098053 848216284241163120580885)
              ·
                refine ⟨39760138323804521277229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 848216284241163120580885 39760138323804521277229)
                ·
                  rfl

theorem cell20_261335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 6].length) (baseStart_261335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261335 prefixEnd_261335 := by exact prefixLift 261335
  have htrace : WordTrace (prefixWord ++ tailWord_261335) baseStart_261335 baseEnd_261335 := by
    simpa [prefixWord, tailWord_261335, baseEnd_261335] using wordTrace_append hprefix tailTrace_261335
  have hstable : (prefixWord ++ tailWord_261335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261335).length < 2 ^ (prefixWord ++ tailWord_261335).sum := by decide
  have hdescent : baseEnd_261335 < baseStart_261335 := by decide
  rcases family_descends (prefixWord ++ tailWord_261335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261400 : List Nat := [2, 1, 2, 3, 1, 4, 2, 3, 2]
def baseStart_261400 : Nat := 118140960795 + 261400 * 2 ^ 59
def prefixEnd_261400 : Nat := 4983230072969 + 3 ^ 40 * 261400 * 2
def baseEnd_261400 : Nat := 119310082742562226664755

theorem tailTrace_261400 : CollatzResearch.WordTrace tailWord_261400 prefixEnd_261400 119310082742562226664755 := by
  unfold tailWord_261400
  simp only [CollatzResearch.WordTrace]
  refine ⟨4767020626499959205426827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6356027501999945607235769 4767020626499959205426827)
  ·
    refine ⟨7150530939749938808140241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4767020626499959205426827 7150530939749938808140241)
    ·
      refine ⟨5362898204812454106105181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7150530939749938808140241 5362898204812454106105181)
      ·
        refine ⟨2011086826804670289789443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5362898204812454106105181 2011086826804670289789443)
        ·
          refine ⟨3016630240207005434684165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2011086826804670289789443 3016630240207005434684165)
          ·
            refine ⟨565618170038813519003281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3016630240207005434684165 565618170038813519003281)
            ·
              refine ⟨424213627529110139252461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565618170038813519003281 424213627529110139252461)
              ·
                refine ⟨159080110323416302219673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 424213627529110139252461 159080110323416302219673)
                ·
                  refine ⟨119310082742562226664755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159080110323416302219673 119310082742562226664755)
                  ·
                    rfl

theorem cell20_261400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 2].length) (baseStart_261400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261400 prefixEnd_261400 := by exact prefixLift 261400
  have htrace : WordTrace (prefixWord ++ tailWord_261400) baseStart_261400 baseEnd_261400 := by
    simpa [prefixWord, tailWord_261400, baseEnd_261400] using wordTrace_append hprefix tailTrace_261400
  have hstable : (prefixWord ++ tailWord_261400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261400).length < 2 ^ (prefixWord ++ tailWord_261400).sum := by decide
  have hdescent : baseEnd_261400 < baseStart_261400 := by decide
  rcases family_descends (prefixWord ++ tailWord_261400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261410 : List Nat := [3, 3, 1, 1, 5, 1, 1, 2, 3]
def baseStart_261410 : Nat := 118140960795 + 261410 * 2 ^ 59
def prefixEnd_261410 : Nat := 4983230072969 + 3 ^ 40 * 261410 * 2
def baseEnd_261410 : Nat := 119314647015046636331381

theorem tailTrace_261410 : CollatzResearch.WordTrace tailWord_261410 prefixEnd_261410 119314647015046636331381 := by
  unfold tailWord_261410
  simp only [CollatzResearch.WordTrace]
  refine ⟨2383601495740922529679421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6356270655309126745811789 2383601495740922529679421)
  ·
    refine ⟨893850560902845948629783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2383601495740922529679421 893850560902845948629783)
    ·
      refine ⟨1340775841354268922944675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 893850560902845948629783 1340775841354268922944675)
      ·
        refine ⟨2011163762031403384417013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1340775841354268922944675 2011163762031403384417013)
        ·
          refine ⟨188546602690444067289095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2011163762031403384417013 188546602690444067289095)
          ·
            refine ⟨282819904035666100933643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188546602690444067289095 282819904035666100933643)
            ·
              refine ⟨424229856053499151400465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282819904035666100933643 424229856053499151400465)
              ·
                refine ⟨318172392040124363550349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424229856053499151400465 318172392040124363550349)
                ·
                  refine ⟨119314647015046636331381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 318172392040124363550349 119314647015046636331381)
                  ·
                    rfl

theorem cell20_261410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_261410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261410 prefixEnd_261410 := by exact prefixLift 261410
  have htrace : WordTrace (prefixWord ++ tailWord_261410) baseStart_261410 baseEnd_261410 := by
    simpa [prefixWord, tailWord_261410, baseEnd_261410] using wordTrace_append hprefix tailTrace_261410
  have hstable : (prefixWord ++ tailWord_261410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261410).length < 2 ^ (prefixWord ++ tailWord_261410).sum := by decide
  have hdescent : baseEnd_261410 < baseStart_261410 := by decide
  rcases family_descends (prefixWord ++ tailWord_261410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261411 : List Nat := [1, 1, 1, 4, 2, 4, 7]
def baseStart_261411 : Nat := 118140960795 + 261411 * 2 ^ 59
def prefixEnd_261411 : Nat := 4983230072969 + 3 ^ 40 * 261411 * 2
def baseEnd_261411 : Nat := 13257233715810564144227

theorem tailTrace_261411 : CollatzResearch.WordTrace tailWord_261411 prefixEnd_261411 13257233715810564144227 := by
  unfold tailWord_261411
  simp only [CollatzResearch.WordTrace]
  refine ⟨9534442455960067289504087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6356294970640044859669391 9534442455960067289504087)
  ·
    refine ⟨14301663683940100934256131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9534442455960067289504087 14301663683940100934256131)
    ·
      refine ⟨21452495525910151401384197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14301663683940100934256131 21452495525910151401384197)
      ·
        refine ⟨4022342911108153387759537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21452495525910151401384197 4022342911108153387759537)
        ·
          refine ⟨3016757183331115040819653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4022342911108153387759537 3016757183331115040819653)
          ·
            refine ⟨565641971874584070153685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3016757183331115040819653 565641971874584070153685)
            ·
              refine ⟨13257233715810564144227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 565641971874584070153685 13257233715810564144227)
              ·
                rfl

theorem cell20_261411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 7].length) (baseStart_261411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261411 prefixEnd_261411 := by exact prefixLift 261411
  have htrace : WordTrace (prefixWord ++ tailWord_261411) baseStart_261411 baseEnd_261411 := by
    simpa [prefixWord, tailWord_261411, baseEnd_261411] using wordTrace_append hprefix tailTrace_261411
  have hstable : (prefixWord ++ tailWord_261411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261411).length < 2 ^ (prefixWord ++ tailWord_261411).sum := by decide
  have hdescent : baseEnd_261411 < baseStart_261411 := by decide
  rcases family_descends (prefixWord ++ tailWord_261411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261428 : List Nat := [2, 5, 1, 1, 1, 1, 2, 7]
def baseStart_261428 : Nat := 118140960795 + 261428 * 2 ^ 59
def prefixEnd_261428 : Nat := 4983230072969 + 3 ^ 40 * 261428 * 2
def baseEnd_261428 : Nat := 39774287568506191243769

theorem tailTrace_261428 : CollatzResearch.WordTrace tailWord_261428 prefixEnd_261428 39774287568506191243769 := by
  unfold tailWord_261428
  simp only [CollatzResearch.WordTrace]
  refine ⟨4767531248449239596436469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6356708331265652795248625 4767531248449239596436469)
  ·
    refine ⟨446956054542116212165919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4767531248449239596436469 446956054542116212165919)
    ·
      refine ⟨670434081813174318248879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 446956054542116212165919 670434081813174318248879)
      ·
        refine ⟨1005651122719761477373319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670434081813174318248879 1005651122719761477373319)
        ·
          refine ⟨1508476684079642216059979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1005651122719761477373319 1508476684079642216059979)
          ·
            refine ⟨2262715026119463324089969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1508476684079642216059979 2262715026119463324089969)
            ·
              refine ⟨1697036269589597493067477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2262715026119463324089969 1697036269589597493067477)
              ·
                refine ⟨39774287568506191243769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1697036269589597493067477 39774287568506191243769)
                ·
                  rfl

theorem cell20_261428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_261428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261428 prefixEnd_261428 := by exact prefixLift 261428
  have htrace : WordTrace (prefixWord ++ tailWord_261428) baseStart_261428 baseEnd_261428 := by
    simpa [prefixWord, tailWord_261428, baseEnd_261428] using wordTrace_append hprefix tailTrace_261428
  have hstable : (prefixWord ++ tailWord_261428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261428).length < 2 ^ (prefixWord ++ tailWord_261428).sum := by decide
  have hdescent : baseEnd_261428 < baseStart_261428 := by decide
  rcases family_descends (prefixWord ++ tailWord_261428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261456 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 7]
def baseStart_261456 : Nat := 118140960795 + 261456 * 2 ^ 59
def prefixEnd_261456 : Nat := 4983230072969 + 3 ^ 40 * 261456 * 2
def baseEnd_261456 : Nat := 119335642668474920797859

theorem tailTrace_261456 : CollatzResearch.WordTrace tailWord_261456 prefixEnd_261456 119335642668474920797859 := by
  unfold tailWord_261456
  simp only [CollatzResearch.WordTrace]
  refine ⟨4768041870398519987446111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6357389160531359983261481 4768041870398519987446111)
  ·
    refine ⟨7152062805597779981169167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4768041870398519987446111 7152062805597779981169167)
    ·
      refine ⟨10728094208396669971753751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7152062805597779981169167 10728094208396669971753751)
      ·
        refine ⟨16092141312595004957630627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10728094208396669971753751 16092141312595004957630627)
        ·
          refine ⟨24138211968892507436445941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16092141312595004957630627 24138211968892507436445941)
          ·
            refine ⟨2262957372083672572166807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24138211968892507436445941 2262957372083672572166807)
            ·
              refine ⟨3394436058125508858250211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2262957372083672572166807 3394436058125508858250211)
              ·
                refine ⟨5091654087188263287375317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3394436058125508858250211 5091654087188263287375317)
                ·
                  refine ⟨119335642668474920797859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5091654087188263287375317 119335642668474920797859)
                  ·
                    rfl

theorem cell20_261456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_261456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261456 prefixEnd_261456 := by exact prefixLift 261456
  have htrace : WordTrace (prefixWord ++ tailWord_261456) baseStart_261456 baseEnd_261456 := by
    simpa [prefixWord, tailWord_261456, baseEnd_261456] using wordTrace_append hprefix tailTrace_261456
  have hstable : (prefixWord ++ tailWord_261456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261456).length < 2 ^ (prefixWord ++ tailWord_261456).sum := by decide
  have hdescent : baseEnd_261456 < baseStart_261456 := by decide
  rcases family_descends (prefixWord ++ tailWord_261456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261487 : List Nat := [1, 1, 2, 1, 3, 1, 6, 5]
def baseStart_261487 : Nat := 118140960795 + 261487 * 2 ^ 59
def prefixEnd_261487 : Nat := 4983230072969 + 3 ^ 40 * 261487 * 2
def baseEnd_261487 : Nat := 39783263971058863588133

theorem tailTrace_261487 : CollatzResearch.WordTrace tailWord_261487 prefixEnd_261487 39783263971058863588133 := by
  unfold tailWord_261487
  simp only [CollatzResearch.WordTrace]
  refine ⟨9537214403684732269270715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6358142935789821512847143 9537214403684732269270715)
  ·
    refine ⟨14305821605527098403906073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9537214403684732269270715 14305821605527098403906073)
    ·
      refine ⟨10729366204145323802929555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14305821605527098403906073 10729366204145323802929555)
      ·
        refine ⟨16094049306217985704394333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10729366204145323802929555 16094049306217985704394333)
        ·
          refine ⟨6035268489831744639147875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16094049306217985704394333 6035268489831744639147875)
          ·
            refine ⟨9052902734747616958721813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6035268489831744639147875 9052902734747616958721813)
            ·
              refine ⟨424354815691294544940085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9052902734747616958721813 424354815691294544940085)
              ·
                refine ⟨39783263971058863588133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 424354815691294544940085 39783263971058863588133)
                ·
                  rfl

theorem cell20_261487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 5].length) (baseStart_261487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261487 prefixEnd_261487 := by exact prefixLift 261487
  have htrace : WordTrace (prefixWord ++ tailWord_261487) baseStart_261487 baseEnd_261487 := by
    simpa [prefixWord, tailWord_261487, baseEnd_261487] using wordTrace_append hprefix tailTrace_261487
  have hstable : (prefixWord ++ tailWord_261487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261487).length < 2 ^ (prefixWord ++ tailWord_261487).sum := by decide
  have hdescent : baseEnd_261487 < baseStart_261487 := by decide
  rcases family_descends (prefixWord ++ tailWord_261487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261577 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 8]
def baseStart_261577 : Nat := 118140960795 + 261577 * 2 ^ 59
def prefixEnd_261577 : Nat := 4983230072969 + 3 ^ 40 * 261577 * 2
def baseEnd_261577 : Nat := 119390870365536277764031

theorem tailTrace_261577 : CollatzResearch.WordTrace tailWord_261577 prefixEnd_261577 119390870365536277764031 := by
  unfold tailWord_261577
  simp only [CollatzResearch.WordTrace]
  refine ⟨9540496973358677640046985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6360331315572451760031323 9540496973358677640046985)
  ·
    refine ⟨7155372730019008230035239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9540496973358677640046985 7155372730019008230035239)
    ·
      refine ⟨10733059095028512345052859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7155372730019008230035239 10733059095028512345052859)
      ·
        refine ⟨16099588642542768517579289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10733059095028512345052859 16099588642542768517579289)
        ·
          refine ⟨12074691481907076388184467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16099588642542768517579289 12074691481907076388184467)
          ·
            refine ⟨18112037222860614582276701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12074691481907076388184467 18112037222860614582276701)
            ·
              refine ⟨6792013958572730468353763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18112037222860614582276701 6792013958572730468353763)
              ·
                refine ⟨10188020937859095702530645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6792013958572730468353763 10188020937859095702530645)
                ·
                  refine ⟨119390870365536277764031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10188020937859095702530645 119390870365536277764031)
                  ·
                    rfl

theorem cell20_261577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_261577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261577 prefixEnd_261577 := by exact prefixLift 261577
  have htrace : WordTrace (prefixWord ++ tailWord_261577) baseStart_261577 baseEnd_261577 := by
    simpa [prefixWord, tailWord_261577, baseEnd_261577] using wordTrace_append hprefix tailTrace_261577
  have hstable : (prefixWord ++ tailWord_261577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261577).length < 2 ^ (prefixWord ++ tailWord_261577).sum := by decide
  have hdescent : baseEnd_261577 < baseStart_261577 := by decide
  rcases family_descends (prefixWord ++ tailWord_261577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261590 : List Nat := [5, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_261590 : Nat := 118140960795 + 261590 * 2 ^ 59
def prefixEnd_261590 : Nat := 4983230072969 + 3 ^ 40 * 261590 * 2
def baseEnd_261590 : Nat := 119396803919766010330645

theorem tailTrace_261590 : CollatzResearch.WordTrace tailWord_261590 prefixEnd_261590 119396803919766010330645 := by
  unfold tailWord_261590
  simp only [CollatzResearch.WordTrace]
  refine ⟨596310695144473803766889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6360647414874387240180149 596310695144473803766889)
  ·
    refine ⟨447233021358355352825167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 596310695144473803766889 447233021358355352825167)
    ·
      refine ⟨670849532037533029237751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 447233021358355352825167 670849532037533029237751)
      ·
        refine ⟨1006274298056299543856627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670849532037533029237751 1006274298056299543856627)
        ·
          refine ⟨1509411447084449315784941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1006274298056299543856627 1509411447084449315784941)
          ·
            refine ⟨566029292656668493419353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1509411447084449315784941 566029292656668493419353)
            ·
              refine ⟨424521969492501370064515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 566029292656668493419353 424521969492501370064515)
              ·
                refine ⟨636782954238752055096773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 424521969492501370064515 636782954238752055096773)
                ·
                  refine ⟨119396803919766010330645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 636782954238752055096773 119396803919766010330645)
                  ·
                    rfl

theorem cell20_261590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_261590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261590 prefixEnd_261590 := by exact prefixLift 261590
  have htrace : WordTrace (prefixWord ++ tailWord_261590) baseStart_261590 baseEnd_261590 := by
    simpa [prefixWord, tailWord_261590, baseEnd_261590] using wordTrace_append hprefix tailTrace_261590
  have hstable : (prefixWord ++ tailWord_261590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261590).length < 2 ^ (prefixWord ++ tailWord_261590).sum := by decide
  have hdescent : baseEnd_261590 < baseStart_261590 := by decide
  rcases family_descends (prefixWord ++ tailWord_261590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261594 : List Nat := [3, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_261594 : Nat := 118140960795 + 261594 * 2 ^ 59
def prefixEnd_261594 : Nat := 4983230072969 + 3 ^ 40 * 261594 * 2
def baseEnd_261594 : Nat := 119398629628759774197295

theorem tailTrace_261594 : CollatzResearch.WordTrace tailWord_261594 prefixEnd_261594 119398629628759774197295 := by
  unfold tailWord_261594
  simp only [CollatzResearch.WordTrace]
  refine ⟨2385279253574272385853959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6360744676198059695610557 2385279253574272385853959)
  ·
    refine ⟨3577918880361408578780939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2385279253574272385853959 3577918880361408578780939)
    ·
      refine ⟨5366878320542112868171409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3577918880361408578780939 5366878320542112868171409)
      ·
        refine ⟨4025158740406584651128557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5366878320542112868171409 4025158740406584651128557)
        ·
          refine ⟨1509434527652469244173209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4025158740406584651128557 1509434527652469244173209)
          ·
            refine ⟨1132075895739351933129907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1509434527652469244173209 1132075895739351933129907)
            ·
              refine ⟨1698113843609027899694861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132075895739351933129907 1698113843609027899694861)
              ·
                refine ⟨636792691353385462385573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1698113843609027899694861 636792691353385462385573)
                ·
                  refine ⟨119398629628759774197295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 636792691353385462385573 119398629628759774197295)
                  ·
                    rfl

theorem cell20_261594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_261594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261594 prefixEnd_261594 := by exact prefixLift 261594
  have htrace : WordTrace (prefixWord ++ tailWord_261594) baseStart_261594 baseEnd_261594 := by
    simpa [prefixWord, tailWord_261594, baseEnd_261594] using wordTrace_append hprefix tailTrace_261594
  have hstable : (prefixWord ++ tailWord_261594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261594).length < 2 ^ (prefixWord ++ tailWord_261594).sum := by decide
  have hdescent : baseEnd_261594 < baseStart_261594 := by decide
  rcases family_descends (prefixWord ++ tailWord_261594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261618 : List Nat := [3, 2, 1, 4, 1, 2, 1, 6]
def baseStart_261618 : Nat := 118140960795 + 261618 * 2 ^ 59
def prefixEnd_261618 : Nat := 4983230072969 + 3 ^ 40 * 261618 * 2
def baseEnd_261618 : Nat := 39803194627574119132399

theorem tailTrace_261618 : CollatzResearch.WordTrace tailWord_261618 prefixEnd_261618 39803194627574119132399 := by
  unfold tailWord_261618
  simp only [CollatzResearch.WordTrace]
  refine ⟨2385498091552535410572377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6361328244140094428193005 2385498091552535410572377)
  ·
    refine ⟨1789123568664401557929283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2385498091552535410572377 1789123568664401557929283)
    ·
      refine ⟨2683685352996602336893925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1789123568664401557929283 2683685352996602336893925)
      ·
        refine ⟨503191003686862938167611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2683685352996602336893925 503191003686862938167611)
        ·
          refine ⟨754786505530294407251417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503191003686862938167611 754786505530294407251417)
          ·
            refine ⟨566089879147720805438563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 754786505530294407251417 566089879147720805438563)
            ·
              refine ⟨849134818721581208157845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566089879147720805438563 849134818721581208157845)
              ·
                refine ⟨39803194627574119132399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 849134818721581208157845 39803194627574119132399)
                ·
                  rfl

theorem cell20_261618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_261618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261618 prefixEnd_261618 := by exact prefixLift 261618
  have htrace : WordTrace (prefixWord ++ tailWord_261618) baseStart_261618 baseEnd_261618 := by
    simpa [prefixWord, tailWord_261618, baseEnd_261618] using wordTrace_append hprefix tailTrace_261618
  have hstable : (prefixWord ++ tailWord_261618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261618).length < 2 ^ (prefixWord ++ tailWord_261618).sum := by decide
  have hdescent : baseEnd_261618 < baseStart_261618 := by decide
  rcases family_descends (prefixWord ++ tailWord_261618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261639 : List Nat := [1, 1, 4, 3, 2, 1, 8]
def baseStart_261639 : Nat := 118140960795 + 261639 * 2 ^ 59
def prefixEnd_261639 : Nat := 4983230072969 + 3 ^ 40 * 261639 * 2
def baseEnd_261639 : Nat := 13268796539437735299679

theorem tailTrace_261639 : CollatzResearch.WordTrace tailWord_261639 prefixEnd_261639 13268796539437735299679 := by
  unfold tailWord_261639
  simp only [CollatzResearch.WordTrace]
  refine ⟨9542758299134062228803971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6361838866089374819202647 9542758299134062228803971)
  ·
    refine ⟨14314137448701093343205957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9542758299134062228803971 14314137448701093343205957)
    ·
      refine ⟨2683900771631455001851117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14314137448701093343205957 2683900771631455001851117)
      ·
        refine ⟨1006462789361795625694169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2683900771631455001851117 1006462789361795625694169)
        ·
          refine ⟨754847092021346719270627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1006462789361795625694169 754847092021346719270627)
          ·
            refine ⟨1132270638032020078905941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754847092021346719270627 1132270638032020078905941)
            ·
              refine ⟨13268796539437735299679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1132270638032020078905941 13268796539437735299679)
              ·
                rfl

theorem cell20_261639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 8].length) (baseStart_261639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261639 prefixEnd_261639 := by exact prefixLift 261639
  have htrace : WordTrace (prefixWord ++ tailWord_261639) baseStart_261639 baseEnd_261639 := by
    simpa [prefixWord, tailWord_261639, baseEnd_261639] using wordTrace_append hprefix tailTrace_261639
  have hstable : (prefixWord ++ tailWord_261639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261639).length < 2 ^ (prefixWord ++ tailWord_261639).sum := by decide
  have hdescent : baseEnd_261639 < baseStart_261639 := by decide
  rcases family_descends (prefixWord ++ tailWord_261639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261656 : List Nat := [2, 1, 2, 3, 4, 1, 2, 5]
def baseStart_261656 : Nat := 118140960795 + 261656 * 2 ^ 59
def prefixEnd_261656 : Nat := 4983230072969 + 3 ^ 40 * 261656 * 2
def baseEnd_261656 : Nat := 39808976039387704710125

theorem tailTrace_261656 : CollatzResearch.WordTrace tailWord_261656 prefixEnd_261656 39808976039387704710125 := by
  unfold tailWord_261656
  simp only [CollatzResearch.WordTrace]
  refine ⟨4771689170036237066086411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6362252226714982754781881 4771689170036237066086411)
  ·
    refine ⟨7157533755054355599129617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4771689170036237066086411 7157533755054355599129617)
    ·
      refine ⟨5368150316290766699347213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7157533755054355599129617 5368150316290766699347213)
      ·
        refine ⟨2013056368609037512255205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5368150316290766699347213 2013056368609037512255205)
        ·
          refine ⟨377448069114194533547851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2013056368609037512255205 377448069114194533547851)
          ·
            refine ⟨566172103671291800321777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377448069114194533547851 566172103671291800321777)
            ·
              refine ⟨424629077753468850241333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 566172103671291800321777 424629077753468850241333)
              ·
                refine ⟨39808976039387704710125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 424629077753468850241333 39808976039387704710125)
                ·
                  rfl

theorem cell20_261656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_261656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261656 prefixEnd_261656 := by exact prefixLift 261656
  have htrace : WordTrace (prefixWord ++ tailWord_261656) baseStart_261656 baseEnd_261656 := by
    simpa [prefixWord, tailWord_261656, baseEnd_261656] using wordTrace_append hprefix tailTrace_261656
  have hstable : (prefixWord ++ tailWord_261656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261656).length < 2 ^ (prefixWord ++ tailWord_261656).sum := by decide
  have hdescent : baseEnd_261656 < baseStart_261656 := by decide
  rcases family_descends (prefixWord ++ tailWord_261656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261701 : List Nat := [1, 3, 1, 1, 1, 4, 4, 2, 3]
def baseStart_261701 : Nat := 118140960795 + 261701 * 2 ^ 59
def prefixEnd_261701 : Nat := 4983230072969 + 3 ^ 40 * 261701 * 2
def baseEnd_261701 : Nat := 119447467344342957630191

theorem tailTrace_261701 : CollatzResearch.WordTrace tailWord_261701 prefixEnd_261701 119447467344342957630191 := by
  unfold tailWord_261701
  simp only [CollatzResearch.WordTrace]
  refine ⟨9545019624909446817560957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6363346416606297878373971 9545019624909446817560957)
  ·
    refine ⟨3579382359341042556585359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9545019624909446817560957 3579382359341042556585359)
    ·
      refine ⟨5369073539011563834878039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3579382359341042556585359 5369073539011563834878039)
      ·
        refine ⟨8053610308517345752317059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5369073539011563834878039 8053610308517345752317059)
        ·
          refine ⟨12080415462776018628475589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8053610308517345752317059 12080415462776018628475589)
          ·
            refine ⟨2265077899270503492839173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12080415462776018628475589 2265077899270503492839173)
            ·
              refine ⟨424702106113219404907345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2265077899270503492839173 424702106113219404907345)
              ·
                refine ⟨318526579584914553680509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424702106113219404907345 318526579584914553680509)
                ·
                  refine ⟨119447467344342957630191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 318526579584914553680509 119447467344342957630191)
                  ·
                    rfl

theorem cell20_261701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_261701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261701 prefixEnd_261701 := by exact prefixLift 261701
  have htrace : WordTrace (prefixWord ++ tailWord_261701) baseStart_261701 baseEnd_261701 := by
    simpa [prefixWord, tailWord_261701, baseEnd_261701] using wordTrace_append hprefix tailTrace_261701
  have hstable : (prefixWord ++ tailWord_261701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261701).length < 2 ^ (prefixWord ++ tailWord_261701).sum := by decide
  have hdescent : baseEnd_261701 < baseStart_261701 := by decide
  rcases family_descends (prefixWord ++ tailWord_261701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261732 : List Nat := [2, 3, 1, 1, 2, 4, 3, 4]
def baseStart_261732 : Nat := 118140960795 + 261732 * 2 ^ 59
def prefixEnd_261732 : Nat := 4983230072969 + 3 ^ 40 * 261732 * 2
def baseEnd_261732 : Nat := 39820538863014875865577

theorem tailTrace_261732 : CollatzResearch.WordTrace tailWord_261732 prefixEnd_261732 39820538863014875865577 := by
  unfold tailWord_261732
  simp only [CollatzResearch.WordTrace]
  refine ⟨4773075143898569555969725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6364100191864759407959633 4773075143898569555969725)
  ·
    refine ⟨1789903178961963583488647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4773075143898569555969725 1789903178961963583488647)
    ·
      refine ⟨2684854768442945375232971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1789903178961963583488647 2684854768442945375232971)
      ·
        refine ⟨4027282152664418062849457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2684854768442945375232971 4027282152664418062849457)
        ·
          refine ⟨3020461614498313547137093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4027282152664418062849457 3020461614498313547137093)
          ·
            refine ⟨566336552718433790088205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3020461614498313547137093 566336552718433790088205)
            ·
              refine ⟨212376207269412671283077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 566336552718433790088205 212376207269412671283077)
              ·
                refine ⟨39820538863014875865577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212376207269412671283077 39820538863014875865577)
                ·
                  rfl

theorem cell20_261732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 4].length) (baseStart_261732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261732 prefixEnd_261732 := by exact prefixLift 261732
  have htrace : WordTrace (prefixWord ++ tailWord_261732) baseStart_261732 baseEnd_261732 := by
    simpa [prefixWord, tailWord_261732, baseEnd_261732] using wordTrace_append hprefix tailTrace_261732
  have hstable : (prefixWord ++ tailWord_261732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261732).length < 2 ^ (prefixWord ++ tailWord_261732).sum := by decide
  have hdescent : baseEnd_261732 < baseStart_261732 := by decide
  rcases family_descends (prefixWord ++ tailWord_261732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261760 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 5]
def baseStart_261760 : Nat := 118140960795 + 261760 * 2 ^ 59
def prefixEnd_261760 : Nat := 4983230072969 + 3 ^ 40 * 261760 * 2
def baseEnd_261760 : Nat := 119474396552000974663283

theorem tailTrace_261760 : CollatzResearch.WordTrace tailWord_261760 prefixEnd_261760 119474396552000974663283 := by
  unfold tailWord_261760
  simp only [CollatzResearch.WordTrace]
  refine ⟨4773585765847849946979367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6364781021130466595972489 4773585765847849946979367)
  ·
    refine ⟨7160378648771774920469051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4773585765847849946979367 7160378648771774920469051)
    ·
      refine ⟨10740567973157662380703577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7160378648771774920469051 10740567973157662380703577)
      ·
        refine ⟨8055425979868246785527683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10740567973157662380703577 8055425979868246785527683)
        ·
          refine ⟨12083138969802370178291525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8055425979868246785527683 12083138969802370178291525)
          ·
            refine ⟨2265588556837944408429661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12083138969802370178291525 2265588556837944408429661)
            ·
              refine ⟨849595708814229153161123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2265588556837944408429661 849595708814229153161123)
              ·
                refine ⟨1274393563221343729741685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 849595708814229153161123 1274393563221343729741685)
                ·
                  refine ⟨119474396552000974663283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1274393563221343729741685 119474396552000974663283)
                  ·
                    rfl

theorem cell20_261760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_261760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261760 prefixEnd_261760 := by exact prefixLift 261760
  have htrace : WordTrace (prefixWord ++ tailWord_261760) baseStart_261760 baseEnd_261760 := by
    simpa [prefixWord, tailWord_261760, baseEnd_261760] using wordTrace_append hprefix tailTrace_261760
  have hstable : (prefixWord ++ tailWord_261760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261760).length < 2 ^ (prefixWord ++ tailWord_261760).sum := by decide
  have hdescent : baseEnd_261760 < baseStart_261760 := by decide
  rcases family_descends (prefixWord ++ tailWord_261760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261784 : List Nat := [2, 1, 2, 4, 1, 2, 2, 2, 4]
def baseStart_261784 : Nat := 118140960795 + 261784 * 2 ^ 59
def prefixEnd_261784 : Nat := 4983230072969 + 3 ^ 40 * 261784 * 2
def baseEnd_261784 : Nat := 119485350805963557863185

theorem tailTrace_261784 : CollatzResearch.WordTrace tailWord_261784 prefixEnd_261784 119485350805963557863185 := by
  unfold tailWord_261784
  simp only [CollatzResearch.WordTrace]
  refine ⟨4774023441804375996416203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6365364589072501328554937 4774023441804375996416203)
  ·
    refine ⟨7161035162706563994624305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4774023441804375996416203 7161035162706563994624305)
    ·
      refine ⟨5370776372029922995968229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7161035162706563994624305 5370776372029922995968229)
      ·
        refine ⟨1007020569755610561744043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5370776372029922995968229 1007020569755610561744043)
        ·
          refine ⟨1510530854633415842616065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007020569755610561744043 1510530854633415842616065)
          ·
            refine ⟨1132898140975061881962049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1510530854633415842616065 1132898140975061881962049)
            ·
              refine ⟨849673605731296411471537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1132898140975061881962049 849673605731296411471537)
              ·
                refine ⟨637255204298472308603653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 849673605731296411471537 637255204298472308603653)
                ·
                  refine ⟨119485350805963557863185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 637255204298472308603653 119485350805963557863185)
                  ·
                    rfl

theorem cell20_261784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_261784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261784 prefixEnd_261784 := by exact prefixLift 261784
  have htrace : WordTrace (prefixWord ++ tailWord_261784) baseStart_261784 baseEnd_261784 := by
    simpa [prefixWord, tailWord_261784, baseEnd_261784] using wordTrace_append hprefix tailTrace_261784
  have hstable : (prefixWord ++ tailWord_261784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261784).length < 2 ^ (prefixWord ++ tailWord_261784).sum := by decide
  have hdescent : baseEnd_261784 < baseStart_261784 := by decide
  rcases family_descends (prefixWord ++ tailWord_261784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261814 : List Nat := [5, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_261814 : Nat := 118140960795 + 261814 * 2 ^ 59
def prefixEnd_261814 : Nat := 4983230072969 + 3 ^ 40 * 261814 * 2
def baseEnd_261814 : Nat := 119499043623416786863063

theorem tailTrace_261814 : CollatzResearch.WordTrace tailWord_261814 prefixEnd_261814 119499043623416786863063 := by
  unfold tailWord_261814
  simp only [CollatzResearch.WordTrace]
  refine ⟨596821317093754194776531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6366094049000044744282997 596821317093754194776531)
  ·
    refine ⟨895231975640631292164797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 596821317093754194776531 895231975640631292164797)
    ·
      refine ⟨335711990865236734561799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 895231975640631292164797 335711990865236734561799)
      ·
        refine ⟨503567986297855101842699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335711990865236734561799 503567986297855101842699)
        ·
          refine ⟨755351979446782652764049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503567986297855101842699 755351979446782652764049)
          ·
            refine ⟨566513984585086989573037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 755351979446782652764049 566513984585086989573037)
            ·
              refine ⟨212442744219407621089889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 566513984585086989573037 212442744219407621089889)
              ·
                refine ⟨159332058164555715817417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212442744219407621089889 159332058164555715817417)
                ·
                  refine ⟨119499043623416786863063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159332058164555715817417 119499043623416786863063)
                  ·
                    rfl

theorem cell20_261814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_261814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261814 prefixEnd_261814 := by exact prefixLift 261814
  have htrace : WordTrace (prefixWord ++ tailWord_261814) baseStart_261814 baseEnd_261814 := by
    simpa [prefixWord, tailWord_261814, baseEnd_261814] using wordTrace_append hprefix tailTrace_261814
  have hstable : (prefixWord ++ tailWord_261814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261814).length < 2 ^ (prefixWord ++ tailWord_261814).sum := by decide
  have hdescent : baseEnd_261814 < baseStart_261814 := by decide
  rcases family_descends (prefixWord ++ tailWord_261814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261818 : List Nat := [3, 1, 1, 1, 2, 5, 3, 2, 2]
def baseStart_261818 : Nat := 118140960795 + 261818 * 2 ^ 59
def prefixEnd_261818 : Nat := 4983230072969 + 3 ^ 40 * 261818 * 2
def baseEnd_261818 : Nat := 119500869332410550729713

theorem tailTrace_261818 : CollatzResearch.WordTrace tailWord_261818 prefixEnd_261818 119500869332410550729713 := by
  unfold tailWord_261818
  simp only [CollatzResearch.WordTrace]
  refine ⟨2387321741371393949892527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6366191310323717199713405 2387321741371393949892527)
  ·
    refine ⟨3580982612057090924838791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2387321741371393949892527 3580982612057090924838791)
    ·
      refine ⟨5371473918085636387258187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3580982612057090924838791 5371473918085636387258187)
      ·
        refine ⟨8057210877128454580887281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5371473918085636387258187 8057210877128454580887281)
        ·
          refine ⟨6042908157846340935665461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8057210877128454580887281 6042908157846340935665461)
          ·
            refine ⟨566522639798094462718637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6042908157846340935665461 566522639798094462718637)
            ·
              refine ⟨212445989924285423519489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 566522639798094462718637 212445989924285423519489)
              ·
                refine ⟨159334492443214067639617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212445989924285423519489 159334492443214067639617)
                ·
                  refine ⟨119500869332410550729713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159334492443214067639617 119500869332410550729713)
                  ·
                    rfl

theorem cell20_261818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_261818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261818 prefixEnd_261818 := by exact prefixLift 261818
  have htrace : WordTrace (prefixWord ++ tailWord_261818) baseStart_261818 baseEnd_261818 := by
    simpa [prefixWord, tailWord_261818, baseEnd_261818] using wordTrace_append hprefix tailTrace_261818
  have hstable : (prefixWord ++ tailWord_261818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261818).length < 2 ^ (prefixWord ++ tailWord_261818).sum := by decide
  have hdescent : baseEnd_261818 < baseStart_261818 := by decide
  rcases family_descends (prefixWord ++ tailWord_261818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261898 : List Nat := [3, 1, 2, 2, 1, 4, 1, 2, 4]
def baseStart_261898 : Nat := 118140960795 + 261898 * 2 ^ 59
def prefixEnd_261898 : Nat := 4983230072969 + 3 ^ 40 * 261898 * 2
def baseEnd_261898 : Nat := 119537383512285828062719

theorem tailTrace_261898 : CollatzResearch.WordTrace tailWord_261898 prefixEnd_261898 119537383512285828062719 := by
  unfold tailWord_261898
  simp only [CollatzResearch.WordTrace]
  refine ⟨2388051201298937365620587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6368136536797166308321565 2388051201298937365620587)
  ·
    refine ⟨3582076801948406048430881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2388051201298937365620587 3582076801948406048430881)
    ·
      refine ⟨2686557601461304536323161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3582076801948406048430881 2686557601461304536323161)
      ·
        refine ⟨2014918201095978402242371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2686557601461304536323161 2014918201095978402242371)
        ·
          refine ⟨3022377301643967603363557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2014918201095978402242371 3022377301643967603363557)
          ·
            refine ⟨566695744058243925630667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3022377301643967603363557 566695744058243925630667)
            ·
              refine ⟨850043616087365888446001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 566695744058243925630667 850043616087365888446001)
              ·
                refine ⟨637532712065524416334501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 850043616087365888446001 637532712065524416334501)
                ·
                  refine ⟨119537383512285828062719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 637532712065524416334501 119537383512285828062719)
                  ·
                    rfl

theorem cell20_261898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_261898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261898 prefixEnd_261898 := by exact prefixLift 261898
  have htrace : WordTrace (prefixWord ++ tailWord_261898) baseStart_261898 baseEnd_261898 := by
    simpa [prefixWord, tailWord_261898, baseEnd_261898] using wordTrace_append hprefix tailTrace_261898
  have hstable : (prefixWord ++ tailWord_261898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261898).length < 2 ^ (prefixWord ++ tailWord_261898).sum := by decide
  have hdescent : baseEnd_261898 < baseStart_261898 := by decide
  rcases family_descends (prefixWord ++ tailWord_261898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261919 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 6]
def baseStart_261919 : Nat := 118140960795 + 261919 * 2 ^ 59
def prefixEnd_261919 : Nat := 4983230072969 + 3 ^ 40 * 261919 * 2
def baseEnd_261919 : Nat := 119546968484503088362633

theorem tailTrace_261919 : CollatzResearch.WordTrace tailWord_261919 prefixEnd_261919 119546968484503088362633 := by
  unfold tailWord_261919
  simp only [CollatzResearch.WordTrace]
  refine ⟨9552970738119670048996811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6368647158746446699331207 9552970738119670048996811)
  ·
    refine ⟨14329456107179505073495217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9552970738119670048996811 14329456107179505073495217)
    ·
      refine ⟨10747092080384628805121413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14329456107179505073495217 10747092080384628805121413)
      ·
        refine ⟨2015079765072117900960265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10747092080384628805121413 2015079765072117900960265)
        ·
          refine ⟨1511309823804088425720199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2015079765072117900960265 1511309823804088425720199)
          ·
            refine ⟨2266964735706132638580299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1511309823804088425720199 2266964735706132638580299)
            ·
              refine ⟨3400447103559198957870449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2266964735706132638580299 3400447103559198957870449)
              ·
                refine ⟨2550335327669399218402837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3400447103559198957870449 2550335327669399218402837)
                ·
                  refine ⟨119546968484503088362633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2550335327669399218402837 119546968484503088362633)
                  ·
                    rfl

theorem cell20_261919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_261919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261919 prefixEnd_261919 := by exact prefixLift 261919
  have htrace : WordTrace (prefixWord ++ tailWord_261919) baseStart_261919 baseEnd_261919 := by
    simpa [prefixWord, tailWord_261919, baseEnd_261919] using wordTrace_append hprefix tailTrace_261919
  have hstable : (prefixWord ++ tailWord_261919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261919).length < 2 ^ (prefixWord ++ tailWord_261919).sum := by decide
  have hdescent : baseEnd_261919 < baseStart_261919 := by decide
  rcases family_descends (prefixWord ++ tailWord_261919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261946 : List Nat := [3, 1, 1, 1, 5, 2, 3, 1, 3]
def baseStart_261946 : Nat := 118140960795 + 261946 * 2 ^ 59
def prefixEnd_261946 : Nat := 4983230072969 + 3 ^ 40 * 261946 * 2
def baseEnd_261946 : Nat := 119559292020210994462523

theorem tailTrace_261946 : CollatzResearch.WordTrace tailWord_261946 prefixEnd_261946 119559292020210994462523 := by
  unfold tailWord_261946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2388488877255463415057423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6369303672681235773486461 2388488877255463415057423)
  ·
    refine ⟨3582733315883195122586135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2388488877255463415057423 3582733315883195122586135)
    ·
      refine ⟨5374099973824792683879203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3582733315883195122586135 5374099973824792683879203)
      ·
        refine ⟨8061149960737189025818805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5374099973824792683879203 8061149960737189025818805)
        ·
          refine ⟨755732808819111471170513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8061149960737189025818805 755732808819111471170513)
          ·
            refine ⟨566799606614333603377885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 755732808819111471170513 566799606614333603377885)
            ·
              refine ⟨212549852480375101266707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 566799606614333603377885 212549852480375101266707)
              ·
                refine ⟨318824778720562651900061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 212549852480375101266707 318824778720562651900061)
                ·
                  refine ⟨119559292020210994462523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 318824778720562651900061 119559292020210994462523)
                  ·
                    rfl

theorem cell20_261946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_261946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261946 prefixEnd_261946 := by exact prefixLift 261946
  have htrace : WordTrace (prefixWord ++ tailWord_261946) baseStart_261946 baseEnd_261946 := by
    simpa [prefixWord, tailWord_261946, baseEnd_261946] using wordTrace_append hprefix tailTrace_261946
  have hstable : (prefixWord ++ tailWord_261946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261946).length < 2 ^ (prefixWord ++ tailWord_261946).sum := by decide
  have hdescent : baseEnd_261946 < baseStart_261946 := by decide
  rcases family_descends (prefixWord ++ tailWord_261946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261957 : List Nat := [1, 3, 1, 1, 1, 2, 3, 4, 4]
def baseStart_261957 : Nat := 118140960795 + 261957 * 2 ^ 59
def prefixEnd_261957 : Nat := 4983230072969 + 3 ^ 40 * 261957 * 2
def baseEnd_261957 : Nat := 119564312719943845095811

theorem tailTrace_261957 : CollatzResearch.WordTrace tailWord_261957 prefixEnd_261957 119564312719943845095811 := by
  unfold tailWord_261957
  simp only [CollatzResearch.WordTrace]
  refine ⟨9554356711982002538880125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6369571141321335025920083 9554356711982002538880125)
  ·
    refine ⟨3582883766993250952080047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9554356711982002538880125 3582883766993250952080047)
    ·
      refine ⟨5374325650489876428120071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3582883766993250952080047 5374325650489876428120071)
      ·
        refine ⟨8061488475734814642180107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5374325650489876428120071 8061488475734814642180107)
        ·
          refine ⟨12092232713602221963270161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8061488475734814642180107 12092232713602221963270161)
          ·
            refine ⟨9069174535201666472452621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12092232713602221963270161 9069174535201666472452621)
            ·
              refine ⟨3400940450700624927169733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9069174535201666472452621 3400940450700624927169733)
              ·
                refine ⟨637676334506367173844325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3400940450700624927169733 637676334506367173844325)
                ·
                  refine ⟨119564312719943845095811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 637676334506367173844325 119564312719943845095811)
                  ·
                    rfl

theorem cell20_261957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_261957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261957 prefixEnd_261957 := by exact prefixLift 261957
  have htrace : WordTrace (prefixWord ++ tailWord_261957) baseStart_261957 baseEnd_261957 := by
    simpa [prefixWord, tailWord_261957, baseEnd_261957] using wordTrace_append hprefix tailTrace_261957
  have hstable : (prefixWord ++ tailWord_261957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261957).length < 2 ^ (prefixWord ++ tailWord_261957).sum := by decide
  have hdescent : baseEnd_261957 < baseStart_261957 := by decide
  rcases family_descends (prefixWord ++ tailWord_261957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261960 : List Nat := [2, 1, 3, 1, 1, 6, 2, 4]
def baseStart_261960 : Nat := 118140960795 + 261960 * 2 ^ 59
def prefixEnd_261960 : Nat := 4983230072969 + 3 ^ 40 * 261960 * 2
def baseEnd_261960 : Nat := 39855227333896389331933

theorem tailTrace_261960 : CollatzResearch.WordTrace tailWord_261960 prefixEnd_261960 39855227333896389331933 := by
  unfold tailWord_261960
  simp only [CollatzResearch.WordTrace]
  refine ⟨4777233065485567025619667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6369644087314089367492889 4777233065485567025619667)
  ·
    refine ⟨7165849598228350538429501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4777233065485567025619667 7165849598228350538429501)
    ·
      refine ⟨2687193599335631451911063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7165849598228350538429501 2687193599335631451911063)
      ·
        refine ⟨4030790399003447177866595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2687193599335631451911063 4030790399003447177866595)
        ·
          refine ⟨6046185598505170766799893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4030790399003447177866595 6046185598505170766799893)
          ·
            refine ⟨283414949929929879693745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6046185598505170766799893 283414949929929879693745)
            ·
              refine ⟨212561212447447409770309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283414949929929879693745 212561212447447409770309)
              ·
                refine ⟨39855227333896389331933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212561212447447409770309 39855227333896389331933)
                ·
                  rfl

theorem cell20_261960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 2, 4].length) (baseStart_261960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261960 prefixEnd_261960 := by exact prefixLift 261960
  have htrace : WordTrace (prefixWord ++ tailWord_261960) baseStart_261960 baseEnd_261960 := by
    simpa [prefixWord, tailWord_261960, baseEnd_261960] using wordTrace_append hprefix tailTrace_261960
  have hstable : (prefixWord ++ tailWord_261960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261960).length < 2 ^ (prefixWord ++ tailWord_261960).sum := by decide
  have hdescent : baseEnd_261960 < baseStart_261960 := by decide
  rcases family_descends (prefixWord ++ tailWord_261960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261970 : List Nat := [3, 2, 2, 1, 1, 5, 1, 3, 2]
def baseStart_261970 : Nat := 118140960795 + 261970 * 2 ^ 59
def prefixEnd_261970 : Nat := 4983230072969 + 3 ^ 40 * 261970 * 2
def baseEnd_261970 : Nat := 119570246274173577662425

theorem tailTrace_261970 : CollatzResearch.WordTrace tailWord_261970 prefixEnd_261970 119570246274173577662425 := by
  unfold tailWord_261970
  simp only [CollatzResearch.WordTrace]
  refine ⟨2388707715233726439775841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6369887240623270506068909 2388707715233726439775841)
  ·
    refine ⟨1791530786425294829831881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2388707715233726439775841 1791530786425294829831881)
    ·
      refine ⟨1343648089818971122373911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1791530786425294829831881 1343648089818971122373911)
      ·
        refine ⟨2015472134728456683560867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1343648089818971122373911 2015472134728456683560867)
        ·
          refine ⟨3023208202092685025341301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2015472134728456683560867 3023208202092685025341301)
          ·
            refine ⟨283425768946189221125747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3023208202092685025341301 283425768946189221125747)
            ·
              refine ⟨425138653419283831688621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283425768946189221125747 425138653419283831688621)
              ·
                refine ⟨159426995032231436883233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 425138653419283831688621 159426995032231436883233)
                ·
                  refine ⟨119570246274173577662425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159426995032231436883233 119570246274173577662425)
                  ·
                    rfl

theorem cell20_261970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 2].length) (baseStart_261970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261970 prefixEnd_261970 := by exact prefixLift 261970
  have htrace : WordTrace (prefixWord ++ tailWord_261970) baseStart_261970 baseEnd_261970 := by
    simpa [prefixWord, tailWord_261970, baseEnd_261970] using wordTrace_append hprefix tailTrace_261970
  have hstable : (prefixWord ++ tailWord_261970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261970).length < 2 ^ (prefixWord ++ tailWord_261970).sum := by decide
  have hdescent : baseEnd_261970 < baseStart_261970 := by decide
  rcases family_descends (prefixWord ++ tailWord_261970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_261998 : List Nat := [4, 1, 2, 3, 1, 2, 2, 5]
def baseStart_261998 : Nat := 118140960795 + 261998 * 2 ^ 59
def prefixEnd_261998 : Nat := 4983230072969 + 3 ^ 40 * 261998 * 2
def baseEnd_261998 : Nat := 39861008745709974909659

theorem tailTrace_261998 : CollatzResearch.WordTrace tailWord_261998 prefixEnd_261998 39861008745709974909659 := by
  unfold tailWord_261998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1194481513104183317640331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6370568069888977694081765 1194481513104183317640331)
  ·
    refine ⟨1791722269656274976460497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1194481513104183317640331 1791722269656274976460497)
    ·
      refine ⟨1343791702242206232345373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1791722269656274976460497 1343791702242206232345373)
      ·
        refine ⟨503921888340827337129515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1343791702242206232345373 503921888340827337129515)
        ·
          refine ⟨755882832511241005694273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 503921888340827337129515 755882832511241005694273)
          ·
            refine ⟨566912124383430754270705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 755882832511241005694273 566912124383430754270705)
            ·
              refine ⟨425184093287573065703029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 566912124383430754270705 425184093287573065703029)
              ·
                refine ⟨39861008745709974909659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 425184093287573065703029 39861008745709974909659)
                ·
                  rfl

theorem cell20_261998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_261998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_261998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_261998 prefixEnd_261998 := by exact prefixLift 261998
  have htrace : WordTrace (prefixWord ++ tailWord_261998) baseStart_261998 baseEnd_261998 := by
    simpa [prefixWord, tailWord_261998, baseEnd_261998] using wordTrace_append hprefix tailTrace_261998
  have hstable : (prefixWord ++ tailWord_261998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_261998).length < 2 ^ (prefixWord ++ tailWord_261998).sum := by decide
  have hdescent : baseEnd_261998 < baseStart_261998 := by decide
  rcases family_descends (prefixWord ++ tailWord_261998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262005 : List Nat := [1, 3, 4, 1, 1, 1, 3, 3, 3]
def baseStart_262005 : Nat := 118140960795 + 262005 * 2 ^ 59
def prefixEnd_262005 : Nat := 4983230072969 + 3 ^ 40 * 262005 * 2
def baseEnd_262005 : Nat := 119586221227869011495615

theorem tailTrace_262005 : CollatzResearch.WordTrace tailWord_262005 prefixEnd_262005 119586221227869011495615 := by
  unfold tailWord_262005
  simp only [CollatzResearch.WordTrace]
  refine ⟨9556107415808106736627469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6370738277205404491084979 9556107415808106736627469)
  ·
    refine ⟨3583540280928040026235301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9556107415808106736627469 3583540280928040026235301)
    ·
      refine ⟨671913802674007504919119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3583540280928040026235301 671913802674007504919119)
      ·
        refine ⟨1007870704011011257378679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 671913802674007504919119 1007870704011011257378679)
        ·
          refine ⟨1511806056016516886068019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1007870704011011257378679 1511806056016516886068019)
          ·
            refine ⟨2267709084024775329102029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1511806056016516886068019 2267709084024775329102029)
            ·
              refine ⟨850390906509290748413261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2267709084024775329102029 850390906509290748413261)
              ·
                refine ⟨318896589940984030654973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 850390906509290748413261 318896589940984030654973)
                ·
                  refine ⟨119586221227869011495615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 318896589940984030654973 119586221227869011495615)
                  ·
                    rfl

theorem cell20_262005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_262005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262005 prefixEnd_262005 := by exact prefixLift 262005
  have htrace : WordTrace (prefixWord ++ tailWord_262005) baseStart_262005 baseEnd_262005 := by
    simpa [prefixWord, tailWord_262005, baseEnd_262005] using wordTrace_append hprefix tailTrace_262005
  have hstable : (prefixWord ++ tailWord_262005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262005).length < 2 ^ (prefixWord ++ tailWord_262005).sum := by decide
  have hdescent : baseEnd_262005 < baseStart_262005 := by decide
  rcases family_descends (prefixWord ++ tailWord_262005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262038 : List Nat := [5, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_262038 : Nat := 118140960795 + 262038 * 2 ^ 59
def prefixEnd_262038 : Nat := 4983230072969 + 3 ^ 40 * 262038 * 2
def baseEnd_262038 : Nat := 119601283327067563395481

theorem tailTrace_262038 : CollatzResearch.WordTrace tailWord_262038 prefixEnd_262038 119601283327067563395481 := by
  unfold tailWord_262038
  simp only [CollatzResearch.WordTrace]
  refine ⟨597331939043034585786173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6371540683125702248385845 597331939043034585786173)
  ·
    refine ⟨223999477141137969669815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 597331939043034585786173 223999477141137969669815)
    ·
      refine ⟨335999215711706954504723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223999477141137969669815 335999215711706954504723)
      ·
        refine ⟨503998823567560431757085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335999215711706954504723 503998823567560431757085)
        ·
          refine ⟨188999558837835161908907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 503998823567560431757085 188999558837835161908907)
          ·
            refine ⟨283499338256752742863361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188999558837835161908907 283499338256752742863361)
            ·
              refine ⟨212624503692564557147521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283499338256752742863361 212624503692564557147521)
              ·
                refine ⟨159468377769423417860641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212624503692564557147521 159468377769423417860641)
                ·
                  refine ⟨119601283327067563395481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159468377769423417860641 119601283327067563395481)
                  ·
                    rfl

theorem cell20_262038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_262038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262038 prefixEnd_262038 := by exact prefixLift 262038
  have htrace : WordTrace (prefixWord ++ tailWord_262038) baseStart_262038 baseEnd_262038 := by
    simpa [prefixWord, tailWord_262038, baseEnd_262038] using wordTrace_append hprefix tailTrace_262038
  have hstable : (prefixWord ++ tailWord_262038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262038).length < 2 ^ (prefixWord ++ tailWord_262038).sum := by decide
  have hdescent : baseEnd_262038 < baseStart_262038 := by decide
  rcases family_descends (prefixWord ++ tailWord_262038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262116 : List Nat := [2, 3, 1, 1, 1, 1, 4, 7]
def baseStart_262116 : Nat := 118140960795 + 262116 * 2 ^ 59
def prefixEnd_262116 : Nat := 4983230072969 + 3 ^ 40 * 262116 * 2
def baseEnd_262116 : Nat := 39878961550815319598387

theorem tailTrace_262116 : CollatzResearch.WordTrace tailWord_262116 prefixEnd_262116 39878961550815319598387 := by
  unfold tailWord_262116
  simp only [CollatzResearch.WordTrace]
  refine ⟨4780077959202986346959101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6373437278937315129278801 4780077959202986346959101)
  ·
    refine ⟨1792529234701119880109663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4780077959202986346959101 1792529234701119880109663)
    ·
      refine ⟨2688793852051679820164495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1792529234701119880109663 2688793852051679820164495)
      ·
        refine ⟨4033190778077519730246743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2688793852051679820164495 4033190778077519730246743)
        ·
          refine ⟨6049786167116279595370115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4033190778077519730246743 6049786167116279595370115)
          ·
            refine ⟨9074679250674419393055173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6049786167116279595370115 9074679250674419393055173)
            ·
              refine ⟨1701502359501453636197845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9074679250674419393055173 1701502359501453636197845)
              ·
                refine ⟨39878961550815319598387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1701502359501453636197845 39878961550815319598387)
                ·
                  rfl

theorem cell20_262116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_262116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262116 prefixEnd_262116 := by exact prefixLift 262116
  have htrace : WordTrace (prefixWord ++ tailWord_262116) baseStart_262116 baseEnd_262116 := by
    simpa [prefixWord, tailWord_262116, baseEnd_262116] using wordTrace_append hprefix tailTrace_262116
  have hstable : (prefixWord ++ tailWord_262116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262116).length < 2 ^ (prefixWord ++ tailWord_262116).sum := by decide
  have hdescent : baseEnd_262116 < baseStart_262116 := by decide
  rcases family_descends (prefixWord ++ tailWord_262116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262126 : List Nat := [4, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_262126 : Nat := 118140960795 + 262126 * 2 ^ 59
def prefixEnd_262126 : Nat := 4983230072969 + 3 ^ 40 * 262126 * 2
def baseEnd_262126 : Nat := 119641448924930368461787

theorem tailTrace_262126 : CollatzResearch.WordTrace tailWord_262126 prefixEnd_262126 119641448924930368461787 := by
  unfold tailWord_262126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1195065081046218050222779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6373680432246496267854821 1195065081046218050222779)
  ·
    refine ⟨1792597621569327075334169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1195065081046218050222779 1792597621569327075334169)
    ·
      refine ⟨1344448216176995306500627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1792597621569327075334169 1344448216176995306500627)
      ·
        refine ⟨2016672324265492959750941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1344448216176995306500627 2016672324265492959750941)
        ·
          refine ⟨756252121599559859906603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2016672324265492959750941 756252121599559859906603)
          ·
            refine ⟨1134378182399339789859905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756252121599559859906603 1134378182399339789859905)
            ·
              refine ⟨850783636799504842394929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1134378182399339789859905 850783636799504842394929)
              ·
                refine ⟨638087727599628631796197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 850783636799504842394929 638087727599628631796197)
                ·
                  refine ⟨119641448924930368461787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 638087727599628631796197 119641448924930368461787)
                  ·
                    rfl

theorem cell20_262126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_262126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262126 prefixEnd_262126 := by exact prefixLift 262126
  have htrace : WordTrace (prefixWord ++ tailWord_262126) baseStart_262126 baseEnd_262126 := by
    simpa [prefixWord, tailWord_262126, baseEnd_262126] using wordTrace_append hprefix tailTrace_262126
  have hstable : (prefixWord ++ tailWord_262126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262126).length < 2 ^ (prefixWord ++ tailWord_262126).sum := by decide
  have hdescent : baseEnd_262126 < baseStart_262126 := by decide
  rcases family_descends (prefixWord ++ tailWord_262126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262129 : List Nat := [1, 2, 2, 2, 6, 1, 2, 4]
def baseStart_262129 : Nat := 118140960795 + 262129 * 2 ^ 59
def prefixEnd_262129 : Nat := 4983230072969 + 3 ^ 40 * 262129 * 2
def baseEnd_262129 : Nat := 39880939402225230453925

theorem tailTrace_262129 : CollatzResearch.WordTrace tailWord_262129 prefixEnd_262129 39880939402225230453925 := by
  unfold tailWord_262129
  simp only [CollatzResearch.WordTrace]
  refine ⟨9560630067358875914141441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6373753378239250609427627 9560630067358875914141441)
  ·
    refine ⟨7170472550519156935606081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9560630067358875914141441 7170472550519156935606081)
    ·
      refine ⟨5377854412889367701704561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7170472550519156935606081 5377854412889367701704561)
      ·
        refine ⟨4033390809667025776278421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5377854412889367701704561 4033390809667025776278421)
        ·
          refine ⟨189065194203141833263051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4033390809667025776278421 189065194203141833263051)
          ·
            refine ⟨283597791304712749894577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189065194203141833263051 283597791304712749894577)
            ·
              refine ⟨212698343478534562420933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283597791304712749894577 212698343478534562420933)
              ·
                refine ⟨39880939402225230453925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212698343478534562420933 39880939402225230453925)
                ·
                  rfl

theorem cell20_262129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 4].length) (baseStart_262129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262129 prefixEnd_262129 := by exact prefixLift 262129
  have htrace : WordTrace (prefixWord ++ tailWord_262129) baseStart_262129 baseEnd_262129 := by
    simpa [prefixWord, tailWord_262129, baseEnd_262129] using wordTrace_append hprefix tailTrace_262129
  have hstable : (prefixWord ++ tailWord_262129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262129).length < 2 ^ (prefixWord ++ tailWord_262129).sum := by decide
  have hdescent : baseEnd_262129 < baseStart_262129 := by decide
  rcases family_descends (prefixWord ++ tailWord_262129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262192 : List Nat := [2, 1, 1, 1, 2, 5, 2, 6]
def baseStart_262192 : Nat := 118140960795 + 262192 * 2 ^ 59
def prefixEnd_262192 : Nat := 4983230072969 + 3 ^ 40 * 262192 * 2
def baseEnd_262192 : Nat := 39890524374442490753839

theorem tailTrace_262192 : CollatzResearch.WordTrace tailWord_262192 prefixEnd_262192 39890524374442490753839 := by
  unfold tailWord_262192
  simp only [CollatzResearch.WordTrace]
  refine ⟨4781463933065318836842415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6375285244087091782456553 4781463933065318836842415)
  ·
    refine ⟨7172195899597978255263623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4781463933065318836842415 7172195899597978255263623)
    ·
      refine ⟨10758293849396967382895435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7172195899597978255263623 10758293849396967382895435)
      ·
        refine ⟨16137440774095451074343153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10758293849396967382895435 16137440774095451074343153)
        ·
          refine ⟨12103080580571588305757365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16137440774095451074343153 12103080580571588305757365)
          ·
            refine ⟨1134663804428586403664753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12103080580571588305757365 1134663804428586403664753)
            ·
              refine ⟨850997853321439802748565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1134663804428586403664753 850997853321439802748565)
              ·
                refine ⟨39890524374442490753839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 850997853321439802748565 39890524374442490753839)
                ·
                  rfl

theorem cell20_262192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_262192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262192 prefixEnd_262192 := by exact prefixLift 262192
  have htrace : WordTrace (prefixWord ++ tailWord_262192) baseStart_262192 baseEnd_262192 := by
    simpa [prefixWord, tailWord_262192, baseEnd_262192] using wordTrace_append hprefix tailTrace_262192
  have hstable : (prefixWord ++ tailWord_262192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262192).length < 2 ^ (prefixWord ++ tailWord_262192).sum := by decide
  have hdescent : baseEnd_262192 < baseStart_262192 := by decide
  rcases family_descends (prefixWord ++ tailWord_262192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262199 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 7]
def baseStart_262199 : Nat := 118140960795 + 262199 * 2 ^ 59
def prefixEnd_262199 : Nat := 4983230072969 + 3 ^ 40 * 262199 * 2
def baseEnd_262199 : Nat := 119674768114066559028155

theorem tailTrace_262199 : CollatzResearch.WordTrace tailWord_262199 prefixEnd_262199 119674768114066559028155 := by
  unfold tailWord_262199
  simp only [CollatzResearch.WordTrace]
  refine ⟨9563183177105277869189651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6375455451403518579459767 9563183177105277869189651)
  ·
    refine ⟨14344774765657916803784477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9563183177105277869189651 14344774765657916803784477)
    ·
      refine ⟨5379290537121718801419179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14344774765657916803784477 5379290537121718801419179)
      ·
        refine ⟨8068935805682578202128769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5379290537121718801419179 8068935805682578202128769)
        ·
          refine ⟨6051701854261933651596577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8068935805682578202128769 6051701854261933651596577)
          ·
            refine ⟨4538776390696450238697433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6051701854261933651596577 4538776390696450238697433)
            ·
              refine ⟨3404082293022337679023075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4538776390696450238697433 3404082293022337679023075)
              ·
                refine ⟨5106123439533506518534613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3404082293022337679023075 5106123439533506518534613)
                ·
                  refine ⟨119674768114066559028155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5106123439533506518534613 119674768114066559028155)
                  ·
                    rfl

theorem cell20_262199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_262199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262199 prefixEnd_262199 := by exact prefixLift 262199
  have htrace : WordTrace (prefixWord ++ tailWord_262199) baseStart_262199 baseEnd_262199 := by
    simpa [prefixWord, tailWord_262199, baseEnd_262199] using wordTrace_append hprefix tailTrace_262199
  have hstable : (prefixWord ++ tailWord_262199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262199).length < 2 ^ (prefixWord ++ tailWord_262199).sum := by decide
  have hdescent : baseEnd_262199 < baseStart_262199 := by decide
  rcases family_descends (prefixWord ++ tailWord_262199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262202 : List Nat := [3, 1, 1, 1, 3, 1, 1, 7, 2]
def baseStart_262202 : Nat := 118140960795 + 262202 * 2 ^ 59
def prefixEnd_262202 : Nat := 4983230072969 + 3 ^ 40 * 262202 * 2
def baseEnd_262202 : Nat := 119676137395811881928143

theorem tailTrace_262202 : CollatzResearch.WordTrace tailWord_262202 prefixEnd_262202 119676137395811881928143 := by
  unfold tailWord_262202
  simp only [CollatzResearch.WordTrace]
  refine ⟨2390823149023602345387215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6375528397396272921032573 2390823149023602345387215)
  ·
    refine ⟨3586234723535403518080823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2390823149023602345387215 3586234723535403518080823)
    ·
      refine ⟨5379352085303105277121235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3586234723535403518080823 5379352085303105277121235)
      ·
        refine ⟨8069028127954657915681853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5379352085303105277121235 8069028127954657915681853)
        ·
          refine ⟨3025885547982996718380695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8069028127954657915681853 3025885547982996718380695)
          ·
            refine ⟨4538828321974495077571043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3025885547982996718380695 4538828321974495077571043)
            ·
              refine ⟨6808242482961742616356565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4538828321974495077571043 6808242482961742616356565)
              ·
                refine ⟨159568183194415842570857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6808242482961742616356565 159568183194415842570857)
                ·
                  refine ⟨119676137395811881928143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159568183194415842570857 119676137395811881928143)
                  ·
                    rfl

theorem cell20_262202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_262202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262202 prefixEnd_262202 := by exact prefixLift 262202
  have htrace : WordTrace (prefixWord ++ tailWord_262202) baseStart_262202 baseEnd_262202 := by
    simpa [prefixWord, tailWord_262202, baseEnd_262202] using wordTrace_append hprefix tailTrace_262202
  have hstable : (prefixWord ++ tailWord_262202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262202).length < 2 ^ (prefixWord ++ tailWord_262202).sum := by decide
  have hdescent : baseEnd_262202 < baseStart_262202 := by decide
  rcases family_descends (prefixWord ++ tailWord_262202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262226 : List Nat := [3, 2, 2, 1, 4, 2, 1, 5]
def baseStart_262226 : Nat := 118140960795 + 262226 * 2 ^ 59
def prefixEnd_262226 : Nat := 4983230072969 + 3 ^ 40 * 262226 * 2
def baseEnd_262226 : Nat := 39895697216591488376015

theorem tailTrace_262226 : CollatzResearch.WordTrace tailWord_262226 prefixEnd_262226 39895697216591488376015 := by
  unfold tailWord_262226
  simp only [CollatzResearch.WordTrace]
  refine ⟨2391041987001865370105633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6376111965338307653615021 2391041987001865370105633)
  ·
    refine ⟨1793281490251399027579225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2391041987001865370105633 1793281490251399027579225)
    ·
      refine ⟨1344961117688549270684419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1793281490251399027579225 1344961117688549270684419)
      ·
        refine ⟨2017441676532823906026629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1344961117688549270684419 2017441676532823906026629)
        ·
          refine ⟨378270314349904482379993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2017441676532823906026629 378270314349904482379993)
          ·
            refine ⟨283702735762428361784995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378270314349904482379993 283702735762428361784995)
            ·
              refine ⟨425554103643642542677493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283702735762428361784995 425554103643642542677493)
              ·
                refine ⟨39895697216591488376015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 425554103643642542677493 39895697216591488376015)
                ·
                  rfl

theorem cell20_262226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_262226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262226 prefixEnd_262226 := by exact prefixLift 262226
  have htrace : WordTrace (prefixWord ++ tailWord_262226) baseStart_262226 baseEnd_262226 := by
    simpa [prefixWord, tailWord_262226, baseEnd_262226] using wordTrace_append hprefix tailTrace_262226
  have hstable : (prefixWord ++ tailWord_262226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262226).length < 2 ^ (prefixWord ++ tailWord_262226).sum := by decide
  have hdescent : baseEnd_262226 < baseStart_262226 := by decide
  rcases family_descends (prefixWord ++ tailWord_262226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262247 : List Nat := [1, 1, 5, 1, 1, 2, 5, 4]
def baseStart_262247 : Nat := 118140960795 + 262247 * 2 ^ 59
def prefixEnd_262247 : Nat := 4983230072969 + 3 ^ 40 * 262247 * 2
def baseEnd_262247 : Nat := 39898892207330575142653

theorem tailTrace_262247 : CollatzResearch.WordTrace tailWord_262247 prefixEnd_262247 39898892207330575142653 := by
  unfold tailWord_262247
  simp only [CollatzResearch.WordTrace]
  refine ⟨9564933880931382066936995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6376622587287588044624663 9564933880931382066936995)
  ·
    refine ⟨14347400821397073100405493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9564933880931382066936995 14347400821397073100405493)
    ·
      refine ⟨1345068827005975603163015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14347400821397073100405493 1345068827005975603163015)
      ·
        refine ⟨2017603240508963404744523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1345068827005975603163015 2017603240508963404744523)
        ·
          refine ⟨3026404860763445107116785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2017603240508963404744523 3026404860763445107116785)
          ·
            refine ⟨2269803645572583830337589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3026404860763445107116785 2269803645572583830337589)
            ·
              refine ⟨212794091772429734094149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2269803645572583830337589 212794091772429734094149)
              ·
                refine ⟨39898892207330575142653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212794091772429734094149 39898892207330575142653)
                ·
                  rfl

theorem cell20_262247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 5, 4].length) (baseStart_262247 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262247 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262247 prefixEnd_262247 := by exact prefixLift 262247
  have htrace : WordTrace (prefixWord ++ tailWord_262247) baseStart_262247 baseEnd_262247 := by
    simpa [prefixWord, tailWord_262247, baseEnd_262247] using wordTrace_append hprefix tailTrace_262247
  have hstable : (prefixWord ++ tailWord_262247).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262247).length < 2 ^ (prefixWord ++ tailWord_262247).sum := by decide
  have hdescent : baseEnd_262247 < baseStart_262247 := by decide
  rcases family_descends (prefixWord ++ tailWord_262247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262254 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_262254 : Nat := 118140960795 + 262254 * 2 ^ 59
def prefixEnd_262254 : Nat := 4983230072969 + 3 ^ 40 * 262254 * 2
def baseEnd_262254 : Nat := 119699871612730812194597

theorem tailTrace_262254 : CollatzResearch.WordTrace tailWord_262254 prefixEnd_262254 119699871612730812194597 := by
  unfold tailWord_262254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1195648648988252782805227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6376792794604014841627877 1195648648988252782805227)
  ·
    refine ⟨1793472973482379174207841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1195648648988252782805227 1793472973482379174207841)
    ·
      refine ⟨1345104730111784380655881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1793472973482379174207841 1345104730111784380655881)
      ·
        refine ⟨1008828547583838285491911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1345104730111784380655881 1008828547583838285491911)
        ·
          refine ⟨1513242821375757428237867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008828547583838285491911 1513242821375757428237867)
          ·
            refine ⟨2269864232063636142356801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513242821375757428237867 2269864232063636142356801)
            ·
              refine ⟨1702398174047727106767601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2269864232063636142356801 1702398174047727106767601)
              ·
                refine ⟨1276798630535795330075701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1702398174047727106767601 1276798630535795330075701)
                ·
                  refine ⟨119699871612730812194597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1276798630535795330075701 119699871612730812194597)
                  ·
                    rfl

theorem cell20_262254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_262254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262254 prefixEnd_262254 := by exact prefixLift 262254
  have htrace : WordTrace (prefixWord ++ tailWord_262254) baseStart_262254 baseEnd_262254 := by
    simpa [prefixWord, tailWord_262254, baseEnd_262254] using wordTrace_append hprefix tailTrace_262254
  have hstable : (prefixWord ++ tailWord_262254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262254).length < 2 ^ (prefixWord ++ tailWord_262254).sum := by decide
  have hdescent : baseEnd_262254 < baseStart_262254 := by decide
  rcases family_descends (prefixWord ++ tailWord_262254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262268 : List Nat := [2, 2, 2, 1, 1, 5, 7]
def baseStart_262268 : Nat := 118140960795 + 262268 * 2 ^ 59
def prefixEnd_262268 : Nat := 4983230072969 + 3 ^ 40 * 262268 * 2
def baseEnd_262268 : Nat := 13300695732689887303097

theorem tailTrace_262268 : CollatzResearch.WordTrace tailWord_262268 prefixEnd_262268 13300695732689887303097 := by
  unfold tailWord_262268
  simp only [CollatzResearch.WordTrace]
  refine ⟨4782849906927651326725729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6377133209236868435634305 4782849906927651326725729)
  ·
    refine ⟨3587137430195738495044297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4782849906927651326725729 3587137430195738495044297)
    ·
      refine ⟨2690353072646803871283223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3587137430195738495044297 2690353072646803871283223)
      ·
        refine ⟨4035529608970205806924835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2690353072646803871283223 4035529608970205806924835)
        ·
          refine ⟨6053294413455308710387253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4035529608970205806924835 6053294413455308710387253)
          ·
            refine ⟨567496351261435191598805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6053294413455308710387253 567496351261435191598805)
            ·
              refine ⟨13300695732689887303097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 567496351261435191598805 13300695732689887303097)
              ·
                rfl

theorem cell20_262268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 7].length) (baseStart_262268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262268 prefixEnd_262268 := by exact prefixLift 262268
  have htrace : WordTrace (prefixWord ++ tailWord_262268) baseStart_262268 baseEnd_262268 := by
    simpa [prefixWord, tailWord_262268, baseEnd_262268] using wordTrace_append hprefix tailTrace_262268
  have hstable : (prefixWord ++ tailWord_262268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262268).length < 2 ^ (prefixWord ++ tailWord_262268).sum := by decide
  have hdescent : baseEnd_262268 < baseStart_262268 := by decide
  rcases family_descends (prefixWord ++ tailWord_262268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262294 : List Nat := [5, 3, 2, 1, 1, 2, 2, 4]
def baseStart_262294 : Nat := 118140960795 + 262294 * 2 ^ 59
def prefixEnd_262294 : Nat := 4983230072969 + 3 ^ 40 * 262294 * 2
def baseEnd_262294 : Nat := 39906042900889483620367

theorem tailTrace_262294 : CollatzResearch.WordTrace tailWord_262294 prefixEnd_262294 39906042900889483620367 := by
  unfold tailWord_262294
  simp only [CollatzResearch.WordTrace]
  refine ⟨597915506985069318368621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6377765407840739395931957 597915506985069318368621)
  ·
    refine ⟨224218315119400994388233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 597915506985069318368621 224218315119400994388233)
    ·
      refine ⟨168163736339550745791175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 224218315119400994388233 168163736339550745791175)
      ·
        refine ⟨252245604509326118686763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168163736339550745791175 252245604509326118686763)
        ·
          refine ⟨378368406763989178030145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252245604509326118686763 378368406763989178030145)
          ·
            refine ⟨283776305072991883522609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378368406763989178030145 283776305072991883522609)
            ·
              refine ⟨212832228804743912641957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283776305072991883522609 212832228804743912641957)
              ·
                refine ⟨39906042900889483620367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 212832228804743912641957 39906042900889483620367)
                ·
                  rfl

theorem cell20_262294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_262294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262294 prefixEnd_262294 := by exact prefixLift 262294
  have htrace : WordTrace (prefixWord ++ tailWord_262294) baseStart_262294 baseEnd_262294 := by
    simpa [prefixWord, tailWord_262294, baseEnd_262294] using wordTrace_append hprefix tailTrace_262294
  have hstable : (prefixWord ++ tailWord_262294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262294).length < 2 ^ (prefixWord ++ tailWord_262294).sum := by decide
  have hdescent : baseEnd_262294 < baseStart_262294 := by decide
  rcases family_descends (prefixWord ++ tailWord_262294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262302 : List Nat := [4, 3, 1, 1, 3, 1, 1, 6]
def baseStart_262302 : Nat := 118140960795 + 262302 * 2 ^ 59
def prefixEnd_262302 : Nat := 4983230072969 + 3 ^ 40 * 262302 * 2
def baseEnd_262302 : Nat := 39907260040218659531467

theorem tailTrace_262302 : CollatzResearch.WordTrace tailWord_262302 prefixEnd_262302 39907260040218659531467 := by
  unfold tailWord_262302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1195867486966515807523645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6377959930488084306792773 1195867486966515807523645)
  ·
    refine ⟨448450307612443427821367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1195867486966515807523645 448450307612443427821367)
    ·
      refine ⟨672675461418665141732051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 448450307612443427821367 672675461418665141732051)
      ·
        refine ⟨1009013192127997712598077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672675461418665141732051 1009013192127997712598077)
        ·
          refine ⟨378379947047999142224279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1009013192127997712598077 378379947047999142224279)
          ·
            refine ⟨567569920571998713336419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378379947047999142224279 567569920571998713336419)
            ·
              refine ⟨851354880857998070004629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 567569920571998713336419 851354880857998070004629)
              ·
                refine ⟨39907260040218659531467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 851354880857998070004629 39907260040218659531467)
                ·
                  rfl

theorem cell20_262302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_262302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262302 prefixEnd_262302 := by exact prefixLift 262302
  have htrace : WordTrace (prefixWord ++ tailWord_262302) baseStart_262302 baseEnd_262302 := by
    simpa [prefixWord, tailWord_262302, baseEnd_262302] using wordTrace_append hprefix tailTrace_262302
  have hstable : (prefixWord ++ tailWord_262302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262302).length < 2 ^ (prefixWord ++ tailWord_262302).sum := by decide
  have hdescent : baseEnd_262302 < baseStart_262302 := by decide
  rcases family_descends (prefixWord ++ tailWord_262302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262440 : List Nat := [2, 1, 5, 1, 3, 2, 1, 2, 3]
def baseStart_262440 : Nat := 118140960795 + 262440 * 2 ^ 59
def prefixEnd_262440 : Nat := 4983230072969 + 3 ^ 40 * 262440 * 2
def baseEnd_262440 : Nat := 119784767080940831993837

theorem tailTrace_262440 : CollatzResearch.WordTrace tailWord_262440 prefixEnd_262440 119784767080940831993837 := by
  unfold tailWord_262440
  simp only [CollatzResearch.WordTrace]
  refine ⟨4785986584616088014356387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6381315446154784019141849 4785986584616088014356387)
  ·
    refine ⟨7178979876924132021534581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4785986584616088014356387 7178979876924132021534581)
    ·
      refine ⟨673029363461637377018867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7178979876924132021534581 673029363461637377018867)
      ·
        refine ⟨1009544045192456065528301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 673029363461637377018867 1009544045192456065528301)
        ·
          refine ⟨378579016947171024573113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1009544045192456065528301 378579016947171024573113)
          ·
            refine ⟨283934262710378268429835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378579016947171024573113 283934262710378268429835)
            ·
              refine ⟨425901394065567402644753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 283934262710378268429835 425901394065567402644753)
              ·
                refine ⟨319426045549175551983565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 425901394065567402644753 319426045549175551983565)
                ·
                  refine ⟨119784767080940831993837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319426045549175551983565 119784767080940831993837)
                  ·
                    rfl

theorem cell20_262440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 3].length) (baseStart_262440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262440 prefixEnd_262440 := by exact prefixLift 262440
  have htrace : WordTrace (prefixWord ++ tailWord_262440) baseStart_262440 baseEnd_262440 := by
    simpa [prefixWord, tailWord_262440, baseEnd_262440] using wordTrace_append hprefix tailTrace_262440
  have hstable : (prefixWord ++ tailWord_262440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262440).length < 2 ^ (prefixWord ++ tailWord_262440).sum := by decide
  have hdescent : baseEnd_262440 < baseStart_262440 := by decide
  rcases family_descends (prefixWord ++ tailWord_262440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262444 : List Nat := [2, 2, 1, 1, 1, 3, 5, 2, 3]
def baseStart_262444 : Nat := 118140960795 + 262444 * 2 ^ 59
def prefixEnd_262444 : Nat := 4983230072969 + 3 ^ 40 * 262444 * 2
def baseEnd_262444 : Nat := 119786592789934595860487

theorem tailTrace_262444 : CollatzResearch.WordTrace tailWord_262444 prefixEnd_262444 119786592789934595860487 := by
  unfold tailWord_262444
  simp only [CollatzResearch.WordTrace]
  refine ⟨4786059530608842355929193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6381412707478456474572257 4786059530608842355929193)
  ·
    refine ⟨3589544647956631766946895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4786059530608842355929193 3589544647956631766946895)
    ·
      refine ⟨5384316971934947650420343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3589544647956631766946895 5384316971934947650420343)
      ·
        refine ⟨8076475457902421475630515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5384316971934947650420343 8076475457902421475630515)
        ·
          refine ⟨12114713186853632213445773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8076475457902421475630515 12114713186853632213445773)
          ·
            refine ⟨4543017445070112080042165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12114713186853632213445773 4543017445070112080042165)
            ·
              refine ⟨425907885475323007503953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4543017445070112080042165 425907885475323007503953)
              ·
                refine ⟨319430914106492255627965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 425907885475323007503953 319430914106492255627965)
                ·
                  refine ⟨119786592789934595860487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319430914106492255627965 119786592789934595860487)
                  ·
                    rfl

theorem cell20_262444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_262444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262444 prefixEnd_262444 := by exact prefixLift 262444
  have htrace : WordTrace (prefixWord ++ tailWord_262444) baseStart_262444 baseEnd_262444 := by
    simpa [prefixWord, tailWord_262444, baseEnd_262444] using wordTrace_append hprefix tailTrace_262444
  have hstable : (prefixWord ++ tailWord_262444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262444).length < 2 ^ (prefixWord ++ tailWord_262444).sum := by decide
  have hdescent : baseEnd_262444 < baseStart_262444 := by decide
  rcases family_descends (prefixWord ++ tailWord_262444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262451 : List Nat := [1, 1, 1, 2, 5, 1, 4, 1, 4]
def baseStart_262451 : Nat := 118140960795 + 262451 * 2 ^ 59
def prefixEnd_262451 : Nat := 4983230072969 + 3 ^ 40 * 262451 * 2
def baseEnd_262451 : Nat := 119789787780673682627125

theorem tailTrace_262451 : CollatzResearch.WordTrace tailWord_262451 prefixEnd_262451 119789787780673682627125 := by
  unfold tailWord_262451
  simp only [CollatzResearch.WordTrace]
  refine ⟨9572374372192324907363207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6381582914794883271575471 9572374372192324907363207)
  ·
    refine ⟨14358561558288487361044811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9572374372192324907363207 14358561558288487361044811)
    ·
      refine ⟨21537842337432731041567217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14358561558288487361044811 21537842337432731041567217)
      ·
        refine ⟨16153381753074548281175413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21537842337432731041567217 16153381753074548281175413)
        ·
          refine ⟨1514379539350738901360195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16153381753074548281175413 1514379539350738901360195)
          ·
            refine ⟨2271569309026108352040293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1514379539350738901360195 2271569309026108352040293)
            ·
              refine ⟨425919245442395316007555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2271569309026108352040293 425919245442395316007555)
              ·
                refine ⟨638878868163592974011333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 425919245442395316007555 638878868163592974011333)
                ·
                  refine ⟨119789787780673682627125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 638878868163592974011333 119789787780673682627125)
                  ·
                    rfl

theorem cell20_262451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 4].length) (baseStart_262451 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262451 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262451 prefixEnd_262451 := by exact prefixLift 262451
  have htrace : WordTrace (prefixWord ++ tailWord_262451) baseStart_262451 baseEnd_262451 := by
    simpa [prefixWord, tailWord_262451, baseEnd_262451] using wordTrace_append hprefix tailTrace_262451
  have hstable : (prefixWord ++ tailWord_262451).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262451).length < 2 ^ (prefixWord ++ tailWord_262451).sum := by decide
  have hdescent : baseEnd_262451 < baseStart_262451 := by decide
  rcases family_descends (prefixWord ++ tailWord_262451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262492 : List Nat := [2, 2, 4, 3, 1, 2, 6]
def baseStart_262492 : Nat := 118140960795 + 262492 * 2 ^ 59
def prefixEnd_262492 : Nat := 4983230072969 + 3 ^ 40 * 262492 * 2
def baseEnd_262492 : Nat := 13312055699762195806699

theorem tailTrace_262492 : CollatzResearch.WordTrace tailWord_262492 prefixEnd_262492 13312055699762195806699 := by
  unfold tailWord_262492
  simp only [CollatzResearch.WordTrace]
  refine ⟨4786934882521894454802865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6382579843362525939737153 4786934882521894454802865)
  ·
    refine ⟨3590201161891420841102149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4786934882521894454802865 3590201161891420841102149)
    ·
      refine ⟨673162717854641407706653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3590201161891420841102149 673162717854641407706653)
      ·
        refine ⟨252436019195490527889995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 673162717854641407706653 252436019195490527889995)
        ·
          refine ⟨378654028793235791834993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252436019195490527889995 378654028793235791834993)
          ·
            refine ⟨283990521594926843876245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 378654028793235791834993 283990521594926843876245)
            ·
              refine ⟨13312055699762195806699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 283990521594926843876245 13312055699762195806699)
              ·
                rfl

theorem cell20_262492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 2, 6].length) (baseStart_262492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262492 prefixEnd_262492 := by exact prefixLift 262492
  have htrace : WordTrace (prefixWord ++ tailWord_262492) baseStart_262492 baseEnd_262492 := by
    simpa [prefixWord, tailWord_262492, baseEnd_262492] using wordTrace_append hprefix tailTrace_262492
  have hstable : (prefixWord ++ tailWord_262492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262492).length < 2 ^ (prefixWord ++ tailWord_262492).sum := by decide
  have hdescent : baseEnd_262492 < baseStart_262492 := by decide
  rcases family_descends (prefixWord ++ tailWord_262492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262506 : List Nat := [3, 1, 3, 3, 1, 1, 3, 1, 4]
def baseStart_262506 : Nat := 118140960795 + 262506 * 2 ^ 59
def prefixEnd_262506 : Nat := 4983230072969 + 3 ^ 40 * 262506 * 2
def baseEnd_262506 : Nat := 119814891279337935793567

theorem tailTrace_262506 : CollatzResearch.WordTrace tailWord_262506 prefixEnd_262506 119814891279337935793567 := by
  unfold tailWord_262506
  simp only [CollatzResearch.WordTrace]
  refine ⟨2393595096748267325153843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6382920257995379533743581 2393595096748267325153843)
  ·
    refine ⟨3590392645122400987730765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2393595096748267325153843 3590392645122400987730765)
    ·
      refine ⟨1346397241920900370399037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3590392645122400987730765 1346397241920900370399037)
      ·
        refine ⟨504898965720337638899639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1346397241920900370399037 504898965720337638899639)
        ·
          refine ⟨757348448580506458349459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 504898965720337638899639 757348448580506458349459)
          ·
            refine ⟨1136022672870759687524189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757348448580506458349459 1136022672870759687524189)
            ·
              refine ⟨426008502326534882821571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1136022672870759687524189 426008502326534882821571)
              ·
                refine ⟨639012753489802324232357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426008502326534882821571 639012753489802324232357)
                ·
                  refine ⟨119814891279337935793567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 639012753489802324232357 119814891279337935793567)
                  ·
                    rfl

theorem cell20_262506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_262506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262506 prefixEnd_262506 := by exact prefixLift 262506
  have htrace : WordTrace (prefixWord ++ tailWord_262506) baseStart_262506 baseEnd_262506 := by
    simpa [prefixWord, tailWord_262506, baseEnd_262506] using wordTrace_append hprefix tailTrace_262506
  have hstable : (prefixWord ++ tailWord_262506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262506).length < 2 ^ (prefixWord ++ tailWord_262506).sum := by decide
  have hdescent : baseEnd_262506 < baseStart_262506 := by decide
  rcases family_descends (prefixWord ++ tailWord_262506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262550 : List Nat := [5, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_262550 : Nat := 118140960795 + 262550 * 2 ^ 59
def prefixEnd_262550 : Nat := 4983230072969 + 3 ^ 40 * 262550 * 2
def baseEnd_262550 : Nat := 119834974078269338326721

theorem tailTrace_262550 : CollatzResearch.WordTrace tailWord_262550 prefixEnd_262550 119834974078269338326721 := by
  unfold tailWord_262550
  simp only [CollatzResearch.WordTrace]
  refine ⟨598499074927104050951069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6383990132555776543478069 598499074927104050951069)
  ·
    refine ⟨224437153097664019106651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 598499074927104050951069 224437153097664019106651)
    ·
      refine ⟨336655729646496028659977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 224437153097664019106651 336655729646496028659977)
      ·
        refine ⟨252491797234872021494983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 336655729646496028659977 252491797234872021494983)
        ·
          refine ⟨378737695852308032242475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252491797234872021494983 378737695852308032242475)
          ·
            refine ⟨568106543778462048363713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 378737695852308032242475 568106543778462048363713)
            ·
              refine ⟨426079907833846536272785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 568106543778462048363713 426079907833846536272785)
              ·
                refine ⟨319559930875384902204589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426079907833846536272785 319559930875384902204589)
                ·
                  refine ⟨119834974078269338326721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319559930875384902204589 119834974078269338326721)
                  ·
                    rfl

theorem cell20_262550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_262550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262550 prefixEnd_262550 := by exact prefixLift 262550
  have htrace : WordTrace (prefixWord ++ tailWord_262550) baseStart_262550 baseEnd_262550 := by
    simpa [prefixWord, tailWord_262550, baseEnd_262550] using wordTrace_append hprefix tailTrace_262550
  have hstable : (prefixWord ++ tailWord_262550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262550).length < 2 ^ (prefixWord ++ tailWord_262550).sum := by decide
  have hdescent : baseEnd_262550 < baseStart_262550 := by decide
  rcases family_descends (prefixWord ++ tailWord_262550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262557 : List Nat := [1, 4, 2, 1, 5, 1, 2, 2, 2]
def baseStart_262557 : Nat := 118140960795 + 262557 * 2 ^ 59
def prefixEnd_262557 : Nat := 4983230072969 + 3 ^ 40 * 262557 * 2
def baseEnd_262557 : Nat := 119838169069008425093359

theorem tailTrace_262557 : CollatzResearch.WordTrace tailWord_262557 prefixEnd_262557 119838169069008425093359 := by
  unfold tailWord_262557
  simp only [CollatzResearch.WordTrace]
  refine ⟨9576240509808305010721925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6384160339872203340481283 9576240509808305010721925)
  ·
    refine ⟨1795545095589057189510361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9576240509808305010721925 1795545095589057189510361)
    ·
      refine ⟨1346658821691792892132771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1795545095589057189510361 1346658821691792892132771)
      ·
        refine ⟨2019988232537689338199157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1346658821691792892132771 2019988232537689338199157)
        ·
          refine ⟨189373896800408375456171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2019988232537689338199157 189373896800408375456171)
          ·
            refine ⟨284060845200612563184257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189373896800408375456171 284060845200612563184257)
            ·
              refine ⟨213045633900459422388193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284060845200612563184257 213045633900459422388193)
              ·
                refine ⟨159784225425344566791145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213045633900459422388193 159784225425344566791145)
                ·
                  refine ⟨119838169069008425093359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159784225425344566791145 119838169069008425093359)
                  ·
                    rfl

theorem cell20_262557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_262557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262557 prefixEnd_262557 := by exact prefixLift 262557
  have htrace : WordTrace (prefixWord ++ tailWord_262557) baseStart_262557 baseEnd_262557 := by
    simpa [prefixWord, tailWord_262557, baseEnd_262557] using wordTrace_append hprefix tailTrace_262557
  have hstable : (prefixWord ++ tailWord_262557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262557).length < 2 ^ (prefixWord ++ tailWord_262557).sum := by decide
  have hdescent : baseEnd_262557 < baseStart_262557 := by decide
  rcases family_descends (prefixWord ++ tailWord_262557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262568 : List Nat := [2, 1, 6, 1, 1, 3, 1, 5]
def baseStart_262568 : Nat := 118140960795 + 262568 * 2 ^ 59
def prefixEnd_262568 : Nat := 4983230072969 + 3 ^ 40 * 262568 * 2
def baseEnd_262568 : Nat := 39947729922913758575549

theorem tailTrace_262568 : CollatzResearch.WordTrace tailWord_262568 prefixEnd_262568 39947729922913758575549 := by
  unfold tailWord_262568
  simp only [CollatzResearch.WordTrace]
  refine ⟨4788320856384226944686179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6384427808512302592914905 4788320856384226944686179)
  ·
    refine ⟨7182481284576340417029269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4788320856384226944686179 7182481284576340417029269)
    ·
      refine ⟨336678810214515957048247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7182481284576340417029269 336678810214515957048247)
      ·
        refine ⟨505018215321773935572371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 336678810214515957048247 505018215321773935572371)
        ·
          refine ⟨757527322982660903358557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 505018215321773935572371 757527322982660903358557)
          ·
            refine ⟨284072746118497838759459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 757527322982660903358557 284072746118497838759459)
            ·
              refine ⟨426109119177746758139189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284072746118497838759459 426109119177746758139189)
              ·
                refine ⟨39947729922913758575549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 426109119177746758139189 39947729922913758575549)
                ·
                  rfl

theorem cell20_262568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 1, 5].length) (baseStart_262568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262568 prefixEnd_262568 := by exact prefixLift 262568
  have htrace : WordTrace (prefixWord ++ tailWord_262568) baseStart_262568 baseEnd_262568 := by
    simpa [prefixWord, tailWord_262568, baseEnd_262568] using wordTrace_append hprefix tailTrace_262568
  have hstable : (prefixWord ++ tailWord_262568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262568).length < 2 ^ (prefixWord ++ tailWord_262568).sum := by decide
  have hdescent : baseEnd_262568 < baseStart_262568 := by decide
  rcases family_descends (prefixWord ++ tailWord_262568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262589 : List Nat := [1, 4, 1, 2, 2, 3, 3, 4]
def baseStart_262589 : Nat := 118140960795 + 262589 * 2 ^ 59
def prefixEnd_262589 : Nat := 4983230072969 + 3 ^ 40 * 262589 * 2
def baseEnd_262589 : Nat := 39950924913652845342187

theorem tailTrace_262589 : CollatzResearch.WordTrace tailWord_262589 prefixEnd_262589 39950924913652845342187 := by
  unfold tailWord_262589
  simp only [CollatzResearch.WordTrace]
  refine ⟨9577407645692374475886821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6384938430461582983924547 9577407645692374475886821)
  ·
    refine ⟨1795763933567320214228779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9577407645692374475886821 1795763933567320214228779)
    ·
      refine ⟨2693645900350980321343169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1795763933567320214228779 2693645900350980321343169)
      ·
        refine ⟨2020234425263235241007377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2693645900350980321343169 2020234425263235241007377)
        ·
          refine ⟨1515175818947426430755533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2020234425263235241007377 1515175818947426430755533)
          ·
            refine ⟨568190932105284911533325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1515175818947426430755533 568190932105284911533325)
            ·
              refine ⟨213071599539481841824997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 568190932105284911533325 213071599539481841824997)
              ·
                refine ⟨39950924913652845342187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213071599539481841824997 39950924913652845342187)
                ·
                  rfl

theorem cell20_262589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 4].length) (baseStart_262589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262589 prefixEnd_262589 := by exact prefixLift 262589
  have htrace : WordTrace (prefixWord ++ tailWord_262589) baseStart_262589 baseEnd_262589 := by
    simpa [prefixWord, tailWord_262589, baseEnd_262589] using wordTrace_append hprefix tailTrace_262589
  have hstable : (prefixWord ++ tailWord_262589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262589).length < 2 ^ (prefixWord ++ tailWord_262589).sum := by decide
  have hdescent : baseEnd_262589 < baseStart_262589 := by decide
  rcases family_descends (prefixWord ++ tailWord_262589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262613 : List Nat := [1, 3, 2, 3, 1, 4, 1, 2, 3]
def baseStart_262613 : Nat := 118140960795 + 262613 * 2 ^ 59
def prefixEnd_262613 : Nat := 4983230072969 + 3 ^ 40 * 262613 * 2
def baseEnd_262613 : Nat := 119863728994921119226463

theorem tailTrace_262613 : CollatzResearch.WordTrace tailWord_262613 prefixEnd_262613 119863728994921119226463 := by
  unfold tailWord_262613
  simp only [CollatzResearch.WordTrace]
  refine ⟨9578282997605426574760493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6385521998403617716506995 9578282997605426574760493)
  ·
    refine ⟨3591856124102034965535185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9578282997605426574760493 3591856124102034965535185)
    ·
      refine ⟨2693892093076526224151389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3591856124102034965535185 2693892093076526224151389)
      ·
        refine ⟨1010209534903697334056771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2693892093076526224151389 1010209534903697334056771)
        ·
          refine ⟨1515314302355546001085157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010209534903697334056771 1515314302355546001085157)
          ·
            refine ⟨284121431691664875203467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1515314302355546001085157 284121431691664875203467)
            ·
              refine ⟨426182147537497312805201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284121431691664875203467 426182147537497312805201)
              ·
                refine ⟨319636610653122984603901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426182147537497312805201 319636610653122984603901)
                ·
                  refine ⟨119863728994921119226463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319636610653122984603901 119863728994921119226463)
                  ·
                    rfl

theorem cell20_262613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_262613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262613 prefixEnd_262613 := by exact prefixLift 262613
  have htrace : WordTrace (prefixWord ++ tailWord_262613) baseStart_262613 baseEnd_262613 := by
    simpa [prefixWord, tailWord_262613, baseEnd_262613] using wordTrace_append hprefix tailTrace_262613
  have hstable : (prefixWord ++ tailWord_262613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262613).length < 2 ^ (prefixWord ++ tailWord_262613).sum := by decide
  have hdescent : baseEnd_262613 < baseStart_262613 := by decide
  rcases family_descends (prefixWord ++ tailWord_262613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262617 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 5]
def baseStart_262617 : Nat := 118140960795 + 262617 * 2 ^ 59
def prefixEnd_262617 : Nat := 4983230072969 + 3 ^ 40 * 262617 * 2
def baseEnd_262617 : Nat := 119865554703914883093113

theorem tailTrace_262617 : CollatzResearch.WordTrace tailWord_262617 prefixEnd_262617 119865554703914883093113 := by
  unfold tailWord_262617
  simp only [CollatzResearch.WordTrace]
  refine ⟨9578428889590935257906105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6385619259727290171937403 9578428889590935257906105)
  ·
    refine ⟨7183821667193201443429579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9578428889590935257906105 7183821667193201443429579)
    ·
      refine ⟨10775732500789802165144369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7183821667193201443429579 10775732500789802165144369)
      ·
        refine ⟨8081799375592351623858277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10775732500789802165144369 8081799375592351623858277)
        ·
          refine ⟨1515337382923565929473427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8081799375592351623858277 1515337382923565929473427)
          ·
            refine ⟨2273006074385348894210141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515337382923565929473427 2273006074385348894210141)
            ·
              refine ⟨852377277894505835328803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2273006074385348894210141 852377277894505835328803)
              ·
                refine ⟨1278565916841758752993205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 852377277894505835328803 1278565916841758752993205)
                ·
                  refine ⟨119865554703914883093113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1278565916841758752993205 119865554703914883093113)
                  ·
                    rfl

theorem cell20_262617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_262617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262617 prefixEnd_262617 := by exact prefixLift 262617
  have htrace : WordTrace (prefixWord ++ tailWord_262617) baseStart_262617 baseEnd_262617 := by
    simpa [prefixWord, tailWord_262617, baseEnd_262617] using wordTrace_append hprefix tailTrace_262617
  have hstable : (prefixWord ++ tailWord_262617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262617).length < 2 ^ (prefixWord ++ tailWord_262617).sum := by decide
  have hdescent : baseEnd_262617 < baseStart_262617 := by decide
  rcases family_descends (prefixWord ++ tailWord_262617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262700 : List Nat := [2, 2, 1, 1, 1, 2, 1, 6, 4]
def baseStart_262700 : Nat := 118140960795 + 262700 * 2 ^ 59
def prefixEnd_262700 : Nat := 4983230072969 + 3 ^ 40 * 262700 * 2
def baseEnd_262700 : Nat := 119903438165535483326107

theorem tailTrace_262700 : CollatzResearch.WordTrace tailWord_262700 prefixEnd_262700 119903438165535483326107 := by
  unfold tailWord_262700
  simp only [CollatzResearch.WordTrace]
  refine ⟨4790728074145120216588777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6387637432193493622118369 4790728074145120216588777)
  ·
    refine ⟨3593046055608840162441583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4790728074145120216588777 3593046055608840162441583)
    ·
      refine ⟨5389569083413260243662375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3593046055608840162441583 5389569083413260243662375)
      ·
        refine ⟨8084353625119890365493563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5389569083413260243662375 8084353625119890365493563)
        ·
          refine ⟨12126530437679835548240345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8084353625119890365493563 12126530437679835548240345)
          ·
            refine ⟨9094897828259876661180259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12126530437679835548240345 9094897828259876661180259)
            ·
              refine ⟨13642346742389814991770389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9094897828259876661180259 13642346742389814991770389)
              ·
                refine ⟨639485003549522577739237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13642346742389814991770389 639485003549522577739237)
                ·
                  refine ⟨119903438165535483326107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 639485003549522577739237 119903438165535483326107)
                  ·
                    rfl

theorem cell20_262700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_262700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262700 prefixEnd_262700 := by exact prefixLift 262700
  have htrace : WordTrace (prefixWord ++ tailWord_262700) baseStart_262700 baseEnd_262700 := by
    simpa [prefixWord, tailWord_262700, baseEnd_262700] using wordTrace_append hprefix tailTrace_262700
  have hstable : (prefixWord ++ tailWord_262700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262700).length < 2 ^ (prefixWord ++ tailWord_262700).sum := by decide
  have hdescent : baseEnd_262700 < baseStart_262700 := by decide
  rcases family_descends (prefixWord ++ tailWord_262700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262707 : List Nat := [1, 1, 1, 2, 4, 2, 1, 8]
def baseStart_262707 : Nat := 118140960795 + 262707 * 2 ^ 59
def prefixEnd_262707 : Nat := 4983230072969 + 3 ^ 40 * 262707 * 2
def baseEnd_262707 : Nat := 39968877718758190030915

theorem tailTrace_262707 : CollatzResearch.WordTrace tailWord_262707 prefixEnd_262707 39968877718758190030915 := by
  unfold tailWord_262707
  simp only [CollatzResearch.WordTrace]
  refine ⟨9581711459264880628682375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6387807639509920419121583 9581711459264880628682375)
  ·
    refine ⟨14372567188897320943023563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9581711459264880628682375 14372567188897320943023563)
    ·
      refine ⟨21558850783345981414535345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14372567188897320943023563 21558850783345981414535345)
      ·
        refine ⟨16169138087509486060901509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21558850783345981414535345 16169138087509486060901509)
        ·
          refine ⟨3031713391408028636419033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16169138087509486060901509 3031713391408028636419033)
          ·
            refine ⟨2273785043556021477314275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3031713391408028636419033 2273785043556021477314275)
            ·
              refine ⟨3410677565334032215971413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2273785043556021477314275 3410677565334032215971413)
              ·
                refine ⟨39968877718758190030915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3410677565334032215971413 39968877718758190030915)
                ·
                  rfl

theorem cell20_262707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 8].length) (baseStart_262707 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262707 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262707 prefixEnd_262707 := by exact prefixLift 262707
  have htrace : WordTrace (prefixWord ++ tailWord_262707) baseStart_262707 baseEnd_262707 := by
    simpa [prefixWord, tailWord_262707, baseEnd_262707] using wordTrace_append hprefix tailTrace_262707
  have hstable : (prefixWord ++ tailWord_262707).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262707).length < 2 ^ (prefixWord ++ tailWord_262707).sum := by decide
  have hdescent : baseEnd_262707 < baseStart_262707 := by decide
  rcases family_descends (prefixWord ++ tailWord_262707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262731 : List Nat := [1, 1, 1, 1, 3, 1, 5, 4, 3]
def baseStart_262731 : Nat := 118140960795 + 262731 * 2 ^ 59
def prefixEnd_262731 : Nat := 4983230072969 + 3 ^ 40 * 262731 * 2
def baseEnd_262731 : Nat := 119917587410237153292647

theorem tailTrace_262731 : CollatzResearch.WordTrace tailWord_262731 prefixEnd_262731 119917587410237153292647 := by
  unfold tailWord_262731
  simp only [CollatzResearch.WordTrace]
  refine ⟨9582586811177932727556047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6388391207451955151704031 9582586811177932727556047)
  ·
    refine ⟨14373880216766899091334071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9582586811177932727556047 14373880216766899091334071)
    ·
      refine ⟨21560820325150348637001107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14373880216766899091334071 21560820325150348637001107)
      ·
        refine ⟨32341230487725522955501661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21560820325150348637001107 32341230487725522955501661)
        ·
          refine ⟨12127961432897071108313123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32341230487725522955501661 12127961432897071108313123)
          ·
            refine ⟨18191942149345606662469685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12127961432897071108313123 18191942149345606662469685)
            ·
              refine ⟨1705494576501150624606533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18191942149345606662469685 1705494576501150624606533)
              ·
                refine ⟨319780233093965742113725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1705494576501150624606533 319780233093965742113725)
                ·
                  refine ⟨119917587410237153292647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319780233093965742113725 119917587410237153292647)
                  ·
                    rfl

theorem cell20_262731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 3].length) (baseStart_262731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262731 prefixEnd_262731 := by exact prefixLift 262731
  have htrace : WordTrace (prefixWord ++ tailWord_262731) baseStart_262731 baseEnd_262731 := by
    simpa [prefixWord, tailWord_262731, baseEnd_262731] using wordTrace_append hprefix tailTrace_262731
  have hstable : (prefixWord ++ tailWord_262731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262731).length < 2 ^ (prefixWord ++ tailWord_262731).sum := by decide
  have hdescent : baseEnd_262731 < baseStart_262731 := by decide
  rcases family_descends (prefixWord ++ tailWord_262731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262823 : List Nat := [1, 1, 6, 3, 2, 1, 1, 3, 2]
def baseStart_262823 : Nat := 118140960795 + 262823 * 2 ^ 59
def prefixEnd_262823 : Nat := 4983230072969 + 3 ^ 40 * 262823 * 2
def baseEnd_262823 : Nat := 119959578717093722225605

theorem tailTrace_262823 : CollatzResearch.WordTrace tailWord_262823 prefixEnd_262823 119959578717093722225605 := by
  unfold tailWord_262823
  simp only [CollatzResearch.WordTrace]
  refine ⟨9585942326844632439905123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6390628217896421626603415 9585942326844632439905123)
  ·
    refine ⟨14378913490266948659857685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9585942326844632439905123 14378913490266948659857685)
    ·
      refine ⟨674011569856263218430829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14378913490266948659857685 674011569856263218430829)
      ·
        refine ⟨252754338696098706911561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 674011569856263218430829 252754338696098706911561)
        ·
          refine ⟨189565754022074030183671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252754338696098706911561 189565754022074030183671)
          ·
            refine ⟨284348631033111045275507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189565754022074030183671 284348631033111045275507)
            ·
              refine ⟨426522946549666567913261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284348631033111045275507 426522946549666567913261)
              ·
                refine ⟨159946104956124962967473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 426522946549666567913261 159946104956124962967473)
                ·
                  refine ⟨119959578717093722225605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 159946104956124962967473 119959578717093722225605)
                  ·
                    rfl

theorem cell20_262823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 2].length) (baseStart_262823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262823 prefixEnd_262823 := by exact prefixLift 262823
  have htrace : WordTrace (prefixWord ++ tailWord_262823) baseStart_262823 baseEnd_262823 := by
    simpa [prefixWord, tailWord_262823, baseEnd_262823] using wordTrace_append hprefix tailTrace_262823
  have hstable : (prefixWord ++ tailWord_262823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262823).length < 2 ^ (prefixWord ++ tailWord_262823).sum := by decide
  have hdescent : baseEnd_262823 < baseStart_262823 := by decide
  rcases family_descends (prefixWord ++ tailWord_262823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262845 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 5]
def baseStart_262845 : Nat := 118140960795 + 262845 * 2 ^ 59
def prefixEnd_262845 : Nat := 4983230072969 + 3 ^ 40 * 262845 * 2
def baseEnd_262845 : Nat := 119969620116559423492181

theorem tailTrace_262845 : CollatzResearch.WordTrace tailWord_262845 prefixEnd_262845 119969620116559423492181 := by
  unfold tailWord_262845
  simp only [CollatzResearch.WordTrace]
  refine ⟨9586744732764930197205989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6391163155176620131470659 9586744732764930197205989)
  ·
    refine ⟨1797514637393424411976123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9586744732764930197205989 1797514637393424411976123)
    ·
      refine ⟨2696271956090136617964185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1797514637393424411976123 2696271956090136617964185)
      ·
        refine ⟨2022203967067602463473139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2696271956090136617964185 2022203967067602463473139)
        ·
          refine ⟨3033305950601403695209709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2022203967067602463473139 3033305950601403695209709)
          ·
            refine ⟨1137489731475526385703641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3033305950601403695209709 1137489731475526385703641)
            ·
              refine ⟨853117298606644789277731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1137489731475526385703641 853117298606644789277731)
              ·
                refine ⟨1279675947909967183916597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853117298606644789277731 1279675947909967183916597)
                ·
                  refine ⟨119969620116559423492181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1279675947909967183916597 119969620116559423492181)
                  ·
                    rfl

theorem cell20_262845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_262845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262845 prefixEnd_262845 := by exact prefixLift 262845
  have htrace : WordTrace (prefixWord ++ tailWord_262845) baseStart_262845 baseEnd_262845 := by
    simpa [prefixWord, tailWord_262845, baseEnd_262845] using wordTrace_append hprefix tailTrace_262845
  have hstable : (prefixWord ++ tailWord_262845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262845).length < 2 ^ (prefixWord ++ tailWord_262845).sum := by decide
  have hdescent : baseEnd_262845 < baseStart_262845 := by decide
  rcases family_descends (prefixWord ++ tailWord_262845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262854 : List Nat := [6, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_262854 : Nat := 118140960795 + 262854 * 2 ^ 59
def prefixEnd_262854 : Nat := 4983230072969 + 3 ^ 40 * 262854 * 2
def baseEnd_262854 : Nat := 119973727961795392192145

theorem tailTrace_262854 : CollatzResearch.WordTrace tailWord_262854 prefixEnd_262854 119973727961795392192145 := by
  unfold tailWord_262854
  simp only [CollatzResearch.WordTrace]
  refine ⟨299596030929135147946363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6391381993154883156189077 299596030929135147946363)
  ·
    refine ⟨449394046393702721919545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299596030929135147946363 449394046393702721919545)
    ·
      refine ⟨337045534795277041439659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 449394046393702721919545 337045534795277041439659)
      ·
        refine ⟨505568302192915562159489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 337045534795277041439659 505568302192915562159489)
        ·
          refine ⟨379176226644686671619617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 505568302192915562159489 379176226644686671619617)
          ·
            refine ⟨284382169983515003714713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379176226644686671619617 284382169983515003714713)
            ·
              refine ⟨213286627487636252786035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284382169983515003714713 213286627487636252786035)
              ·
                refine ⟨319929941231454379179053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213286627487636252786035 319929941231454379179053)
                ·
                  refine ⟨119973727961795392192145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319929941231454379179053 119973727961795392192145)
                  ·
                    rfl

theorem cell20_262854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_262854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262854 prefixEnd_262854 := by exact prefixLift 262854
  have htrace : WordTrace (prefixWord ++ tailWord_262854) baseStart_262854 baseEnd_262854 := by
    simpa [prefixWord, tailWord_262854, baseEnd_262854] using wordTrace_append hprefix tailTrace_262854
  have hstable : (prefixWord ++ tailWord_262854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262854).length < 2 ^ (prefixWord ++ tailWord_262854).sum := by decide
  have hdescent : baseEnd_262854 < baseStart_262854 := by decide
  rcases family_descends (prefixWord ++ tailWord_262854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262862 : List Nat := [4, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_262862 : Nat := 118140960795 + 262862 * 2 ^ 59
def prefixEnd_262862 : Nat := 4983230072969 + 3 ^ 40 * 262862 * 2
def baseEnd_262862 : Nat := 119977379379782919925445

theorem tailTrace_262862 : CollatzResearch.WordTrace tailWord_262862 prefixEnd_262862 119977379379782919925445 := by
  unfold tailWord_262862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1198420596712917762571855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6391576515802228067049893 1198420596712917762571855)
  ·
    refine ⟨1797630895069376643857783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1198420596712917762571855 1797630895069376643857783)
    ·
      refine ⟨2696446342604064965786675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1797630895069376643857783 2696446342604064965786675)
      ·
        refine ⟨4044669513906097448680013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2696446342604064965786675 4044669513906097448680013)
        ·
          refine ⟨1516751067714786543255005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4044669513906097448680013 1516751067714786543255005)
          ·
            refine ⟨568781650393044953720627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1516751067714786543255005 568781650393044953720627)
            ·
              refine ⟨853172475589567430580941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568781650393044953720627 853172475589567430580941)
              ·
                refine ⟨319939678346087786467853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 853172475589567430580941 319939678346087786467853)
                ·
                  refine ⟨119977379379782919925445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 319939678346087786467853 119977379379782919925445)
                  ·
                    rfl

theorem cell20_262862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_262862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262862 prefixEnd_262862 := by exact prefixLift 262862
  have htrace : WordTrace (prefixWord ++ tailWord_262862) baseStart_262862 baseEnd_262862 := by
    simpa [prefixWord, tailWord_262862, baseEnd_262862] using wordTrace_append hprefix tailTrace_262862
  have hstable : (prefixWord ++ tailWord_262862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262862).length < 2 ^ (prefixWord ++ tailWord_262862).sum := by decide
  have hdescent : baseEnd_262862 < baseStart_262862 := by decide
  rcases family_descends (prefixWord ++ tailWord_262862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262921 : List Nat := [1, 2, 1, 1, 3, 2, 4, 3, 3]
def baseStart_262921 : Nat := 118140960795 + 262921 * 2 ^ 59
def prefixEnd_262921 : Nat := 4983230072969 + 3 ^ 40 * 262921 * 2
def baseEnd_262921 : Nat := 120004308587440936958537

theorem tailTrace_262921 : CollatzResearch.WordTrace tailWord_262921 prefixEnd_262921 120004308587440936958537 := by
  unfold tailWord_262921
  simp only [CollatzResearch.WordTrace]
  refine ⟨9589516680489595176972617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6393011120326396784648411 9589516680489595176972617)
  ·
    refine ⟨7192137510367196382729463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9589516680489595176972617 7192137510367196382729463)
    ·
      refine ⟨10788206265550794574094195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7192137510367196382729463 10788206265550794574094195)
      ·
        refine ⟨16182309398326191861141293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10788206265550794574094195 16182309398326191861141293)
        ·
          refine ⟨6068366024372321947927985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16182309398326191861141293 6068366024372321947927985)
          ·
            refine ⟨4551274518279241460945989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6068366024372321947927985 4551274518279241460945989)
            ·
              refine ⟨853363972177357773927373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4551274518279241460945989 853363972177357773927373)
              ·
                refine ⟨320011489566509165222765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 853363972177357773927373 320011489566509165222765)
                ·
                  refine ⟨120004308587440936958537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320011489566509165222765 120004308587440936958537)
                  ·
                    rfl

theorem cell20_262921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_262921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262921 prefixEnd_262921 := by exact prefixLift 262921
  have htrace : WordTrace (prefixWord ++ tailWord_262921) baseStart_262921 baseEnd_262921 := by
    simpa [prefixWord, tailWord_262921, baseEnd_262921] using wordTrace_append hprefix tailTrace_262921
  have hstable : (prefixWord ++ tailWord_262921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262921).length < 2 ^ (prefixWord ++ tailWord_262921).sum := by decide
  have hdescent : baseEnd_262921 < baseStart_262921 := by decide
  rcases family_descends (prefixWord ++ tailWord_262921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262982 : List Nat := [6, 1, 1, 2, 3, 1, 2, 4]
def baseStart_262982 : Nat := 118140960795 + 262982 * 2 ^ 59
def prefixEnd_262982 : Nat := 4983230072969 + 3 ^ 40 * 262982 * 2
def baseEnd_262982 : Nat := 40010716883198611974985

theorem tailTrace_262982 : CollatzResearch.WordTrace tailWord_262982 prefixEnd_262982 40010716883198611974985 := by
  unfold tailWord_262982
  simp only [CollatzResearch.WordTrace]
  refine ⟨299741922914643831091975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6394494355512401729962133 299741922914643831091975)
  ·
    refine ⟨449612884371965746637963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 299741922914643831091975 449612884371965746637963)
    ·
      refine ⟨674419326557948619956945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 449612884371965746637963 674419326557948619956945)
      ·
        refine ⟨505814494918461464967709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 674419326557948619956945 505814494918461464967709)
        ·
          refine ⟨189680435594423049362891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 505814494918461464967709 189680435594423049362891)
          ·
            refine ⟨284520653391634574044337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189680435594423049362891 284520653391634574044337)
            ·
              refine ⟨213390490043725930533253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284520653391634574044337 213390490043725930533253)
              ·
                refine ⟨40010716883198611974985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213390490043725930533253 40010716883198611974985)
                ·
                  rfl

theorem cell20_262982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_262982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262982 prefixEnd_262982 := by exact prefixLift 262982
  have htrace : WordTrace (prefixWord ++ tailWord_262982) baseStart_262982 baseEnd_262982 := by
    simpa [prefixWord, tailWord_262982, baseEnd_262982] using wordTrace_append hprefix tailTrace_262982
  have hstable : (prefixWord ++ tailWord_262982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262982).length < 2 ^ (prefixWord ++ tailWord_262982).sum := by decide
  have hdescent : baseEnd_262982 < baseStart_262982 := by decide
  rcases family_descends (prefixWord ++ tailWord_262982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_262996 : List Nat := [2, 4, 1, 1, 5, 1, 1, 3, 2]
def baseStart_262996 : Nat := 118140960795 + 262996 * 2 ^ 59
def prefixEnd_262996 : Nat := 4983230072969 + 3 ^ 40 * 262996 * 2
def baseEnd_262996 : Nat := 120038540631074009458231

theorem tailTrace_262996 : CollatzResearch.WordTrace tailWord_262996 prefixEnd_262996 120038540631074009458231 := by
  unfold tailWord_262996
  simp only [CollatzResearch.WordTrace]
  refine ⟨4796126077608941492976421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6394834770145255323968561 4796126077608941492976421)
  ·
    refine ⟨899273639551676529933079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4796126077608941492976421 899273639551676529933079)
    ·
      refine ⟨1348910459327514794899619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 899273639551676529933079 1348910459327514794899619)
      ·
        refine ⟨2023365688991272192349429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1348910459327514794899619 2023365688991272192349429)
        ·
          refine ⟨189690533342931768032759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2023365688991272192349429 189690533342931768032759)
          ·
            refine ⟨284535800014397652049139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189690533342931768032759 284535800014397652049139)
            ·
              refine ⟨426803700021596478073709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284535800014397652049139 426803700021596478073709)
              ·
                refine ⟨160051387508098679277641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 426803700021596478073709 160051387508098679277641)
                ·
                  refine ⟨120038540631074009458231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160051387508098679277641 120038540631074009458231)
                  ·
                    rfl

theorem cell20_262996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_262996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_262996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_262996 prefixEnd_262996 := by exact prefixLift 262996
  have htrace : WordTrace (prefixWord ++ tailWord_262996) baseStart_262996 baseEnd_262996 := by
    simpa [prefixWord, tailWord_262996, baseEnd_262996] using wordTrace_append hprefix tailTrace_262996
  have hstable : (prefixWord ++ tailWord_262996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_262996).length < 2 ^ (prefixWord ++ tailWord_262996).sum := by decide
  have hdescent : baseEnd_262996 < baseStart_262996 := by decide
  rcases family_descends (prefixWord ++ tailWord_262996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263011 : List Nat := [1, 1, 1, 5, 3, 1, 8]
def baseStart_263011 : Nat := 118140960795 + 263011 * 2 ^ 59
def prefixEnd_263011 : Nat := 4983230072969 + 3 ^ 40 * 263011 * 2
def baseEnd_263011 : Nat := 13338376337755624884241

theorem tailTrace_263011 : CollatzResearch.WordTrace tailWord_263011 prefixEnd_263011 13338376337755624884241 := by
  unfold tailWord_263011
  simp only [CollatzResearch.WordTrace]
  refine ⟨9592799250163540547748887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6395199500109027031832591 9592799250163540547748887)
  ·
    refine ⟨14389198875245310821623331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9592799250163540547748887 14389198875245310821623331)
    ·
      refine ⟨21583798312867966232434997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14389198875245310821623331 21583798312867966232434997)
      ·
        refine ⟨2023481091831371834290781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21583798312867966232434997 2023481091831371834290781)
        ·
          refine ⟨758805409436764437859043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2023481091831371834290781 758805409436764437859043)
          ·
            refine ⟨1138208114155146656788565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758805409436764437859043 1138208114155146656788565)
            ·
              refine ⟨13338376337755624884241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1138208114155146656788565 13338376337755624884241)
              ·
                rfl

theorem cell20_263011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 8].length) (baseStart_263011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263011 prefixEnd_263011 := by exact prefixLift 263011
  have htrace : WordTrace (prefixWord ++ tailWord_263011) baseStart_263011 baseEnd_263011 := by
    simpa [prefixWord, tailWord_263011, baseEnd_263011] using wordTrace_append hprefix tailTrace_263011
  have hstable : (prefixWord ++ tailWord_263011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263011).length < 2 ^ (prefixWord ++ tailWord_263011).sum := by decide
  have hdescent : baseEnd_263011 < baseStart_263011 := by decide
  rcases family_descends (prefixWord ++ tailWord_263011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263049 : List Nat := [1, 2, 1, 1, 5, 2, 2, 6]
def baseStart_263049 : Nat := 118140960795 + 263049 * 2 ^ 59
def prefixEnd_263049 : Nat := 4983230072969 + 3 ^ 40 * 263049 * 2
def baseEnd_263049 : Nat := 40020910425080460230449

theorem tailTrace_263049 : CollatzResearch.WordTrace tailWord_263049 prefixEnd_263049 40020910425080460230449 := by
  unfold tailWord_263049
  simp only [CollatzResearch.WordTrace]
  refine ⟨9594185224025873037632201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6396123482683915358421467 9594185224025873037632201)
  ·
    refine ⟨7195638918019404778224151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9594185224025873037632201 7195638918019404778224151)
    ·
      refine ⟨10793458377029107167336227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7195638918019404778224151 10793458377029107167336227)
      ·
        refine ⟨16190187565543660751004341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10793458377029107167336227 16190187565543660751004341)
        ·
          refine ⟨1517830084269718195406657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16190187565543660751004341 1517830084269718195406657)
          ·
            refine ⟨1138372563202288646554993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1517830084269718195406657 1138372563202288646554993)
            ·
              refine ⟨853779422401716484916245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1138372563202288646554993 853779422401716484916245)
              ·
                refine ⟨40020910425080460230449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 853779422401716484916245 40020910425080460230449)
                ·
                  rfl

theorem cell20_263049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 6].length) (baseStart_263049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263049 prefixEnd_263049 := by exact prefixLift 263049
  have htrace : WordTrace (prefixWord ++ tailWord_263049) baseStart_263049 baseEnd_263049 := by
    simpa [prefixWord, tailWord_263049, baseEnd_263049] using wordTrace_append hprefix tailTrace_263049
  have hstable : (prefixWord ++ tailWord_263049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263049).length < 2 ^ (prefixWord ++ tailWord_263049).sum := by decide
  have hdescent : baseEnd_263049 < baseStart_263049 := by decide
  rcases family_descends (prefixWord ++ tailWord_263049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263066 : List Nat := [3, 1, 1, 4, 4, 7]
def baseStart_263066 : Nat := 118140960795 + 263066 * 2 ^ 59
def prefixEnd_263066 : Nat := 4983230072969 + 3 ^ 40 * 263066 * 2
def baseEnd_263066 : Nat := 4447055205128328782393

theorem tailTrace_263066 : CollatzResearch.WordTrace tailWord_263066 prefixEnd_263066 4447055205128328782393 := by
  unfold tailWord_263066
  simp only [CollatzResearch.WordTrace]
  refine ⟨2398701316241071235250263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6396536843309523294000701 2398701316241071235250263)
  ·
    refine ⟨3598051974361606852875395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2398701316241071235250263 3598051974361606852875395)
    ·
      refine ⟨5397077961542410279313093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3598051974361606852875395 5397077961542410279313093)
      ·
        refine ⟨1011952117789201927371205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5397077961542410279313093 1011952117789201927371205)
        ·
          refine ⟨189741022085475361382101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1011952117789201927371205 189741022085475361382101)
          ·
            refine ⟨4447055205128328782393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 189741022085475361382101 4447055205128328782393)
            ·
              rfl

theorem cell20_263066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 7].length) (baseStart_263066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263066 prefixEnd_263066 := by exact prefixLift 263066
  have htrace : WordTrace (prefixWord ++ tailWord_263066) baseStart_263066 baseEnd_263066 := by
    simpa [prefixWord, tailWord_263066, baseEnd_263066] using wordTrace_append hprefix tailTrace_263066
  have hstable : (prefixWord ++ tailWord_263066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263066).length < 2 ^ (prefixWord ++ tailWord_263066).sum := by decide
  have hdescent : baseEnd_263066 < baseStart_263066 := by decide
  rcases family_descends (prefixWord ++ tailWord_263066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263104 : List Nat := [2, 1, 1, 2, 3, 4, 3, 4]
def baseStart_263104 : Nat := 118140960795 + 263104 * 2 ^ 59
def prefixEnd_263104 : Nat := 4983230072969 + 3 ^ 40 * 263104 * 2
def baseEnd_263104 : Nat := 40029278257968544619263

theorem tailTrace_263104 : CollatzResearch.WordTrace tailWord_263104 prefixEnd_263104 40029278257968544619263 := by
  unfold tailWord_263104
  simp only [CollatzResearch.WordTrace]
  refine ⟨4798095619413308715442183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6397460825884411620589577 4798095619413308715442183)
  ·
    refine ⟨7197143429119963073163275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4798095619413308715442183 7197143429119963073163275)
    ·
      refine ⟨10795715143679944609744913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7197143429119963073163275 10795715143679944609744913)
      ·
        refine ⟨8096786357759958457308685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10795715143679944609744913 8096786357759958457308685)
        ·
          refine ⟨3036294884159984421490757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8096786357759958457308685 3036294884159984421490757)
          ·
            refine ⟨569305290779997079029517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3036294884159984421490757 569305290779997079029517)
            ·
              refine ⟨213489484042498904636069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 569305290779997079029517 213489484042498904636069)
              ·
                refine ⟨40029278257968544619263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213489484042498904636069 40029278257968544619263)
                ·
                  rfl

theorem cell20_263104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 4].length) (baseStart_263104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263104 prefixEnd_263104 := by exact prefixLift 263104
  have htrace : WordTrace (prefixWord ++ tailWord_263104) baseStart_263104 baseEnd_263104 := by
    simpa [prefixWord, tailWord_263104, baseEnd_263104] using wordTrace_append hprefix tailTrace_263104
  have hstable : (prefixWord ++ tailWord_263104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263104).length < 2 ^ (prefixWord ++ tailWord_263104).sum := by decide
  have hdescent : baseEnd_263104 < baseStart_263104 := by decide
  rcases family_descends (prefixWord ++ tailWord_263104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263128 : List Nat := [2, 1, 2, 2, 2, 5, 1, 2, 3]
def baseStart_263128 : Nat := 118140960795 + 263128 * 2 ^ 59
def prefixEnd_263128 : Nat := 4983230072969 + 3 ^ 40 * 263128 * 2
def baseEnd_263128 : Nat := 120098789027868217057691

theorem tailTrace_263128 : CollatzResearch.WordTrace tailWord_263128 prefixEnd_263128 120098789027868217057691 := by
  unfold tailWord_263128
  simp only [CollatzResearch.WordTrace]
  refine ⟨4798533295369834764879019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6398044393826446353172025 4798533295369834764879019)
  ·
    refine ⟨7197799943054752147318529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4798533295369834764879019 7197799943054752147318529)
    ·
      refine ⟨5398349957291064110488897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7197799943054752147318529 5398349957291064110488897)
      ·
        refine ⟨4048762467968298082866673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5398349957291064110488897 4048762467968298082866673)
        ·
          refine ⟨3036571850976223562150005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4048762467968298082866673 3036571850976223562150005)
          ·
            refine ⟨284678611029020958951563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3036571850976223562150005 284678611029020958951563)
            ·
              refine ⟨427017916543531438427345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284678611029020958951563 427017916543531438427345)
              ·
                refine ⟨320263437407648578820509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 427017916543531438427345 320263437407648578820509)
                ·
                  refine ⟨120098789027868217057691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320263437407648578820509 120098789027868217057691)
                  ·
                    rfl

theorem cell20_263128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 3].length) (baseStart_263128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263128 prefixEnd_263128 := by exact prefixLift 263128
  have htrace : WordTrace (prefixWord ++ tailWord_263128) baseStart_263128 baseEnd_263128 := by
    simpa [prefixWord, tailWord_263128, baseEnd_263128] using wordTrace_append hprefix tailTrace_263128
  have hstable : (prefixWord ++ tailWord_263128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263128).length < 2 ^ (prefixWord ++ tailWord_263128).sum := by decide
  have hdescent : baseEnd_263128 < baseStart_263128 := by decide
  rcases family_descends (prefixWord ++ tailWord_263128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263135 : List Nat := [1, 1, 2, 3, 5, 1, 2, 1, 4]
def baseStart_263135 : Nat := 118140960795 + 263135 * 2 ^ 59
def prefixEnd_263135 : Nat := 4983230072969 + 3 ^ 40 * 263135 * 2
def baseEnd_263135 : Nat := 120101984018607303824329

theorem tailTrace_263135 : CollatzResearch.WordTrace tailWord_263135 prefixEnd_263135 120101984018607303824329 := by
  unfold tailWord_263135
  simp only [CollatzResearch.WordTrace]
  refine ⟨9597321901714309725262859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6398214601142873150175239 9597321901714309725262859)
  ·
    refine ⟨14395982852571464587894289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9597321901714309725262859 14395982852571464587894289)
    ·
      refine ⟨10796987139428598440920717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14395982852571464587894289 10796987139428598440920717)
      ·
        refine ⟨4048870177285724415345269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10796987139428598440920717 4048870177285724415345269)
        ·
          refine ⟨379581579120536663938619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4048870177285724415345269 379581579120536663938619)
          ·
            refine ⟨569372368680804995907929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379581579120536663938619 569372368680804995907929)
            ·
              refine ⟨427029276510603746930947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 569372368680804995907929 427029276510603746930947)
              ·
                refine ⟨640543914765905620396421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427029276510603746930947 640543914765905620396421)
                ·
                  refine ⟨120101984018607303824329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 640543914765905620396421 120101984018607303824329)
                  ·
                    rfl

theorem cell20_263135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 2, 1, 4].length) (baseStart_263135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263135 prefixEnd_263135 := by exact prefixLift 263135
  have htrace : WordTrace (prefixWord ++ tailWord_263135) baseStart_263135 baseEnd_263135 := by
    simpa [prefixWord, tailWord_263135, baseEnd_263135] using wordTrace_append hprefix tailTrace_263135
  have hstable : (prefixWord ++ tailWord_263135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263135).length < 2 ^ (prefixWord ++ tailWord_263135).sum := by decide
  have hdescent : baseEnd_263135 < baseStart_263135 := by decide
  rcases family_descends (prefixWord ++ tailWord_263135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263177 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 6]
def baseStart_263177 : Nat := 118140960795 + 263177 * 2 ^ 59
def prefixEnd_263177 : Nat := 4983230072969 + 3 ^ 40 * 263177 * 2
def baseEnd_263177 : Nat := 120121153963041824424157

theorem tailTrace_263177 : CollatzResearch.WordTrace tailWord_263177 prefixEnd_263177 120121153963041824424157 := by
  unfold tailWord_263177
  simp only [CollatzResearch.WordTrace]
  refine ⟨9598853767562150898291785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6399235845041433932194523 9598853767562150898291785)
  ·
    refine ⟨7199140325671613173718839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9598853767562150898291785 7199140325671613173718839)
    ·
      refine ⟨10798710488507419760578259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7199140325671613173718839 10798710488507419760578259)
      ·
        refine ⟨16198065732761129640867389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10798710488507419760578259 16198065732761129640867389)
        ·
          refine ⟨6074274649785423615325271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16198065732761129640867389 6074274649785423615325271)
          ·
            refine ⟨9111411974678135422987907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6074274649785423615325271 9111411974678135422987907)
            ·
              refine ⟨13667117962017203134481861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9111411974678135422987907 13667117962017203134481861)
              ·
                refine ⟨2562584617878225587715349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13667117962017203134481861 2562584617878225587715349)
                ·
                  refine ⟨120121153963041824424157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2562584617878225587715349 120121153963041824424157)
                  ·
                    rfl

theorem cell20_263177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_263177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263177 prefixEnd_263177 := by exact prefixLift 263177
  have htrace : WordTrace (prefixWord ++ tailWord_263177) baseStart_263177 baseEnd_263177 := by
    simpa [prefixWord, tailWord_263177, baseEnd_263177] using wordTrace_append hprefix tailTrace_263177
  have hstable : (prefixWord ++ tailWord_263177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263177).length < 2 ^ (prefixWord ++ tailWord_263177).sum := by decide
  have hdescent : baseEnd_263177 < baseStart_263177 := by decide
  rcases family_descends (prefixWord ++ tailWord_263177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263186 : List Nat := [3, 2, 5, 1, 1, 2, 1, 1, 4]
def baseStart_263186 : Nat := 118140960795 + 263186 * 2 ^ 59
def prefixEnd_263186 : Nat := 4983230072969 + 3 ^ 40 * 263186 * 2
def baseEnd_263186 : Nat := 120125261808277793124121

theorem tailTrace_263186 : CollatzResearch.WordTrace tailWord_263186 prefixEnd_263186 120125261808277793124121 := by
  unfold tailWord_263186
  simp only [CollatzResearch.WordTrace]
  refine ⟨2399795506132386358842353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6399454683019696956912941 2399795506132386358842353)
  ·
    refine ⟨1799846629599289769131765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2399795506132386358842353 1799846629599289769131765)
    ·
      refine ⟨168735621524933415856103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1799846629599289769131765 168735621524933415856103)
      ·
        refine ⟨253103432287400123784155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 168735621524933415856103 253103432287400123784155)
        ·
          refine ⟨379655148431100185676233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253103432287400123784155 379655148431100185676233)
          ·
            refine ⟨284741361323325139257175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379655148431100185676233 284741361323325139257175)
            ·
              refine ⟨427112041984987708885763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284741361323325139257175 427112041984987708885763)
              ·
                refine ⟨640668062977481563328645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 427112041984987708885763 640668062977481563328645)
                ·
                  refine ⟨120125261808277793124121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 640668062977481563328645 120125261808277793124121)
                  ·
                    rfl

theorem cell20_263186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_263186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263186 prefixEnd_263186 := by exact prefixLift 263186
  have htrace : WordTrace (prefixWord ++ tailWord_263186) baseStart_263186 baseEnd_263186 := by
    simpa [prefixWord, tailWord_263186, baseEnd_263186] using wordTrace_append hprefix tailTrace_263186
  have hstable : (prefixWord ++ tailWord_263186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263186).length < 2 ^ (prefixWord ++ tailWord_263186).sum := by decide
  have hdescent : baseEnd_263186 < baseStart_263186 := by decide
  rcases family_descends (prefixWord ++ tailWord_263186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263200 : List Nat := [2, 1, 1, 7, 1, 2, 2, 1, 3]
def baseStart_263200 : Nat := 118140960795 + 263200 * 2 ^ 59
def prefixEnd_263200 : Nat := 4983230072969 + 3 ^ 40 * 263200 * 2
def baseEnd_263200 : Nat := 120131651789755966657397

theorem tailTrace_263200 : CollatzResearch.WordTrace tailWord_263200 prefixEnd_263200 120131651789755966657397 := by
  unfold tailWord_263200
  simp only [CollatzResearch.WordTrace]
  refine ⟨4799846323239412913189527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6399795097652550550919369 4799846323239412913189527)
  ·
    refine ⟨7199769484859119369784291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4799846323239412913189527 7199769484859119369784291)
    ·
      refine ⟨10799654227288679054676437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7199769484859119369784291 10799654227288679054676437)
      ·
        refine ⟨253116895952078415343979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 10799654227288679054676437 253116895952078415343979)
        ·
          refine ⟨379675343928117623015969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253116895952078415343979 379675343928117623015969)
          ·
            refine ⟨284756507946088217261977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379675343928117623015969 284756507946088217261977)
            ·
              refine ⟨213567380959566162946483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 284756507946088217261977 213567380959566162946483)
              ·
                refine ⟨320351071439349244419725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213567380959566162946483 320351071439349244419725)
                ·
                  refine ⟨120131651789755966657397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320351071439349244419725 120131651789755966657397)
                  ·
                    rfl

theorem cell20_263200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 3].length) (baseStart_263200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263200 prefixEnd_263200 := by exact prefixLift 263200
  have htrace : WordTrace (prefixWord ++ tailWord_263200) baseStart_263200 baseEnd_263200 := by
    simpa [prefixWord, tailWord_263200, baseEnd_263200] using wordTrace_append hprefix tailTrace_263200
  have hstable : (prefixWord ++ tailWord_263200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263200).length < 2 ^ (prefixWord ++ tailWord_263200).sum := by decide
  have hdescent : baseEnd_263200 < baseStart_263200 := by decide
  rcases family_descends (prefixWord ++ tailWord_263200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263201 : List Nat := [1, 2, 3, 2, 3, 1, 1, 7]
def baseStart_263201 : Nat := 118140960795 + 263201 * 2 ^ 59
def prefixEnd_263201 : Nat := 4983230072969 + 3 ^ 40 * 263201 * 2
def baseEnd_263201 : Nat := 40044036072334802541353

theorem tailTrace_263201 : CollatzResearch.WordTrace tailWord_263201 prefixEnd_263201 40044036072334802541353 := by
  unfold tailWord_263201
  simp only [CollatzResearch.WordTrace]
  refine ⟨9599729119475202997165457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6399819412983468664776971 9599729119475202997165457)
  ·
    refine ⟨7199796839606402247874093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9599729119475202997165457 7199796839606402247874093)
    ·
      refine ⟨2699923814852400842952785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7199796839606402247874093 2699923814852400842952785)
      ·
        refine ⟨2024942861139300632214589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2699923814852400842952785 2024942861139300632214589)
        ·
          refine ⟨759353572927237737080471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2024942861139300632214589 759353572927237737080471)
          ·
            refine ⟨1139030359390856605620707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759353572927237737080471 1139030359390856605620707)
            ·
              refine ⟨1708545539086284908431061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1139030359390856605620707 1708545539086284908431061)
              ·
                refine ⟨40044036072334802541353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1708545539086284908431061 40044036072334802541353)
                ·
                  rfl

theorem cell20_263201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 7].length) (baseStart_263201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263201 prefixEnd_263201 := by exact prefixLift 263201
  have htrace : WordTrace (prefixWord ++ tailWord_263201) baseStart_263201 baseEnd_263201 := by
    simpa [prefixWord, tailWord_263201, baseEnd_263201] using wordTrace_append hprefix tailTrace_263201
  have hstable : (prefixWord ++ tailWord_263201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263201).length < 2 ^ (prefixWord ++ tailWord_263201).sum := by decide
  have hdescent : baseEnd_263201 < baseStart_263201 := by decide
  rcases family_descends (prefixWord ++ tailWord_263201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263204 : List Nat := [2, 3, 1, 4, 1, 2, 1, 3, 3]
def baseStart_263204 : Nat := 118140960795 + 263204 * 2 ^ 59
def prefixEnd_263204 : Nat := 4983230072969 + 3 ^ 40 * 263204 * 2
def baseEnd_263204 : Nat := 120133477498749730524047

theorem tailTrace_263204 : CollatzResearch.WordTrace tailWord_263204 prefixEnd_263204 120133477498749730524047 := by
  unfold tailWord_263204
  simp only [CollatzResearch.WordTrace]
  refine ⟨4799919269232167254762333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6399892358976223006349777 4799919269232167254762333)
  ·
    refine ⟨1799969725962062720535875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4799919269232167254762333 1799969725962062720535875)
    ·
      refine ⟨2699954588943094080803813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1799969725962062720535875 2699954588943094080803813)
      ·
        refine ⟨506241485426830140150715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2699954588943094080803813 506241485426830140150715)
        ·
          refine ⟨759362228140245210226073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 506241485426830140150715 759362228140245210226073)
          ·
            refine ⟨569521671105183907669555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 759362228140245210226073 569521671105183907669555)
            ·
              refine ⟨854282506657775861504333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569521671105183907669555 854282506657775861504333)
              ·
                refine ⟨320355939996665948064125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 854282506657775861504333 320355939996665948064125)
                ·
                  refine ⟨120133477498749730524047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320355939996665948064125 120133477498749730524047)
                  ·
                    rfl

theorem cell20_263204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_263204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263204 prefixEnd_263204 := by exact prefixLift 263204
  have htrace : WordTrace (prefixWord ++ tailWord_263204) baseStart_263204 baseEnd_263204 := by
    simpa [prefixWord, tailWord_263204, baseEnd_263204] using wordTrace_append hprefix tailTrace_263204
  have hstable : (prefixWord ++ tailWord_263204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263204).length < 2 ^ (prefixWord ++ tailWord_263204).sum := by decide
  have hdescent : baseEnd_263204 < baseStart_263204 := by decide
  rcases family_descends (prefixWord ++ tailWord_263204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263245 : List Nat := [1, 6, 1, 1, 1, 2, 4, 2, 2]
def baseStart_263245 : Nat := 118140960795 + 263245 * 2 ^ 59
def prefixEnd_263245 : Nat := 4983230072969 + 3 ^ 40 * 263245 * 2
def baseEnd_263245 : Nat := 120152191015935810157213

theorem tailTrace_263245 : CollatzResearch.WordTrace tailWord_263245 prefixEnd_263245 120152191015935810157213 := by
  unfold tailWord_263245
  simp only [CollatzResearch.WordTrace]
  refine ⟨9601333931315798511767189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6400889287543865674511459 9601333931315798511767189)
  ·
    refine ⟨450062528030428055239087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9601333931315798511767189 450062528030428055239087)
    ·
      refine ⟨675093792045642082858631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450062528030428055239087 675093792045642082858631)
      ·
        refine ⟨1012640688068463124287947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675093792045642082858631 1012640688068463124287947)
        ·
          refine ⟨1518961032102694686431921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1012640688068463124287947 1518961032102694686431921)
          ·
            refine ⟨1139220774077021014823941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1518961032102694686431921 1139220774077021014823941)
            ·
              refine ⟨213603895139441440279489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1139220774077021014823941 213603895139441440279489)
              ·
                refine ⟨160202921354581080209617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213603895139441440279489 160202921354581080209617)
                ·
                  refine ⟨120152191015935810157213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160202921354581080209617 120152191015935810157213)
                  ·
                    rfl

theorem cell20_263245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_263245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263245 prefixEnd_263245 := by exact prefixLift 263245
  have htrace : WordTrace (prefixWord ++ tailWord_263245) baseStart_263245 baseEnd_263245 := by
    simpa [prefixWord, tailWord_263245, baseEnd_263245] using wordTrace_append hprefix tailTrace_263245
  have hstable : (prefixWord ++ tailWord_263245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263245).length < 2 ^ (prefixWord ++ tailWord_263245).sum := by decide
  have hdescent : baseEnd_263245 < baseStart_263245 := by decide
  rcases family_descends (prefixWord ++ tailWord_263245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263287 : List Nat := [1, 1, 3, 1, 1, 4, 4, 3, 2]
def baseStart_263287 : Nat := 118140960795 + 263287 * 2 ^ 59
def prefixEnd_263287 : Nat := 4983230072969 + 3 ^ 40 * 263287 * 2
def baseEnd_263287 : Nat := 120171360960370330757041

theorem tailTrace_263287 : CollatzResearch.WordTrace tailWord_263287 prefixEnd_263287 120171360960370330757041 := by
  unfold tailWord_263287
  simp only [CollatzResearch.WordTrace]
  refine ⟨9602865797163639684796115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6401910531442426456530743 9602865797163639684796115)
  ·
    refine ⟨14404298695745459527194173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9602865797163639684796115 14404298695745459527194173)
    ·
      refine ⟨5401612010904547322697815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14404298695745459527194173 5401612010904547322697815)
      ·
        refine ⟨8102418016356820984046723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5401612010904547322697815 8102418016356820984046723)
        ·
          refine ⟨12153627024535231476070085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8102418016356820984046723 12153627024535231476070085)
          ·
            refine ⟨2278805067100355901763141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12153627024535231476070085 2278805067100355901763141)
            ·
              refine ⟨427275950081316731580589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2278805067100355901763141 427275950081316731580589)
              ·
                refine ⟨160228481280493774342721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 427275950081316731580589 160228481280493774342721)
                ·
                  refine ⟨120171360960370330757041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160228481280493774342721 120171360960370330757041)
                  ·
                    rfl

theorem cell20_263287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3, 2].length) (baseStart_263287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263287 prefixEnd_263287 := by exact prefixLift 263287
  have htrace : WordTrace (prefixWord ++ tailWord_263287) baseStart_263287 baseEnd_263287 := by
    simpa [prefixWord, tailWord_263287, baseEnd_263287] using wordTrace_append hprefix tailTrace_263287
  have hstable : (prefixWord ++ tailWord_263287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263287).length < 2 ^ (prefixWord ++ tailWord_263287).sum := by decide
  have hdescent : baseEnd_263287 < baseStart_263287 := by decide
  rcases family_descends (prefixWord ++ tailWord_263287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263301 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 5]
def baseStart_263301 : Nat := 118140960795 + 263301 * 2 ^ 59
def prefixEnd_263301 : Nat := 4983230072969 + 3 ^ 40 * 263301 * 2
def baseEnd_263301 : Nat := 120177750941848504290317

theorem tailTrace_263301 : CollatzResearch.WordTrace tailWord_263301 prefixEnd_263301 120177750941848504290317 := by
  unfold tailWord_263301
  simp only [CollatzResearch.WordTrace]
  refine ⟨9603376419112920075805757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6402250946075280050537171 9603376419112920075805757)
  ·
    refine ⟨3601266157167345028427159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9603376419112920075805757 3601266157167345028427159)
    ·
      refine ⟨5401899235751017542640739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3601266157167345028427159 5401899235751017542640739)
      ·
        refine ⟨8102848853626526313961109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5401899235751017542640739 8102848853626526313961109)
        ·
          refine ⟨379821040013743420966927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8102848853626526313961109 379821040013743420966927)
          ·
            refine ⟨569731560020615131450391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379821040013743420966927 569731560020615131450391)
            ·
              refine ⟨854597340030922697175587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 569731560020615131450391 854597340030922697175587)
              ·
                refine ⟨1281896010046384045763381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854597340030922697175587 1281896010046384045763381)
                ·
                  refine ⟨120177750941848504290317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1281896010046384045763381 120177750941848504290317)
                  ·
                    rfl

theorem cell20_263301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_263301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263301 prefixEnd_263301 := by exact prefixLift 263301
  have htrace : WordTrace (prefixWord ++ tailWord_263301) baseStart_263301 baseEnd_263301 := by
    simpa [prefixWord, tailWord_263301, baseEnd_263301] using wordTrace_append hprefix tailTrace_263301
  have hstable : (prefixWord ++ tailWord_263301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263301).length < 2 ^ (prefixWord ++ tailWord_263301).sum := by decide
  have hdescent : baseEnd_263301 < baseStart_263301 := by decide
  rcases family_descends (prefixWord ++ tailWord_263301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263332 : List Nat := [2, 3, 1, 2, 3, 1, 4, 4]
def baseStart_263332 : Nat := 118140960795 + 263332 * 2 ^ 59
def prefixEnd_263332 : Nat := 4983230072969 + 3 ^ 40 * 263332 * 2
def baseEnd_263332 : Nat := 40063966728850058085619

theorem tailTrace_263332 : CollatzResearch.WordTrace tailWord_263332 prefixEnd_263332 40063966728850058085619 := by
  unfold tailWord_263332
  simp only [CollatzResearch.WordTrace]
  refine ⟨4802253541000306185092125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6403004721333741580122833 4802253541000306185092125)
  ·
    refine ⟨1800845077875114819409547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4802253541000306185092125 1800845077875114819409547)
    ·
      refine ⟨2701267616812672229114321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1800845077875114819409547 2701267616812672229114321)
      ·
        refine ⟨2025950712609504171835741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2701267616812672229114321 2025950712609504171835741)
        ·
          refine ⟨759731517228564064438403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2025950712609504171835741 759731517228564064438403)
          ·
            refine ⟨1139597275842846096657605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759731517228564064438403 1139597275842846096657605)
            ·
              refine ⟨213674489220533643123301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1139597275842846096657605 213674489220533643123301)
              ·
                refine ⟨40063966728850058085619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213674489220533643123301 40063966728850058085619)
                ·
                  rfl

theorem cell20_263332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 4].length) (baseStart_263332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263332 prefixEnd_263332 := by exact prefixLift 263332
  have htrace : WordTrace (prefixWord ++ tailWord_263332) baseStart_263332 baseEnd_263332 := by
    simpa [prefixWord, tailWord_263332, baseEnd_263332] using wordTrace_append hprefix tailTrace_263332
  have hstable : (prefixWord ++ tailWord_263332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263332).length < 2 ^ (prefixWord ++ tailWord_263332).sum := by decide
  have hdescent : baseEnd_263332 < baseStart_263332 := by decide
  rcases family_descends (prefixWord ++ tailWord_263332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263353 : List Nat := [1, 2, 1, 4, 1, 5, 6]
def baseStart_263353 : Nat := 118140960795 + 263353 * 2 ^ 59
def prefixEnd_263353 : Nat := 4983230072969 + 3 ^ 40 * 263353 * 2
def baseEnd_263353 : Nat := 13355720573196381617419

theorem tailTrace_263353 : CollatzResearch.WordTrace tailWord_263353 prefixEnd_263353 13355720573196381617419 := by
  unfold tailWord_263353
  simp only [CollatzResearch.WordTrace]
  refine ⟨9605273014924532956698713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6403515343283021971132475 9605273014924532956698713)
  ·
    refine ⟨7203954761193399717524035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9605273014924532956698713 7203954761193399717524035)
    ·
      refine ⟨10805932141790099576286053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7203954761193399717524035 10805932141790099576286053)
      ·
        refine ⟨2026112276585643670553635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10805932141790099576286053 2026112276585643670553635)
        ·
          refine ⟨3039168414878465505830453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2026112276585643670553635 3039168414878465505830453)
          ·
            refine ⟨284922038894856141171605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3039168414878465505830453 284922038894856141171605)
            ·
              refine ⟨13355720573196381617419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 284922038894856141171605 13355720573196381617419)
              ·
                rfl

theorem cell20_263353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 5, 6].length) (baseStart_263353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263353 prefixEnd_263353 := by exact prefixLift 263353
  have htrace : WordTrace (prefixWord ++ tailWord_263353) baseStart_263353 baseEnd_263353 := by
    simpa [prefixWord, tailWord_263353, baseEnd_263353] using wordTrace_append hprefix tailTrace_263353
  have hstable : (prefixWord ++ tailWord_263353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263353).length < 2 ^ (prefixWord ++ tailWord_263353).sum := by decide
  have hdescent : baseEnd_263353 < baseStart_263353 := by decide
  rcases family_descends (prefixWord ++ tailWord_263353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263442 : List Nat := [3, 2, 4, 2, 1, 1, 3, 4]
def baseStart_263442 : Nat := 118140960795 + 263442 * 2 ^ 59
def prefixEnd_263442 : Nat := 4983230072969 + 3 ^ 40 * 263442 * 2
def baseEnd_263442 : Nat := 40080702394626226863247

theorem tailTrace_263442 : CollatzResearch.WordTrace tailWord_263442 prefixEnd_263442 40080702394626226863247 := by
  unfold tailWord_263442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2402129777900525289172145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6405679407734734104459053 2402129777900525289172145)
  ·
    refine ⟨1801597333425393966879109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2402129777900525289172145 1801597333425393966879109)
    ·
      refine ⟨337799500017261368789833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1801597333425393966879109 337799500017261368789833)
      ·
        refine ⟨253349625012946026592375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 337799500017261368789833 253349625012946026592375)
        ·
          refine ⟨380024437519419039888563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253349625012946026592375 380024437519419039888563)
          ·
            refine ⟨570036656279128559832845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380024437519419039888563 570036656279128559832845)
            ·
              refine ⟨213763746104673209937317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 570036656279128559832845 213763746104673209937317)
              ·
                refine ⟨40080702394626226863247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 213763746104673209937317 40080702394626226863247)
                ·
                  rfl

theorem cell20_263442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_263442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263442 prefixEnd_263442 := by exact prefixLift 263442
  have htrace : WordTrace (prefixWord ++ tailWord_263442) baseStart_263442 baseEnd_263442 := by
    simpa [prefixWord, tailWord_263442, baseEnd_263442] using wordTrace_append hprefix tailTrace_263442
  have hstable : (prefixWord ++ tailWord_263442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263442).length < 2 ^ (prefixWord ++ tailWord_263442).sum := by decide
  have hdescent : baseEnd_263442 < baseStart_263442 := by decide
  rcases family_descends (prefixWord ++ tailWord_263442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263456 : List Nat := [2, 1, 1, 5, 3, 1, 2, 3, 2]
def baseStart_263456 : Nat := 118140960795 + 263456 * 2 ^ 59
def prefixEnd_263456 : Nat := 4983230072969 + 3 ^ 40 * 263456 * 2
def baseEnd_263456 : Nat := 120248497165356854123017

theorem tailTrace_263456 : CollatzResearch.WordTrace tailWord_263456 prefixEnd_263456 120248497165356854123017 := by
  unfold tailWord_263456
  simp only [CollatzResearch.WordTrace]
  refine ⟨4804514866775690773849111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6406019822367587698465481 4804514866775690773849111)
  ·
    refine ⟨7206772300163536160773667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4804514866775690773849111 7206772300163536160773667)
    ·
      refine ⟨10810158450245304241160501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7206772300163536160773667 10810158450245304241160501)
      ·
        refine ⟨1013452354710497272608797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10810158450245304241160501 1013452354710497272608797)
        ·
          refine ⟨380044633016436477228299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1013452354710497272608797 380044633016436477228299)
          ·
            refine ⟨570066949524654715842449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380044633016436477228299 570066949524654715842449)
            ·
              refine ⟨427550212143491036881837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570066949524654715842449 427550212143491036881837)
              ·
                refine ⟨160331329553809138830689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 427550212143491036881837 160331329553809138830689)
                ·
                  refine ⟨120248497165356854123017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160331329553809138830689 120248497165356854123017)
                  ·
                    rfl

theorem cell20_263456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 3, 2].length) (baseStart_263456 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263456 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263456 prefixEnd_263456 := by exact prefixLift 263456
  have htrace : WordTrace (prefixWord ++ tailWord_263456) baseStart_263456 baseEnd_263456 := by
    simpa [prefixWord, tailWord_263456, baseEnd_263456] using wordTrace_append hprefix tailTrace_263456
  have hstable : (prefixWord ++ tailWord_263456).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263456).length < 2 ^ (prefixWord ++ tailWord_263456).sum := by decide
  have hdescent : baseEnd_263456 < baseStart_263456 := by decide
  rcases family_descends (prefixWord ++ tailWord_263456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263477 : List Nat := [1, 3, 3, 1, 2, 2, 2, 4, 2]
def baseStart_263477 : Nat := 118140960795 + 263477 * 2 ^ 59
def prefixEnd_263477 : Nat := 4983230072969 + 3 ^ 40 * 263477 * 2
def baseEnd_263477 : Nat := 120258082137574114422931

theorem tailTrace_263477 : CollatzResearch.WordTrace tailWord_263477 prefixEnd_263477 120258082137574114422931 := by
  unfold tailWord_263477
  simp only [CollatzResearch.WordTrace]
  refine ⟨9609795666475302134212685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6406530444316868089475123 9609795666475302134212685)
  ·
    refine ⟨3603673374928238300329757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9609795666475302134212685 3603673374928238300329757)
    ·
      refine ⟨1351377515598089362623659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3603673374928238300329757 1351377515598089362623659)
      ·
        refine ⟨2027066273397134043935489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1351377515598089362623659 2027066273397134043935489)
        ·
          refine ⟨1520299705047850532951617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2027066273397134043935489 1520299705047850532951617)
          ·
            refine ⟨1140224778785887899713713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1520299705047850532951617 1140224778785887899713713)
            ·
              refine ⟨855168584089415924785285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1140224778785887899713713 855168584089415924785285)
              ·
                refine ⟨160344109516765485897241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 855168584089415924785285 160344109516765485897241)
                ·
                  refine ⟨120258082137574114422931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160344109516765485897241 120258082137574114422931)
                  ·
                    rfl

theorem cell20_263477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 2].length) (baseStart_263477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263477 prefixEnd_263477 := by exact prefixLift 263477
  have htrace : WordTrace (prefixWord ++ tailWord_263477) baseStart_263477 baseEnd_263477 := by
    simpa [prefixWord, tailWord_263477, baseEnd_263477] using wordTrace_append hprefix tailTrace_263477
  have hstable : (prefixWord ++ tailWord_263477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263477).length < 2 ^ (prefixWord ++ tailWord_263477).sum := by decide
  have hdescent : baseEnd_263477 < baseStart_263477 := by decide
  rcases family_descends (prefixWord ++ tailWord_263477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263488 : List Nat := [2, 1, 1, 2, 2, 1, 4, 7]
def baseStart_263488 : Nat := 118140960795 + 263488 * 2 ^ 59
def prefixEnd_263488 : Nat := 4983230072969 + 3 ^ 40 * 263488 * 2
def baseEnd_263488 : Nat := 40087700945768988352073

theorem tailTrace_263488 : CollatzResearch.WordTrace tailWord_263488 prefixEnd_263488 40087700945768988352073 := by
  unfold tailWord_263488
  simp only [CollatzResearch.WordTrace]
  refine ⟨4805098434717725506431559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6406797912956967341908745 4805098434717725506431559)
  ·
    refine ⟨7207647652076588259647339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4805098434717725506431559 7207647652076588259647339)
    ·
      refine ⟨10811471478114882389471009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7207647652076588259647339 10811471478114882389471009)
      ·
        refine ⟨8108603608586161792103257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10811471478114882389471009 8108603608586161792103257)
        ·
          refine ⟨6081452706439621344077443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8108603608586161792103257 6081452706439621344077443)
          ·
            refine ⟨9122179059659432016116165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6081452706439621344077443 9122179059659432016116165)
            ·
              refine ⟨1710408573686143503021781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9122179059659432016116165 1710408573686143503021781)
              ·
                refine ⟨40087700945768988352073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1710408573686143503021781 40087700945768988352073)
                ·
                  rfl

theorem cell20_263488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_263488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263488 prefixEnd_263488 := by exact prefixLift 263488
  have htrace : WordTrace (prefixWord ++ tailWord_263488) baseStart_263488 baseEnd_263488 := by
    simpa [prefixWord, tailWord_263488, baseEnd_263488] using wordTrace_append hprefix tailTrace_263488
  have hstable : (prefixWord ++ tailWord_263488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263488).length < 2 ^ (prefixWord ++ tailWord_263488).sum := by decide
  have hdescent : baseEnd_263488 < baseStart_263488 := by decide
  rcases family_descends (prefixWord ++ tailWord_263488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263501 : List Nat := [1, 6, 1, 3, 1, 1, 1, 6]
def baseStart_263501 : Nat := 118140960795 + 263501 * 2 ^ 59
def prefixEnd_263501 : Nat := 4983230072969 + 3 ^ 40 * 263501 * 2
def baseEnd_263501 : Nat := 40089678797178899207611

theorem tailTrace_263501 : CollatzResearch.WordTrace tailWord_263501 prefixEnd_263501 40089678797178899207611 := by
  unfold tailWord_263501
  simp only [CollatzResearch.WordTrace]
  refine ⟨9610671018388354233086357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6407114012258902822057571 9610671018388354233086357)
  ·
    refine ⟨450500203986954104675923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9610671018388354233086357 450500203986954104675923)
    ·
      refine ⟨675750305980431157013885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450500203986954104675923 675750305980431157013885)
      ·
        refine ⟨253406364742661683880207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 675750305980431157013885 253406364742661683880207)
        ·
          refine ⟨380109547113992525820311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 253406364742661683880207 380109547113992525820311)
          ·
            refine ⟨570164320670988788730467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380109547113992525820311 570164320670988788730467)
            ·
              refine ⟨855246481006483183095701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570164320670988788730467 855246481006483183095701)
              ·
                refine ⟨40089678797178899207611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 855246481006483183095701 40089678797178899207611)
                ·
                  rfl

theorem cell20_263501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 6].length) (baseStart_263501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263501 prefixEnd_263501 := by exact prefixLift 263501
  have htrace : WordTrace (prefixWord ++ tailWord_263501) baseStart_263501 baseEnd_263501 := by
    simpa [prefixWord, tailWord_263501, baseEnd_263501] using wordTrace_append hprefix tailTrace_263501
  have hstable : (prefixWord ++ tailWord_263501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263501).length < 2 ^ (prefixWord ++ tailWord_263501).sum := by decide
  have hdescent : baseEnd_263501 < baseStart_263501 := by decide
  rcases family_descends (prefixWord ++ tailWord_263501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263532 : List Nat := [2, 2, 1, 1, 5, 2, 3, 2, 2]
def baseStart_263532 : Nat := 118140960795 + 263532 * 2 ^ 59
def prefixEnd_263532 : Nat := 4983230072969 + 3 ^ 40 * 263532 * 2
def baseEnd_263532 : Nat := 120283185636238367589373

theorem tailTrace_263532 : CollatzResearch.WordTrace tailWord_263532 prefixEnd_263532 120283185636238367589373 := by
  unfold tailWord_263532
  simp only [CollatzResearch.WordTrace]
  refine ⟨4805900840638023263732425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6407867787517364351643233 4805900840638023263732425)
  ·
    refine ⟨3604425630478517447799319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4805900840638023263732425 3604425630478517447799319)
    ·
      refine ⟨5406638445717776171698979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3604425630478517447799319 5406638445717776171698979)
      ·
        refine ⟨8109957668576664257548469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5406638445717776171698979 8109957668576664257548469)
        ·
          refine ⟨760308531429062274145169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8109957668576664257548469 760308531429062274145169)
          ·
            refine ⟨570231398571796705608877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 760308531429062274145169 570231398571796705608877)
            ·
              refine ⟨213836774464423764603329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 570231398571796705608877 213836774464423764603329)
              ·
                refine ⟨160377580848317823452497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213836774464423764603329 160377580848317823452497)
                ·
                  refine ⟨120283185636238367589373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160377580848317823452497 120283185636238367589373)
                  ·
                    rfl

theorem cell20_263532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 2].length) (baseStart_263532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263532 prefixEnd_263532 := by exact prefixLift 263532
  have htrace : WordTrace (prefixWord ++ tailWord_263532) baseStart_263532 baseEnd_263532 := by
    simpa [prefixWord, tailWord_263532, baseEnd_263532] using wordTrace_append hprefix tailTrace_263532
  have hstable : (prefixWord ++ tailWord_263532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263532).length < 2 ^ (prefixWord ++ tailWord_263532).sum := by decide
  have hdescent : baseEnd_263532 < baseStart_263532 := by decide
  rcases family_descends (prefixWord ++ tailWord_263532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263557 : List Nat := [1, 3, 1, 1, 3, 1, 2, 4, 4]
def baseStart_263557 : Nat := 118140960795 + 263557 * 2 ^ 59
def prefixEnd_263557 : Nat := 4983230072969 + 3 ^ 40 * 263557 * 2
def baseEnd_263557 : Nat := 120294596317449391755937

theorem tailTrace_263557 : CollatzResearch.WordTrace tailWord_263557 prefixEnd_263557 120294596317449391755937 := by
  unfold tailWord_263557
  simp only [CollatzResearch.WordTrace]
  refine ⟨9612713506185475797124925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6408475670790317198083283 9612713506185475797124925)
  ·
    refine ⟨3604767564819553423921847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9612713506185475797124925 3604767564819553423921847)
    ·
      refine ⟨5407151347229330135882771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3604767564819553423921847 5407151347229330135882771)
      ·
        refine ⟨8110727020843995203824157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5407151347229330135882771 8110727020843995203824157)
        ·
          refine ⟨3041522632816498201434059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8110727020843995203824157 3041522632816498201434059)
          ·
            refine ⟨4562283949224747302151089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3041522632816498201434059 4562283949224747302151089)
            ·
              refine ⟨3421712961918560476613317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4562283949224747302151089 3421712961918560476613317)
              ·
                refine ⟨641571180359730089364997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3421712961918560476613317 641571180359730089364997)
                ·
                  refine ⟨120294596317449391755937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 641571180359730089364997 120294596317449391755937)
                  ·
                    rfl

theorem cell20_263557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_263557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263557 prefixEnd_263557 := by exact prefixLift 263557
  have htrace : WordTrace (prefixWord ++ tailWord_263557) baseStart_263557 baseEnd_263557 := by
    simpa [prefixWord, tailWord_263557, baseEnd_263557] using wordTrace_append hprefix tailTrace_263557
  have hstable : (prefixWord ++ tailWord_263557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263557).length < 2 ^ (prefixWord ++ tailWord_263557).sum := by decide
  have hdescent : baseEnd_263557 < baseStart_263557 := by decide
  rcases family_descends (prefixWord ++ tailWord_263557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263564 : List Nat := [2, 2, 1, 2, 1, 3, 1, 8]
def baseStart_263564 : Nat := 118140960795 + 263564 * 2 ^ 59
def prefixEnd_263564 : Nat := 4983230072969 + 3 ^ 40 * 263564 * 2
def baseEnd_263564 : Nat := 40099263769396159507525

theorem tailTrace_263564 : CollatzResearch.WordTrace tailWord_263564 prefixEnd_263564 40099263769396159507525 := by
  unfold tailWord_263564
  simp only [CollatzResearch.WordTrace]
  refine ⟨4806484408580057996314873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6408645878106743995086497 4806484408580057996314873)
  ·
    refine ⟨3604863306435043497236155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4806484408580057996314873 3604863306435043497236155)
    ·
      refine ⟨5407294959652565245854233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3604863306435043497236155 5407294959652565245854233)
      ·
        refine ⟨4055471219739423934390675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5407294959652565245854233 4055471219739423934390675)
        ·
          refine ⟨6083206829609135901586013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4055471219739423934390675 6083206829609135901586013)
          ·
            refine ⟨2281202561103425963094755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6083206829609135901586013 2281202561103425963094755)
            ·
              refine ⟨3421803841655138944642133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2281202561103425963094755 3421803841655138944642133)
              ·
                refine ⟨40099263769396159507525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3421803841655138944642133 40099263769396159507525)
                ·
                  rfl

theorem cell20_263564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_263564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263564 prefixEnd_263564 := by exact prefixLift 263564
  have htrace : WordTrace (prefixWord ++ tailWord_263564) baseStart_263564 baseEnd_263564 := by
    simpa [prefixWord, tailWord_263564, baseEnd_263564] using wordTrace_append hprefix tailTrace_263564
  have hstable : (prefixWord ++ tailWord_263564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263564).length < 2 ^ (prefixWord ++ tailWord_263564).sum := by decide
  have hdescent : baseEnd_263564 < baseStart_263564 := by decide
  rcases family_descends (prefixWord ++ tailWord_263564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263591 : List Nat := [1, 1, 6, 1, 1, 1, 3, 4, 2]
def baseStart_263591 : Nat := 118140960795 + 263591 * 2 ^ 59
def prefixEnd_263591 : Nat := 4983230072969 + 3 ^ 40 * 263591 * 2
def baseEnd_263591 : Nat := 120310114843896384622465

theorem tailTrace_263591 : CollatzResearch.WordTrace tailWord_263591 prefixEnd_263591 120310114843896384622465 := by
  unfold tailWord_263591
  simp only [CollatzResearch.WordTrace]
  refine ⟨9613953588062299603862627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6409302392041533069241751 9613953588062299603862627)
  ·
    refine ⟨14420930382093449405793941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9613953588062299603862627 14420930382093449405793941)
    ·
      refine ⟨675981111660630440896591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14420930382093449405793941 675981111660630440896591)
      ·
        refine ⟨1013971667490945661344887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 675981111660630440896591 1013971667490945661344887)
        ·
          refine ⟨1520957501236418492017331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1013971667490945661344887 1520957501236418492017331)
          ·
            refine ⟨2281436251854627738025997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1520957501236418492017331 2281436251854627738025997)
            ·
              refine ⟨855538594445485401759749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2281436251854627738025997 855538594445485401759749)
              ·
                refine ⟨160413486458528512829953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 855538594445485401759749 160413486458528512829953)
                ·
                  refine ⟨120310114843896384622465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160413486458528512829953 120310114843896384622465)
                  ·
                    rfl

theorem cell20_263591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 4, 2].length) (baseStart_263591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263591 prefixEnd_263591 := by exact prefixLift 263591
  have htrace : WordTrace (prefixWord ++ tailWord_263591) baseStart_263591 baseEnd_263591 := by
    simpa [prefixWord, tailWord_263591, baseEnd_263591] using wordTrace_append hprefix tailTrace_263591
  have hstable : (prefixWord ++ tailWord_263591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263591).length < 2 ^ (prefixWord ++ tailWord_263591).sum := by decide
  have hdescent : baseEnd_263591 < baseStart_263591 := by decide
  rcases family_descends (prefixWord ++ tailWord_263591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263602 : List Nat := [3, 2, 1, 1, 1, 1, 2, 9]
def baseStart_263602 : Nat := 118140960795 + 263602 * 2 ^ 59
def prefixEnd_263602 : Nat := 4983230072969 + 3 ^ 40 * 263602 * 2
def baseEnd_263602 : Nat := 40105045181209745085251

theorem tailTrace_263602 : CollatzResearch.WordTrace tailWord_263602 prefixEnd_263602 40105045181209745085251 := by
  unfold tailWord_263602
  simp only [CollatzResearch.WordTrace]
  refine ⟨2403588697755612120628265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6409569860681632321675373 2403588697755612120628265)
  ·
    refine ⟨1802691523316709090471199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2403588697755612120628265 1802691523316709090471199)
    ·
      refine ⟨2704037284975063635706799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1802691523316709090471199 2704037284975063635706799)
      ·
        refine ⟨4056055927462595453560199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2704037284975063635706799 4056055927462595453560199)
        ·
          refine ⟨6084083891193893180340299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4056055927462595453560199 6084083891193893180340299)
          ·
            refine ⟨9126125836790839770510449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6084083891193893180340299 9126125836790839770510449)
            ·
              refine ⟨6844594377593129827882837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9126125836790839770510449 6844594377593129827882837)
              ·
                refine ⟨40105045181209745085251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6844594377593129827882837 40105045181209745085251)
                ·
                  rfl

theorem cell20_263602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_263602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263602 prefixEnd_263602 := by exact prefixLift 263602
  have htrace : WordTrace (prefixWord ++ tailWord_263602) baseStart_263602 baseEnd_263602 := by
    simpa [prefixWord, tailWord_263602, baseEnd_263602] using wordTrace_append hprefix tailTrace_263602
  have hstable : (prefixWord ++ tailWord_263602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263602).length < 2 ^ (prefixWord ++ tailWord_263602).sum := by decide
  have hdescent : baseEnd_263602 < baseStart_263602 := by decide
  rcases family_descends (prefixWord ++ tailWord_263602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263605 : List Nat := [1, 3, 3, 2, 2, 1, 2, 3, 3]
def baseStart_263605 : Nat := 118140960795 + 263605 * 2 ^ 59
def prefixEnd_263605 : Nat := 4983230072969 + 3 ^ 40 * 263605 * 2
def baseEnd_263605 : Nat := 120316504825374558155741

theorem tailTrace_263605 : CollatzResearch.WordTrace tailWord_263605 prefixEnd_263605 120316504825374558155741 := by
  unfold tailWord_263605
  simp only [CollatzResearch.WordTrace]
  refine ⟨9614464210011579994872269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6409642806674386663248179 9614464210011579994872269)
  ·
    refine ⟨3605424078754342498077101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9614464210011579994872269 3605424078754342498077101)
    ·
      refine ⟨1352034029532878436778913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3605424078754342498077101 1352034029532878436778913)
      ·
        refine ⟨1014025522149658827584185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1352034029532878436778913 1014025522149658827584185)
        ·
          refine ⟨760519141612244120688139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1014025522149658827584185 760519141612244120688139)
          ·
            refine ⟨1140778712418366181032209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760519141612244120688139 1140778712418366181032209)
            ·
              refine ⟨855584034313774635774157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1140778712418366181032209 855584034313774635774157)
              ·
                refine ⟨320844012867665488415309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 855584034313774635774157 320844012867665488415309)
                ·
                  refine ⟨120316504825374558155741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320844012867665488415309 120316504825374558155741)
                  ·
                    rfl

theorem cell20_263605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_263605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263605 prefixEnd_263605 := by exact prefixLift 263605
  have htrace : WordTrace (prefixWord ++ tailWord_263605) baseStart_263605 baseEnd_263605 := by
    simpa [prefixWord, tailWord_263605, baseEnd_263605] using wordTrace_append hprefix tailTrace_263605
  have hstable : (prefixWord ++ tailWord_263605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263605).length < 2 ^ (prefixWord ++ tailWord_263605).sum := by decide
  have hdescent : baseEnd_263605 < baseStart_263605 := by decide
  rcases family_descends (prefixWord ++ tailWord_263605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263715 : List Nat := [1, 1, 1, 4, 6, 1, 2, 1, 3]
def baseStart_263715 : Nat := 118140960795 + 263715 * 2 ^ 59
def prefixEnd_263715 : Nat := 4983230072969 + 3 ^ 40 * 263715 * 2
def baseEnd_263715 : Nat := 120366711822703064488625

theorem tailTrace_263715 : CollatzResearch.WordTrace tailWord_263715 prefixEnd_263715 120366711822703064488625 := by
  unfold tailWord_263715
  simp only [CollatzResearch.WordTrace]
  refine ⟨9618476239613068781376599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6412317493075379187584399 9618476239613068781376599)
  ·
    refine ⟨14427714359419603172064899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9618476239613068781376599 14427714359419603172064899)
    ·
      refine ⟨21641571539129404758097349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14427714359419603172064899 21641571539129404758097349)
      ·
        refine ⟨4057794663586763392143253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21641571539129404758097349 4057794663586763392143253)
        ·
          refine ⟨190209124855629534006715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4057794663586763392143253 190209124855629534006715)
          ·
            refine ⟨285313687283444301010073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190209124855629534006715 285313687283444301010073)
            ·
              refine ⟨213985265462583225757555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 285313687283444301010073 213985265462583225757555)
              ·
                refine ⟨320977898193874838636333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 213985265462583225757555 320977898193874838636333)
                ·
                  refine ⟨120366711822703064488625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 320977898193874838636333 120366711822703064488625)
                  ·
                    rfl

theorem cell20_263715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 3].length) (baseStart_263715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263715 prefixEnd_263715 := by exact prefixLift 263715
  have htrace : WordTrace (prefixWord ++ tailWord_263715) baseStart_263715 baseEnd_263715 := by
    simpa [prefixWord, tailWord_263715, baseEnd_263715] using wordTrace_append hprefix tailTrace_263715
  have hstable : (prefixWord ++ tailWord_263715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263715).length < 2 ^ (prefixWord ++ tailWord_263715).sum := by decide
  have hdescent : baseEnd_263715 < baseStart_263715 := by decide
  rcases family_descends (prefixWord ++ tailWord_263715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263750 : List Nat := [6, 1, 1, 1, 3, 8]
def baseStart_263750 : Nat := 118140960795 + 263750 * 2 ^ 59
def prefixEnd_263750 : Nat := 4983230072969 + 3 ^ 40 * 263750 * 2
def baseEnd_263750 : Nat := 4458618028755499937845

theorem tailTrace_263750 : CollatzResearch.WordTrace tailWord_263750 prefixEnd_263750 4458618028755499937845 := by
  unfold tailWord_263750
  simp only [CollatzResearch.WordTrace]
  refine ⟨300617274827695929965647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6413168529657513172600469 300617274827695929965647)
  ·
    refine ⟨450925912241543894948471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 300617274827695929965647 450925912241543894948471)
    ·
      refine ⟨676388868362315842422707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 450925912241543894948471 676388868362315842422707)
      ·
        refine ⟨1014583302543473763634061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676388868362315842422707 1014583302543473763634061)
        ·
          refine ⟨380468738453802661362773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1014583302543473763634061 380468738453802661362773)
          ·
            refine ⟨4458618028755499937845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 380468738453802661362773 4458618028755499937845)
            ·
              rfl

theorem cell20_263750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 8].length) (baseStart_263750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263750 prefixEnd_263750 := by exact prefixLift 263750
  have htrace : WordTrace (prefixWord ++ tailWord_263750) baseStart_263750 baseEnd_263750 := by
    simpa [prefixWord, tailWord_263750, baseEnd_263750] using wordTrace_append hprefix tailTrace_263750
  have hstable : (prefixWord ++ tailWord_263750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263750).length < 2 ^ (prefixWord ++ tailWord_263750).sum := by decide
  have hdescent : baseEnd_263750 < baseStart_263750 := by decide
  rcases family_descends (prefixWord ++ tailWord_263750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263798 : List Nat := [5, 1, 1, 2, 2, 2, 2, 3, 2]
def baseStart_263798 : Nat := 118140960795 + 263798 * 2 ^ 59
def prefixEnd_263798 : Nat := 4983230072969 + 3 ^ 40 * 263798 * 2
def baseEnd_263798 : Nat := 120404595284323664721619

theorem tailTrace_263798 : CollatzResearch.WordTrace tailWord_263798 prefixEnd_263798 120404595284323664721619 := by
  unfold tailWord_263798
  simp only [CollatzResearch.WordTrace]
  refine ⟨601343968644523372290503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6414335665541582637765365 601343968644523372290503)
  ·
    refine ⟨902015952966785058435755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 601343968644523372290503 902015952966785058435755)
    ·
      refine ⟨1353023929450177587653633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 902015952966785058435755 1353023929450177587653633)
      ·
        refine ⟨1014767947087633190740225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1353023929450177587653633 1014767947087633190740225)
        ·
          refine ⟨761075960315724893055169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1014767947087633190740225 761075960315724893055169)
          ·
            refine ⟨570806970236793669791377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 761075960315724893055169 570806970236793669791377)
            ·
              refine ⟨428105227677595252343533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 570806970236793669791377 428105227677595252343533)
              ·
                refine ⟨160539460379098219628825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 428105227677595252343533 160539460379098219628825)
                ·
                  refine ⟨120404595284323664721619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160539460379098219628825 120404595284323664721619)
                  ·
                    rfl

theorem cell20_263798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 2].length) (baseStart_263798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263798 prefixEnd_263798 := by exact prefixLift 263798
  have htrace : WordTrace (prefixWord ++ tailWord_263798) baseStart_263798 baseEnd_263798 := by
    simpa [prefixWord, tailWord_263798, baseEnd_263798] using wordTrace_append hprefix tailTrace_263798
  have hstable : (prefixWord ++ tailWord_263798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263798).length < 2 ^ (prefixWord ++ tailWord_263798).sum := by decide
  have hdescent : baseEnd_263798 < baseStart_263798 := by decide
  rcases family_descends (prefixWord ++ tailWord_263798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263799 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 5]
def baseStart_263799 : Nat := 118140960795 + 263799 * 2 ^ 59
def prefixEnd_263799 : Nat := 4983230072969 + 3 ^ 40 * 263799 * 2
def baseEnd_263799 : Nat := 120405051711572105688281

theorem tailTrace_263799 : CollatzResearch.WordTrace tailWord_263799 prefixEnd_263799 120405051711572105688281 := by
  unfold tailWord_263799
  simp only [CollatzResearch.WordTrace]
  refine ⟨9621539971308751127434451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6414359980872500751622967 9621539971308751127434451)
  ·
    refine ⟨14432309956963126691151677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9621539971308751127434451 14432309956963126691151677)
    ·
      refine ⟨5412116233861172509181879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14432309956963126691151677 5412116233861172509181879)
      ·
        refine ⟨8118174350791758763772819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5412116233861172509181879 8118174350791758763772819)
        ·
          refine ⟨12177261526187638145659229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8118174350791758763772819 12177261526187638145659229)
          ·
            refine ⟨4566473072320364304622211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12177261526187638145659229 4566473072320364304622211)
            ·
              refine ⟨6849709608480546456933317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4566473072320364304622211 6849709608480546456933317)
              ·
                refine ⟨1284320551590102460674997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6849709608480546456933317 1284320551590102460674997)
                ·
                  refine ⟨120405051711572105688281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1284320551590102460674997 120405051711572105688281)
                  ·
                    rfl

theorem cell20_263799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_263799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263799 prefixEnd_263799 := by exact prefixLift 263799
  have htrace : WordTrace (prefixWord ++ tailWord_263799) baseStart_263799 baseEnd_263799 := by
    simpa [prefixWord, tailWord_263799, baseEnd_263799] using wordTrace_append hprefix tailTrace_263799
  have hstable : (prefixWord ++ tailWord_263799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263799).length < 2 ^ (prefixWord ++ tailWord_263799).sum := by decide
  have hdescent : baseEnd_263799 < baseStart_263799 := by decide
  rcases family_descends (prefixWord ++ tailWord_263799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263812 : List Nat := [2, 3, 2, 1, 4, 2, 1, 2, 3]
def baseStart_263812 : Nat := 118140960795 + 263812 * 2 ^ 59
def prefixEnd_263812 : Nat := 4983230072969 + 3 ^ 40 * 263812 * 2
def baseEnd_263812 : Nat := 120410985265801838254895

theorem tailTrace_263812 : CollatzResearch.WordTrace tailWord_263812 prefixEnd_263812 120410985265801838254895 := by
  unfold tailWord_263812
  simp only [CollatzResearch.WordTrace]
  refine ⟨4811007060130827173828845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6414676080174436231771793 4811007060130827173828845)
  ·
    refine ⟨1804127647549060190185817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4811007060130827173828845 1804127647549060190185817)
    ·
      refine ⟨1353095735661795142639363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1804127647549060190185817 1353095735661795142639363)
      ·
        refine ⟨2029643603492692713959045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1353095735661795142639363 2029643603492692713959045)
        ·
          refine ⟨380558175654879883867321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2029643603492692713959045 380558175654879883867321)
          ·
            refine ⟨285418631741159912900491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 380558175654879883867321 285418631741159912900491)
            ·
              refine ⟨428127947611739869350737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285418631741159912900491 428127947611739869350737)
              ·
                refine ⟨321095960708804902013053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428127947611739869350737 321095960708804902013053)
                ·
                  refine ⟨120410985265801838254895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321095960708804902013053 120410985265801838254895)
                  ·
                    rfl

theorem cell20_263812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_263812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263812 prefixEnd_263812 := by exact prefixLift 263812
  have htrace : WordTrace (prefixWord ++ tailWord_263812) baseStart_263812 baseEnd_263812 := by
    simpa [prefixWord, tailWord_263812, baseEnd_263812] using wordTrace_append hprefix tailTrace_263812
  have hstable : (prefixWord ++ tailWord_263812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263812).length < 2 ^ (prefixWord ++ tailWord_263812).sum := by decide
  have hdescent : baseEnd_263812 < baseStart_263812 := by decide
  rcases family_descends (prefixWord ++ tailWord_263812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263868 : List Nat := [2, 2, 2, 3, 1, 2, 8]
def baseStart_263868 : Nat := 118140960795 + 263868 * 2 ^ 59
def prefixEnd_263868 : Nat := 4983230072969 + 3 ^ 40 * 263868 * 2
def baseEnd_263868 : Nat := 13381838354634948043111

theorem tailTrace_263868 : CollatzResearch.WordTrace tailWord_263868 prefixEnd_263868 13381838354634948043111 := by
  unfold tailWord_263868
  simp only [CollatzResearch.WordTrace]
  refine ⟨4812028304029387955848129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6416037738705850607797505 4812028304029387955848129)
  ·
    refine ⟨3609021228022040966886097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4812028304029387955848129 3609021228022040966886097)
    ·
      refine ⟨2706765921016530725164573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3609021228022040966886097 2706765921016530725164573)
      ·
        refine ⟨1015037220381199021936715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2706765921016530725164573 1015037220381199021936715)
        ·
          refine ⟨1522555830571798532905073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1015037220381199021936715 1522555830571798532905073)
          ·
            refine ⟨1141916872928848899678805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1522555830571798532905073 1141916872928848899678805)
            ·
              refine ⟨13381838354634948043111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1141916872928848899678805 13381838354634948043111)
              ·
                rfl

theorem cell20_263868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 8].length) (baseStart_263868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263868 prefixEnd_263868 := by exact prefixLift 263868
  have htrace : WordTrace (prefixWord ++ tailWord_263868) baseStart_263868 baseEnd_263868 := by
    simpa [prefixWord, tailWord_263868, baseEnd_263868] using wordTrace_append hprefix tailTrace_263868
  have hstable : (prefixWord ++ tailWord_263868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263868).length < 2 ^ (prefixWord ++ tailWord_263868).sum := by decide
  have hdescent : baseEnd_263868 < baseStart_263868 := by decide
  rcases family_descends (prefixWord ++ tailWord_263868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263920 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 8]
def baseStart_263920 : Nat := 118140960795 + 263920 * 2 ^ 59
def prefixEnd_263920 : Nat := 4983230072969 + 3 ^ 40 * 263920 * 2
def baseEnd_263920 : Nat := 120460279408633462654453

theorem tailTrace_263920 : CollatzResearch.WordTrace tailWord_263920 prefixEnd_263920 120460279408633462654453 := by
  unfold tailWord_263920
  simp only [CollatzResearch.WordTrace]
  refine ⟨4812976601935194396294607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6417302135913592528392809 4812976601935194396294607)
  ·
    refine ⟨7219464902902791594441911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4812976601935194396294607 7219464902902791594441911)
    ·
      refine ⟨10829197354354187391662867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7219464902902791594441911 10829197354354187391662867)
      ·
        refine ⟨16243796031531281087494301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10829197354354187391662867 16243796031531281087494301)
        ·
          refine ⟨6091423511824230407810363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16243796031531281087494301 6091423511824230407810363)
          ·
            refine ⟨9137135267736345611715545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6091423511824230407810363 9137135267736345611715545)
            ·
              refine ⟨6852851450802259208786659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9137135267736345611715545 6852851450802259208786659)
              ·
                refine ⟨10279277176203388813179989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6852851450802259208786659 10279277176203388813179989)
                ·
                  refine ⟨120460279408633462654453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10279277176203388813179989 120460279408633462654453)
                  ·
                    rfl

theorem cell20_263920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_263920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263920 prefixEnd_263920 := by exact prefixLift 263920
  have htrace : WordTrace (prefixWord ++ tailWord_263920) baseStart_263920 baseEnd_263920 := by
    simpa [prefixWord, tailWord_263920, baseEnd_263920] using wordTrace_append hprefix tailTrace_263920
  have hstable : (prefixWord ++ tailWord_263920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263920).length < 2 ^ (prefixWord ++ tailWord_263920).sum := by decide
  have hdescent : baseEnd_263920 < baseStart_263920 := by decide
  rcases family_descends (prefixWord ++ tailWord_263920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263954 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 6]
def baseStart_263954 : Nat := 118140960795 + 263954 * 2 ^ 59
def prefixEnd_263954 : Nat := 4983230072969 + 3 ^ 40 * 263954 * 2
def baseEnd_263954 : Nat := 120475797935080455520981

theorem tailTrace_263954 : CollatzResearch.WordTrace tailWord_263954 prefixEnd_263954 120475797935080455520981 := by
  unfold tailWord_263954
  simp only [CollatzResearch.WordTrace]
  refine ⟨2406798321436803149831729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6418128857164808399551277 2406798321436803149831729)
  ·
    refine ⟨1805098741077602362373797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2406798321436803149831729 1805098741077602362373797)
    ·
      refine ⟨338456013952050442945087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1805098741077602362373797 338456013952050442945087)
      ·
        refine ⟨507684020928075664417631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338456013952050442945087 507684020928075664417631)
        ·
          refine ⟨761526031392113496626447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 507684020928075664417631 761526031392113496626447)
          ·
            refine ⟨1142289047088170244939671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761526031392113496626447 1142289047088170244939671)
            ·
              refine ⟨1713433570632255367409507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142289047088170244939671 1713433570632255367409507)
              ·
                refine ⟨2570150355948383051114261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1713433570632255367409507 2570150355948383051114261)
                ·
                  refine ⟨120475797935080455520981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2570150355948383051114261 120475797935080455520981)
                  ·
                    rfl

theorem cell20_263954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_263954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263954 prefixEnd_263954 := by exact prefixLift 263954
  have htrace : WordTrace (prefixWord ++ tailWord_263954) baseStart_263954 baseEnd_263954 := by
    simpa [prefixWord, tailWord_263954, baseEnd_263954] using wordTrace_append hprefix tailTrace_263954
  have hstable : (prefixWord ++ tailWord_263954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263954).length < 2 ^ (prefixWord ++ tailWord_263954).sum := by decide
  have hdescent : baseEnd_263954 < baseStart_263954 := by decide
  rcases family_descends (prefixWord ++ tailWord_263954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263985 : List Nat := [1, 2, 2, 3, 2, 4, 1, 2, 3]
def baseStart_263985 : Nat := 118140960795 + 263985 * 2 ^ 59
def prefixEnd_263985 : Nat := 4983230072969 + 3 ^ 40 * 263985 * 2
def baseEnd_263985 : Nat := 120489947179782125487521

theorem tailTrace_263985 : CollatzResearch.WordTrace tailWord_263985 prefixEnd_263985 120489947179782125487521 := by
  unfold tailWord_263985
  simp only [CollatzResearch.WordTrace]
  refine ⟨9628323948634904893705409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6418882632423269929136939 9628323948634904893705409)
  ·
    refine ⟨7221242961476178670279057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9628323948634904893705409 7221242961476178670279057)
    ·
      refine ⟨5415932221107134002709293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7221242961476178670279057 5415932221107134002709293)
      ·
        refine ⟨2030974582915175251015985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5415932221107134002709293 2030974582915175251015985)
        ·
          refine ⟨1523230937186381438261989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2030974582915175251015985 1523230937186381438261989)
          ·
            refine ⟨285605800722446519674123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1523230937186381438261989 285605800722446519674123)
            ·
              refine ⟨428408701083669779511185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285605800722446519674123 428408701083669779511185)
              ·
                refine ⟨321306525812752334633389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428408701083669779511185 321306525812752334633389)
                ·
                  refine ⟨120489947179782125487521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321306525812752334633389 120489947179782125487521)
                  ·
                    rfl

theorem cell20_263985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 2, 3].length) (baseStart_263985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263985 prefixEnd_263985 := by exact prefixLift 263985
  have htrace : WordTrace (prefixWord ++ tailWord_263985) baseStart_263985 baseEnd_263985 := by
    simpa [prefixWord, tailWord_263985, baseEnd_263985] using wordTrace_append hprefix tailTrace_263985
  have hstable : (prefixWord ++ tailWord_263985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263985).length < 2 ^ (prefixWord ++ tailWord_263985).sum := by decide
  have hdescent : baseEnd_263985 < baseStart_263985 := by decide
  rcases family_descends (prefixWord ++ tailWord_263985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_263992 : List Nat := [2, 1, 2, 1, 3, 3, 2, 4, 2]
def baseStart_263992 : Nat := 118140960795 + 263992 * 2 ^ 59
def prefixEnd_263992 : Nat := 4983230072969 + 3 ^ 40 * 263992 * 2
def baseEnd_263992 : Nat := 120493142170521212254159

theorem tailTrace_263992 : CollatzResearch.WordTrace tailWord_263992 prefixEnd_263992 120493142170521212254159 := by
  unfold tailWord_263992
  simp only [CollatzResearch.WordTrace]
  refine ⟨4814289629804772544605115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6419052839739696726140153 4814289629804772544605115)
  ·
    refine ⟨7221434444707158816907673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4814289629804772544605115 7221434444707158816907673)
    ·
      refine ⟨5416075833530369112680755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7221434444707158816907673 5416075833530369112680755)
      ·
        refine ⟨8124113750295553669021133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5416075833530369112680755 8124113750295553669021133)
        ·
          refine ⟨3046542656360832625882925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8124113750295553669021133 3046542656360832625882925)
          ·
            refine ⟨1142453496135312234706097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3046542656360832625882925 1142453496135312234706097)
            ·
              refine ⟨856840122101484176029573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1142453496135312234706097 856840122101484176029573)
              ·
                refine ⟨160657522894028283005545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 856840122101484176029573 160657522894028283005545)
                ·
                  refine ⟨120493142170521212254159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160657522894028283005545 120493142170521212254159)
                  ·
                    rfl

theorem cell20_263992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 2].length) (baseStart_263992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_263992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_263992 prefixEnd_263992 := by exact prefixLift 263992
  have htrace : WordTrace (prefixWord ++ tailWord_263992) baseStart_263992 baseEnd_263992 := by
    simpa [prefixWord, tailWord_263992, baseEnd_263992] using wordTrace_append hprefix tailTrace_263992
  have hstable : (prefixWord ++ tailWord_263992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_263992).length < 2 ^ (prefixWord ++ tailWord_263992).sum := by decide
  have hdescent : baseEnd_263992 < baseStart_263992 := by decide
  rcases family_descends (prefixWord ++ tailWord_263992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264054 : List Nat := [5, 1, 1, 3, 2, 1, 2, 5]
def baseStart_264054 : Nat := 118140960795 + 264054 * 2 ^ 59
def prefixEnd_264054 : Nat := 4983230072969 + 3 ^ 40 * 264054 * 2
def baseEnd_264054 : Nat := 40173813553308184062413

theorem tailTrace_264054 : CollatzResearch.WordTrace tailWord_264054 prefixEnd_264054 40173813553308184062413 := by
  unfold tailWord_264054
  simp only [CollatzResearch.WordTrace]
  refine ⟨601927536586558104872951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6420560390256619785311477 601927536586558104872951)
  ·
    refine ⟨902891304879837157309427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 601927536586558104872951 902891304879837157309427)
    ·
      refine ⟨1354336957319755735964141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 902891304879837157309427 1354336957319755735964141)
      ·
        refine ⟨507876358994908400986553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1354336957319755735964141 507876358994908400986553)
        ·
          refine ⟨380907269246181300739915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 507876358994908400986553 380907269246181300739915)
          ·
            refine ⟨571360903869271951109873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380907269246181300739915 571360903869271951109873)
            ·
              refine ⟨428520677901953963332405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571360903869271951109873 428520677901953963332405)
              ·
                refine ⟨40173813553308184062413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 428520677901953963332405 40173813553308184062413)
                ·
                  rfl

theorem cell20_264054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_264054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264054 prefixEnd_264054 := by exact prefixLift 264054
  have htrace : WordTrace (prefixWord ++ tailWord_264054) baseStart_264054 baseEnd_264054 := by
    simpa [prefixWord, tailWord_264054, baseEnd_264054] using wordTrace_append hprefix tailTrace_264054
  have hstable : (prefixWord ++ tailWord_264054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264054).length < 2 ^ (prefixWord ++ tailWord_264054).sum := by decide
  have hdescent : baseEnd_264054 < baseStart_264054 := by decide
  rcases family_descends (prefixWord ++ tailWord_264054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264113 : List Nat := [1, 2, 2, 4, 2, 3, 1, 5]
def baseStart_264113 : Nat := 118140960795 + 264113 * 2 ^ 59
def prefixEnd_264113 : Nat := 4983230072969 + 3 ^ 40 * 264113 * 2
def baseEnd_264113 : Nat := 40182789955860856406777

theorem tailTrace_264113 : CollatzResearch.WordTrace tailWord_264113 prefixEnd_264113 40182789955860856406777 := by
  unfold tailWord_264113
  simp only [CollatzResearch.WordTrace]
  refine ⟨9632992492171182754364993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6421994994780788502909995 9632992492171182754364993)
  ·
    refine ⟨7224744369128387065773745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9632992492171182754364993 7224744369128387065773745)
    ·
      refine ⟨5418558276846290299330309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7224744369128387065773745 5418558276846290299330309)
      ·
        refine ⟨1015979676908679431124433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5418558276846290299330309 1015979676908679431124433)
        ·
          refine ⟨761984757681509573343325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1015979676908679431124433 761984757681509573343325)
          ·
            refine ⟨285744284130566090003747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 761984757681509573343325 285744284130566090003747)
            ·
              refine ⟨428616426195849135005621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285744284130566090003747 428616426195849135005621)
              ·
                refine ⟨40182789955860856406777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 428616426195849135005621 40182789955860856406777)
                ·
                  rfl

theorem cell20_264113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 5].length) (baseStart_264113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264113 prefixEnd_264113 := by exact prefixLift 264113
  have htrace : WordTrace (prefixWord ++ tailWord_264113) baseStart_264113 baseEnd_264113 := by
    simpa [prefixWord, tailWord_264113, baseEnd_264113] using wordTrace_append hprefix tailTrace_264113
  have hstable : (prefixWord ++ tailWord_264113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264113).length < 2 ^ (prefixWord ++ tailWord_264113).sum := by decide
  have hdescent : baseEnd_264113 < baseStart_264113 := by decide
  rcases family_descends (prefixWord ++ tailWord_264113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264154 : List Nat := [3, 1, 1, 2, 6, 1, 1, 2, 3]
def baseStart_264154 : Nat := 118140960795 + 264154 * 2 ^ 59
def prefixEnd_264154 : Nat := 4983230072969 + 3 ^ 40 * 264154 * 2
def baseEnd_264154 : Nat := 120567083384768648853497

theorem tailTrace_264154 : CollatzResearch.WordTrace tailWord_264154 prefixEnd_264154 120567083384768648853497 := by
  unfold tailWord_264154
  simp only [CollatzResearch.WordTrace]
  refine ⟨2408621971255661689151879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6422991923348431171071677 2408621971255661689151879)
  ·
    refine ⟨3612932956883492533727819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2408621971255661689151879 3612932956883492533727819)
    ·
      refine ⟨5419399435325238800591729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3612932956883492533727819 5419399435325238800591729)
      ·
        refine ⟨4064549576493929100443797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5419399435325238800591729 4064549576493929100443797)
        ·
          refine ⟨190525761398152926583303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4064549576493929100443797 190525761398152926583303)
          ·
            refine ⟨285788642097229389874955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190525761398152926583303 285788642097229389874955)
            ·
              refine ⟨428682963145844084812433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285788642097229389874955 428682963145844084812433)
              ·
                refine ⟨321512222359383063609325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428682963145844084812433 321512222359383063609325)
                ·
                  refine ⟨120567083384768648853497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321512222359383063609325 120567083384768648853497)
                  ·
                    rfl

theorem cell20_264154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_264154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264154 prefixEnd_264154 := by exact prefixLift 264154
  have htrace : WordTrace (prefixWord ++ tailWord_264154) baseStart_264154 baseEnd_264154 := by
    simpa [prefixWord, tailWord_264154, baseEnd_264154] using wordTrace_append hprefix tailTrace_264154
  have hstable : (prefixWord ++ tailWord_264154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264154).length < 2 ^ (prefixWord ++ tailWord_264154).sum := by decide
  have hdescent : baseEnd_264154 < baseStart_264154 := by decide
  rcases family_descends (prefixWord ++ tailWord_264154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264179 : List Nat := [1, 1, 1, 2, 2, 2, 1, 7, 3]
def baseStart_264179 : Nat := 118140960795 + 264179 * 2 ^ 59
def prefixEnd_264179 : Nat := 4983230072969 + 3 ^ 40 * 264179 * 2
def baseEnd_264179 : Nat := 120578494065979673020061

theorem tailTrace_264179 : CollatzResearch.WordTrace tailWord_264179 prefixEnd_264179 120578494065979673020061 := by
  unfold tailWord_264179
  simp only [CollatzResearch.WordTrace]
  refine ⟨9635399709932076026267591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6423599806621384017511727 9635399709932076026267591)
  ·
    refine ⟨14453099564898114039401387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9635399709932076026267591 14453099564898114039401387)
    ·
      refine ⟨21679649347347171059102081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14453099564898114039401387 21679649347347171059102081)
      ·
        refine ⟨16259737010510378294326561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21679649347347171059102081 16259737010510378294326561)
        ·
          refine ⟨12194802757882783720744921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16259737010510378294326561 12194802757882783720744921)
          ·
            refine ⟨9146102068412087790558691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12194802757882783720744921 9146102068412087790558691)
            ·
              refine ⟨13719153102618131685838037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9146102068412087790558691 13719153102618131685838037)
              ·
                refine ⟨321542650842612461386829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 13719153102618131685838037 321542650842612461386829)
                ·
                  refine ⟨120578494065979673020061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321542650842612461386829 120578494065979673020061)
                  ·
                    rfl

theorem cell20_264179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 3].length) (baseStart_264179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264179 prefixEnd_264179 := by exact prefixLift 264179
  have htrace : WordTrace (prefixWord ++ tailWord_264179) baseStart_264179 baseEnd_264179 := by
    simpa [prefixWord, tailWord_264179, baseEnd_264179] using wordTrace_append hprefix tailTrace_264179
  have hstable : (prefixWord ++ tailWord_264179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264179).length < 2 ^ (prefixWord ++ tailWord_264179).sum := by decide
  have hdescent : baseEnd_264179 < baseStart_264179 := by decide
  rcases family_descends (prefixWord ++ tailWord_264179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264199 : List Nat := [1, 1, 4, 3, 1, 4, 1, 3, 2]
def baseStart_264199 : Nat := 118140960795 + 264199 * 2 ^ 59
def prefixEnd_264199 : Nat := 4983230072969 + 3 ^ 40 * 264199 * 2
def baseEnd_264199 : Nat := 120587622610948492353313

theorem tailTrace_264199 : CollatzResearch.WordTrace tailWord_264199 prefixEnd_264199 120587622610948492353313 := by
  unfold tailWord_264199
  simp only [CollatzResearch.WordTrace]
  refine ⟨9636129169859619441995651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6424086113239746294663767 9636129169859619441995651)
  ·
    refine ⟨14454193754789429162993477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9636129169859619441995651 14454193754789429162993477)
    ·
      refine ⟨2710161329023017968061277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14454193754789429162993477 2710161329023017968061277)
      ·
        refine ⟨1016310498383631738022979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2710161329023017968061277 1016310498383631738022979)
        ·
          refine ⟨1524465747575447607034469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1016310498383631738022979 1524465747575447607034469)
          ·
            refine ⟨285837327670396426318963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1524465747575447607034469 285837327670396426318963)
            ·
              refine ⟨428755991505594639478445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285837327670396426318963 428755991505594639478445)
              ·
                refine ⟨160783496814597989804417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 428755991505594639478445 160783496814597989804417)
                ·
                  refine ⟨120587622610948492353313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160783496814597989804417 120587622610948492353313)
                  ·
                    rfl

theorem cell20_264199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 3, 2].length) (baseStart_264199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264199 prefixEnd_264199 := by exact prefixLift 264199
  have htrace : WordTrace (prefixWord ++ tailWord_264199) baseStart_264199 baseEnd_264199 := by
    simpa [prefixWord, tailWord_264199, baseEnd_264199] using wordTrace_append hprefix tailTrace_264199
  have hstable : (prefixWord ++ tailWord_264199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264199).length < 2 ^ (prefixWord ++ tailWord_264199).sum := by decide
  have hdescent : baseEnd_264199 < baseStart_264199 := by decide
  rcases family_descends (prefixWord ++ tailWord_264199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264217 : List Nat := [1, 2, 1, 2, 1, 1, 3, 6, 3]
def baseStart_264217 : Nat := 118140960795 + 264217 * 2 ^ 59
def prefixEnd_264217 : Nat := 4983230072969 + 3 ^ 40 * 264217 * 2
def baseEnd_264217 : Nat := 120595838301420429753239

theorem tailTrace_264217 : CollatzResearch.WordTrace tailWord_264217 prefixEnd_264217 120595838301420429753239 := by
  unfold tailWord_264217
  simp only [CollatzResearch.WordTrace]
  refine ⟨9636785683794408516150905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6424523789196272344100603 9636785683794408516150905)
  ·
    refine ⟨7227589262845806387113179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9636785683794408516150905 7227589262845806387113179)
    ·
      refine ⟨10841383894268709580669769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7227589262845806387113179 10841383894268709580669769)
      ·
        refine ⟨8131037920701532185502327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10841383894268709580669769 8131037920701532185502327)
        ·
          refine ⟨12196556881052298278253491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8131037920701532185502327 12196556881052298278253491)
          ·
            refine ⟨18294835321578447417380237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12196556881052298278253491 18294835321578447417380237)
            ·
              refine ⟨6860563245591917781517589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18294835321578447417380237 6860563245591917781517589)
              ·
                refine ⟨321588902137121146008637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6860563245591917781517589 321588902137121146008637)
                ·
                  refine ⟨120595838301420429753239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 321588902137121146008637 120595838301420429753239)
                  ·
                    rfl

theorem cell20_264217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_264217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264217 prefixEnd_264217 := by exact prefixLift 264217
  have htrace : WordTrace (prefixWord ++ tailWord_264217) baseStart_264217 baseEnd_264217 := by
    simpa [prefixWord, tailWord_264217, baseEnd_264217] using wordTrace_append hprefix tailTrace_264217
  have hstable : (prefixWord ++ tailWord_264217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264217).length < 2 ^ (prefixWord ++ tailWord_264217).sum := by decide
  have hdescent : baseEnd_264217 < baseStart_264217 := by decide
  rcases family_descends (prefixWord ++ tailWord_264217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264220 : List Nat := [2, 2, 3, 1, 3, 3, 1, 1, 4]
def baseStart_264220 : Nat := 118140960795 + 264220 * 2 ^ 59
def prefixEnd_264220 : Nat := 4983230072969 + 3 ^ 40 * 264220 * 2
def baseEnd_264220 : Nat := 120597207583165752653227

theorem tailTrace_264220 : CollatzResearch.WordTrace tailWord_264220 prefixEnd_264220 120597207583165752653227 := by
  unfold tailWord_264220
  simp only [CollatzResearch.WordTrace]
  refine ⟨4818447551391770014255057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6424596735189026685673409 4818447551391770014255057)
  ·
    refine ⟨3613835663543827510691293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4818447551391770014255057 3613835663543827510691293)
    ·
      refine ⟨1355188373828935316509235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3613835663543827510691293 1355188373828935316509235)
      ·
        refine ⟨2032782560743402974763853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1355188373828935316509235 2032782560743402974763853)
        ·
          refine ⟨762293460278776115536445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2032782560743402974763853 762293460278776115536445)
          ·
            refine ⟨285860047604541043326167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 762293460278776115536445 285860047604541043326167)
            ·
              refine ⟨428790071406811564989251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285860047604541043326167 428790071406811564989251)
              ·
                refine ⟨643185107110217347483877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428790071406811564989251 643185107110217347483877)
                ·
                  refine ⟨120597207583165752653227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 643185107110217347483877 120597207583165752653227)
                  ·
                    rfl

theorem cell20_264220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_264220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264220 prefixEnd_264220 := by exact prefixLift 264220
  have htrace : WordTrace (prefixWord ++ tailWord_264220) baseStart_264220 baseEnd_264220 := by
    simpa [prefixWord, tailWord_264220, baseEnd_264220] using wordTrace_append hprefix tailTrace_264220
  have hstable : (prefixWord ++ tailWord_264220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264220).length < 2 ^ (prefixWord ++ tailWord_264220).sum := by decide
  have hdescent : baseEnd_264220 < baseStart_264220 := by decide
  rcases family_descends (prefixWord ++ tailWord_264220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264300 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 6]
def baseStart_264300 : Nat := 118140960795 + 264300 * 2 ^ 59
def prefixEnd_264300 : Nat := 4983230072969 + 3 ^ 40 * 264300 * 2
def baseEnd_264300 : Nat := 120633721763041029986233

theorem tailTrace_264300 : CollatzResearch.WordTrace tailWord_264300 prefixEnd_264300 120633721763041029986233 := by
  unfold tailWord_264300
  simp only [CollatzResearch.WordTrace]
  refine ⟨4819906471246856845711177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6426541961662475794281569 4819906471246856845711177)
  ·
    refine ⟨3614929853435142634283383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4819906471246856845711177 3614929853435142634283383)
    ·
      refine ⟨5422394780152713951425075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3614929853435142634283383 5422394780152713951425075)
      ·
        refine ⟨8133592170229070927137613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5422394780152713951425075 8133592170229070927137613)
        ·
          refine ⟨3050097063835901597676605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8133592170229070927137613 3050097063835901597676605)
          ·
            refine ⟨1143786398938463099128727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3050097063835901597676605 1143786398938463099128727)
            ·
              refine ⟨1715679598407694648693091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1143786398938463099128727 1715679598407694648693091)
              ·
                refine ⟨2573519397611541973039637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1715679598407694648693091 2573519397611541973039637)
                ·
                  refine ⟨120633721763041029986233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2573519397611541973039637 120633721763041029986233)
                  ·
                    rfl

theorem cell20_264300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_264300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264300 prefixEnd_264300 := by exact prefixLift 264300
  have htrace : WordTrace (prefixWord ++ tailWord_264300) baseStart_264300 baseEnd_264300 := by
    simpa [prefixWord, tailWord_264300, baseEnd_264300] using wordTrace_append hprefix tailTrace_264300
  have hstable : (prefixWord ++ tailWord_264300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264300).length < 2 ^ (prefixWord ++ tailWord_264300).sum := by decide
  have hdescent : baseEnd_264300 < baseStart_264300 := by decide
  rcases family_descends (prefixWord ++ tailWord_264300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264334 : List Nat := [4, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_264334 : Nat := 118140960795 + 264334 * 2 ^ 59
def prefixEnd_264334 : Nat := 4983230072969 + 3 ^ 40 * 264334 * 2
def baseEnd_264334 : Nat := 120649240289488022852761

theorem tailTrace_264334 : CollatzResearch.WordTrace tailWord_264334 prefixEnd_264334 120649240289488022852761 := by
  unfold tailWord_264334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1205131628046317187270007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6427368682913691665440037 1205131628046317187270007)
  ·
    refine ⟨1807697442069475780905011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1205131628046317187270007 1807697442069475780905011)
    ·
      refine ⟨2711546163104213671357517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1807697442069475780905011 2711546163104213671357517)
      ·
        refine ⟨1016829811164080126759069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2711546163104213671357517 1016829811164080126759069)
        ·
          refine ⟨381311179186530047534651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1016829811164080126759069 381311179186530047534651)
          ·
            refine ⟨571966768779795071301977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381311179186530047534651 571966768779795071301977)
            ·
              refine ⟨428975076584846303476483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571966768779795071301977 428975076584846303476483)
              ·
                refine ⟨643462614877269455214725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 428975076584846303476483 643462614877269455214725)
                ·
                  refine ⟨120649240289488022852761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 643462614877269455214725 120649240289488022852761)
                  ·
                    rfl

theorem cell20_264334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_264334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264334 prefixEnd_264334 := by exact prefixLift 264334
  have htrace : WordTrace (prefixWord ++ tailWord_264334) baseStart_264334 baseEnd_264334 := by
    simpa [prefixWord, tailWord_264334, baseEnd_264334] using wordTrace_append hprefix tailTrace_264334
  have hstable : (prefixWord ++ tailWord_264334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264334).length < 2 ^ (prefixWord ++ tailWord_264334).sum := by decide
  have hdescent : baseEnd_264334 < baseStart_264334 := by decide
  rcases family_descends (prefixWord ++ tailWord_264334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264448 : List Nat := [2, 1, 1, 2, 1, 1, 8, 2, 2]
def baseStart_264448 : Nat := 118140960795 + 264448 * 2 ^ 59
def prefixEnd_264448 : Nat := 4983230072969 + 3 ^ 40 * 264448 * 2
def baseEnd_264448 : Nat := 120701272995810293052295

theorem tailTrace_264448 : CollatzResearch.WordTrace tailWord_264448 prefixEnd_264448 120701272995810293052295 := by
  unfold tailWord_264448
  simp only [CollatzResearch.WordTrace]
  refine ⟨4822605472978767483904999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6430140630638356645206665 4822605472978767483904999)
  ·
    refine ⟨7233908209468151225857499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4822605472978767483904999 7233908209468151225857499)
    ·
      refine ⟨10850862314202226838786249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7233908209468151225857499 10850862314202226838786249)
      ·
        refine ⟨8138146735651670129089687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10850862314202226838786249 8138146735651670129089687)
        ·
          refine ⟨12207220103477505193634531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8138146735651670129089687 12207220103477505193634531)
          ·
            refine ⟨18310830155216257790451797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12207220103477505193634531 18310830155216257790451797)
            ·
              refine ⟨214580040881440520981857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 18310830155216257790451797 214580040881440520981857)
              ·
                refine ⟨160935030661080390736393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214580040881440520981857 160935030661080390736393)
                ·
                  refine ⟨120701272995810293052295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 160935030661080390736393 120701272995810293052295)
                  ·
                    rfl

theorem cell20_264448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 2].length) (baseStart_264448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264448 prefixEnd_264448 := by exact prefixLift 264448
  have htrace : WordTrace (prefixWord ++ tailWord_264448) baseStart_264448 baseEnd_264448 := by
    simpa [prefixWord, tailWord_264448, baseEnd_264448] using wordTrace_append hprefix tailTrace_264448
  have hstable : (prefixWord ++ tailWord_264448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264448).length < 2 ^ (prefixWord ++ tailWord_264448).sum := by decide
  have hdescent : baseEnd_264448 < baseStart_264448 := by decide
  rcases family_descends (prefixWord ++ tailWord_264448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264493 : List Nat := [1, 5, 3, 1, 2, 1, 7]
def baseStart_264493 : Nat := 118140960795 + 264493 * 2 ^ 59
def prefixEnd_264493 : Nat := 4983230072969 + 3 ^ 40 * 264493 * 2
def baseEnd_264493 : Nat := 13413534691332237394679

theorem tailTrace_264493 : CollatzResearch.WordTrace tailWord_264493 prefixEnd_264493 13413534691332237394679 := by
  unfold tailWord_264493
  simp only [CollatzResearch.WordTrace]
  refine ⟨9646852230794507653198133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6431234820529671768798755 9646852230794507653198133)
  ·
    refine ⟨904392396636985092487325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9646852230794507653198133 904392396636985092487325)
    ·
      refine ⟨339147148738869409682747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 904392396636985092487325 339147148738869409682747)
      ·
        refine ⟨508720723108304114524121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 339147148738869409682747 508720723108304114524121)
        ·
          refine ⟨381540542331228085893091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508720723108304114524121 381540542331228085893091)
          ·
            refine ⟨572310813496842128839637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381540542331228085893091 572310813496842128839637)
            ·
              refine ⟨13413534691332237394679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 572310813496842128839637 13413534691332237394679)
              ·
                rfl

theorem cell20_264493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 7].length) (baseStart_264493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264493 prefixEnd_264493 := by exact prefixLift 264493
  have htrace : WordTrace (prefixWord ++ tailWord_264493) baseStart_264493 baseEnd_264493 := by
    simpa [prefixWord, tailWord_264493, baseEnd_264493] using wordTrace_append hprefix tailTrace_264493
  have hstable : (prefixWord ++ tailWord_264493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264493).length < 2 ^ (prefixWord ++ tailWord_264493).sum := by decide
  have hdescent : baseEnd_264493 < baseStart_264493 := by decide
  rcases family_descends (prefixWord ++ tailWord_264493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264500 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 5]
def baseStart_264500 : Nat := 118140960795 + 264500 * 2 ^ 59
def prefixEnd_264500 : Nat := 4983230072969 + 3 ^ 40 * 264500 * 2
def baseEnd_264500 : Nat := 120725007212729223318749

theorem tailTrace_264500 : CollatzResearch.WordTrace tailWord_264500 prefixEnd_264500 120725007212729223318749 := by
  unfold tailWord_264500
  simp only [CollatzResearch.WordTrace]
  refine ⟨4823553770884573924351477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6431405027846098565801969 4823553770884573924351477)
  ·
    refine ⟨452208166020428805407951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4823553770884573924351477 452208166020428805407951)
    ·
      refine ⟨678312249030643208111927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452208166020428805407951 678312249030643208111927)
      ·
        refine ⟨1017468373545964812167891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 678312249030643208111927 1017468373545964812167891)
        ·
          refine ⟨1526202560318947218251837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1017468373545964812167891 1526202560318947218251837)
          ·
            refine ⟨572325960119605206844439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1526202560318947218251837 572325960119605206844439)
            ·
              refine ⟨858488940179407810266659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572325960119605206844439 858488940179407810266659)
              ·
                refine ⟨1287733410269111715399989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858488940179407810266659 1287733410269111715399989)
                ·
                  refine ⟨120725007212729223318749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1287733410269111715399989 120725007212729223318749)
                  ·
                    rfl

theorem cell20_264500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_264500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264500 prefixEnd_264500 := by exact prefixLift 264500
  have htrace : WordTrace (prefixWord ++ tailWord_264500) baseStart_264500 baseEnd_264500 := by
    simpa [prefixWord, tailWord_264500, baseEnd_264500] using wordTrace_append hprefix tailTrace_264500
  have hstable : (prefixWord ++ tailWord_264500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264500).length < 2 ^ (prefixWord ++ tailWord_264500).sum := by decide
  have hdescent : baseEnd_264500 < baseStart_264500 := by decide
  rcases family_descends (prefixWord ++ tailWord_264500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264528 : List Nat := [2, 1, 1, 1, 1, 6, 2, 2, 4]
def baseStart_264528 : Nat := 118140960795 + 264528 * 2 ^ 59
def prefixEnd_264528 : Nat := 4983230072969 + 3 ^ 40 * 264528 * 2
def baseEnd_264528 : Nat := 120737787175685570385301

theorem tailTrace_264528 : CollatzResearch.WordTrace tailWord_264528 prefixEnd_264528 120737787175685570385301 := by
  unfold tailWord_264528
  simp only [CollatzResearch.WordTrace]
  refine ⟨4824064392833854315361119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6432085857111805753814825 4824064392833854315361119)
  ·
    refine ⟨7236096589250781473041679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4824064392833854315361119 7236096589250781473041679)
    ·
      refine ⟨10854144883876172209562519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7236096589250781473041679 10854144883876172209562519)
      ·
        refine ⟨16281217325814258314343779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10854144883876172209562519 16281217325814258314343779)
        ·
          refine ⟨24421825988721387471515669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16281217325814258314343779 24421825988721387471515669)
          ·
            refine ⟨1144773093221315037727297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24421825988721387471515669 1144773093221315037727297)
            ·
              refine ⟨858579819915986278295473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1144773093221315037727297 858579819915986278295473)
              ·
                refine ⟨643934864936989708721605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 858579819915986278295473 643934864936989708721605)
                ·
                  refine ⟨120737787175685570385301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 643934864936989708721605 120737787175685570385301)
                  ·
                    rfl

theorem cell20_264528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_264528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264528 prefixEnd_264528 := by exact prefixLift 264528
  have htrace : WordTrace (prefixWord ++ tailWord_264528) baseStart_264528 baseEnd_264528 := by
    simpa [prefixWord, tailWord_264528, baseEnd_264528] using wordTrace_append hprefix tailTrace_264528
  have hstable : (prefixWord ++ tailWord_264528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264528).length < 2 ^ (prefixWord ++ tailWord_264528).sum := by decide
  have hdescent : baseEnd_264528 < baseStart_264528 := by decide
  rcases family_descends (prefixWord ++ tailWord_264528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264535 : List Nat := [1, 1, 3, 2, 3, 1, 3, 6]
def baseStart_264535 : Nat := 118140960795 + 264535 * 2 ^ 59
def prefixEnd_264535 : Nat := 4983230072969 + 3 ^ 40 * 264535 * 2
def baseEnd_264535 : Nat := 40246994055474885717313

theorem tailTrace_264535 : CollatzResearch.WordTrace tailWord_264535 prefixEnd_264535 40246994055474885717313 := by
  unfold tailWord_264535
  simp only [CollatzResearch.WordTrace]
  refine ⟨9648384096642348826227059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6432256064428232550818039 9648384096642348826227059)
  ·
    refine ⟨14472576144963523239340589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9648384096642348826227059 14472576144963523239340589)
    ·
      refine ⟨5427216054361321214752721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14472576144963523239340589 5427216054361321214752721)
      ·
        refine ⟨4070412040770990911064541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5427216054361321214752721 4070412040770990911064541)
        ·
          refine ⟨1526404515289121591649203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4070412040770990911064541 1526404515289121591649203)
          ·
            refine ⟨2289606772933682387473805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1526404515289121591649203 2289606772933682387473805)
            ·
              refine ⟨858602539850130895302677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2289606772933682387473805 858602539850130895302677)
              ·
                refine ⟨40246994055474885717313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 858602539850130895302677 40246994055474885717313)
                ·
                  rfl

theorem cell20_264535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 6].length) (baseStart_264535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264535 prefixEnd_264535 := by exact prefixLift 264535
  have htrace : WordTrace (prefixWord ++ tailWord_264535) baseStart_264535 baseEnd_264535 := by
    simpa [prefixWord, tailWord_264535, baseEnd_264535] using wordTrace_append hprefix tailTrace_264535
  have hstable : (prefixWord ++ tailWord_264535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264535).length < 2 ^ (prefixWord ++ tailWord_264535).sum := by decide
  have hdescent : baseEnd_264535 < baseStart_264535 := by decide
  rcases family_descends (prefixWord ++ tailWord_264535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264552 : List Nat := [2, 1, 4, 2, 2, 3, 6]
def baseStart_264552 : Nat := 118140960795 + 264552 * 2 ^ 59
def prefixEnd_264552 : Nat := 4983230072969 + 3 ^ 40 * 264552 * 2
def baseEnd_264552 : Nat := 13416526825516461509467

theorem tailTrace_264552 : CollatzResearch.WordTrace tailWord_264552 prefixEnd_264552 13416526825516461509467 := by
  unfold tailWord_264552
  simp only [CollatzResearch.WordTrace]
  refine ⟨4824502068790380364797955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6432669425053840486397273 4824502068790380364797955)
  ·
    refine ⟨7236753103185570547196933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4824502068790380364797955 7236753103185570547196933)
    ·
      refine ⟨1356891206847294477599425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7236753103185570547196933 1356891206847294477599425)
      ·
        refine ⟨1017668405135470858199569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1356891206847294477599425 1017668405135470858199569)
        ·
          refine ⟨763251303851603143649677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1017668405135470858199569 763251303851603143649677)
          ·
            refine ⟨286219238944351178868629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 763251303851603143649677 286219238944351178868629)
            ·
              refine ⟨13416526825516461509467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 286219238944351178868629 13416526825516461509467)
              ·
                rfl

theorem cell20_264552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 3, 6].length) (baseStart_264552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264552 prefixEnd_264552 := by exact prefixLift 264552
  have htrace : WordTrace (prefixWord ++ tailWord_264552) baseStart_264552 baseEnd_264552 := by
    simpa [prefixWord, tailWord_264552, baseEnd_264552] using wordTrace_append hprefix tailTrace_264552
  have hstable : (prefixWord ++ tailWord_264552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264552).length < 2 ^ (prefixWord ++ tailWord_264552).sum := by decide
  have hdescent : baseEnd_264552 < baseStart_264552 := by decide
  rcases family_descends (prefixWord ++ tailWord_264552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264573 : List Nat := [1, 4, 1, 1, 2, 3, 1, 7]
def baseStart_264573 : Nat := 118140960795 + 264573 * 2 ^ 59
def prefixEnd_264573 : Nat := 4983230072969 + 3 ^ 40 * 264573 * 2
def baseEnd_264573 : Nat := 40252775467288471295039

theorem tailTrace_264573 : CollatzResearch.WordTrace tailWord_264573 prefixEnd_264573 40252775467288471295039 := by
  unfold tailWord_264573
  simp only [CollatzResearch.WordTrace]
  refine ⟨9649770070504681316110373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6433180047003120877406915 9649770070504681316110373)
  ·
    refine ⟨1809331888219627746770695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9649770070504681316110373 1809331888219627746770695)
    ·
      refine ⟨2713997832329441620156043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1809331888219627746770695 2713997832329441620156043)
      ·
        refine ⟨4070996748494162430234065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2713997832329441620156043 4070996748494162430234065)
        ·
          refine ⟨3053247561370621822675549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4070996748494162430234065 3053247561370621822675549)
          ·
            refine ⟨1144967835513983183503331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3053247561370621822675549 1144967835513983183503331)
            ·
              refine ⟨1717451753270974775254997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1144967835513983183503331 1717451753270974775254997)
              ·
                refine ⟨40252775467288471295039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1717451753270974775254997 40252775467288471295039)
                ·
                  rfl

theorem cell20_264573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 7].length) (baseStart_264573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264573 prefixEnd_264573 := by exact prefixLift 264573
  have htrace : WordTrace (prefixWord ++ tailWord_264573) baseStart_264573 baseEnd_264573 := by
    simpa [prefixWord, tailWord_264573, baseEnd_264573] using wordTrace_append hprefix tailTrace_264573
  have hstable : (prefixWord ++ tailWord_264573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264573).length < 2 ^ (prefixWord ++ tailWord_264573).sum := by decide
  have hdescent : baseEnd_264573 < baseStart_264573 := by decide
  rcases family_descends (prefixWord ++ tailWord_264573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264590 : List Nat := [4, 1, 1, 4, 1, 1, 2, 6]
def baseStart_264590 : Nat := 118140960795 + 264590 * 2 ^ 59
def prefixEnd_264590 : Nat := 4983230072969 + 3 ^ 40 * 264590 * 2
def baseEnd_264590 : Nat := 40255361888362970106127

theorem tailTrace_264590 : CollatzResearch.WordTrace tailWord_264590 prefixEnd_264590 40255361888362970106127 := by
  unfold tailWord_264590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1206298763930386652434903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6433593407628728812986149 1206298763930386652434903)
  ·
    refine ⟨1809448145895579978652355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1206298763930386652434903 1809448145895579978652355)
    ·
      refine ⟨2714172218843369967978533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1809448145895579978652355 2714172218843369967978533)
      ·
        refine ⟨508907291033131868995975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2714172218843369967978533 508907291033131868995975)
        ·
          refine ⟨763360936549697803493963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508907291033131868995975 763360936549697803493963)
          ·
            refine ⟨1145041404824546705240945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 763360936549697803493963 1145041404824546705240945)
            ·
              refine ⟨858781053618410028930709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1145041404824546705240945 858781053618410028930709)
              ·
                refine ⟨40255361888362970106127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 858781053618410028930709 40255361888362970106127)
                ·
                  rfl

theorem cell20_264590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_264590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264590 prefixEnd_264590 := by exact prefixLift 264590
  have htrace : WordTrace (prefixWord ++ tailWord_264590) baseStart_264590 baseEnd_264590 := by
    simpa [prefixWord, tailWord_264590, baseEnd_264590] using wordTrace_append hprefix tailTrace_264590
  have hstable : (prefixWord ++ tailWord_264590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264590).length < 2 ^ (prefixWord ++ tailWord_264590).sum := by decide
  have hdescent : baseEnd_264590 < baseStart_264590 := by decide
  rcases family_descends (prefixWord ++ tailWord_264590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264641 : List Nat := [1, 2, 7, 1, 1, 1, 3, 4]
def baseStart_264641 : Nat := 118140960795 + 264641 * 2 ^ 59
def prefixEnd_264641 : Nat := 4983230072969 + 3 ^ 40 * 264641 * 2
def baseEnd_264641 : Nat := 40263121151586466539391

theorem tailTrace_264641 : CollatzResearch.WordTrace tailWord_264641 prefixEnd_264641 40263121151586466539391 := by
  unfold tailWord_264641
  simp only [CollatzResearch.WordTrace]
  refine ⟨9652250234258328929585777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6434833489505552619723851 9652250234258328929585777)
  ·
    refine ⟨7239187675693746697189333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9652250234258328929585777 7239187675693746697189333)
    ·
      refine ⟨169668461149072188215375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 7239187675693746697189333 169668461149072188215375)
      ·
        refine ⟨254502691723608282323063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169668461149072188215375 254502691723608282323063)
        ·
          refine ⟨381754037585412423484595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254502691723608282323063 381754037585412423484595)
          ·
            refine ⟨572631056378118635226893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381754037585412423484595 572631056378118635226893)
            ·
              refine ⟨214736646141794488210085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 572631056378118635226893 214736646141794488210085)
              ·
                refine ⟨40263121151586466539391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 214736646141794488210085 40263121151586466539391)
                ·
                  rfl

theorem cell20_264641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 4].length) (baseStart_264641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264641 prefixEnd_264641 := by exact prefixLift 264641
  have htrace : WordTrace (prefixWord ++ tailWord_264641) baseStart_264641 baseEnd_264641 := by
    simpa [prefixWord, tailWord_264641, baseEnd_264641] using wordTrace_append hprefix tailTrace_264641
  have hstable : (prefixWord ++ tailWord_264641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264641).length < 2 ^ (prefixWord ++ tailWord_264641).sum := by decide
  have hdescent : baseEnd_264641 < baseStart_264641 := by decide
  rcases family_descends (prefixWord ++ tailWord_264641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264680 : List Nat := [2, 1, 4, 1, 1, 3, 1, 3, 4]
def baseStart_264680 : Nat := 118140960795 + 264680 * 2 ^ 59
def prefixEnd_264680 : Nat := 4983230072969 + 3 ^ 40 * 264680 * 2
def baseEnd_264680 : Nat := 120807164117448597318013

theorem tailTrace_264680 : CollatzResearch.WordTrace tailWord_264680 prefixEnd_264680 120807164117448597318013 := by
  unfold tailWord_264680
  simp only [CollatzResearch.WordTrace]
  refine ⟨4826836340558519295127747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6435781787411359060170329 4826836340558519295127747)
  ·
    refine ⟨7240254510837778942691621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4826836340558519295127747 7240254510837778942691621)
    ·
      refine ⟨1357547720782083551754679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7240254510837778942691621 1357547720782083551754679)
      ·
        refine ⟨2036321581173125327632019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1357547720782083551754679 2036321581173125327632019)
        ·
          refine ⟨3054482371759687991448029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2036321581173125327632019 3054482371759687991448029)
          ·
            refine ⟨1145430889409882996793011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3054482371759687991448029 1145430889409882996793011)
            ·
              refine ⟨1718146334114824495189517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1145430889409882996793011 1718146334114824495189517)
              ·
                refine ⟨644304875293059185696069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1718146334114824495189517 644304875293059185696069)
                ·
                  refine ⟨120807164117448597318013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 644304875293059185696069 120807164117448597318013)
                  ·
                    rfl

theorem cell20_264680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_264680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264680 prefixEnd_264680 := by exact prefixLift 264680
  have htrace : WordTrace (prefixWord ++ tailWord_264680) baseStart_264680 baseEnd_264680 := by
    simpa [prefixWord, tailWord_264680, baseEnd_264680] using wordTrace_append hprefix tailTrace_264680
  have hstable : (prefixWord ++ tailWord_264680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264680).length < 2 ^ (prefixWord ++ tailWord_264680).sum := by decide
  have hdescent : baseEnd_264680 < baseStart_264680 := by decide
  rcases family_descends (prefixWord ++ tailWord_264680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264801 : List Nat := [1, 2, 3, 1, 1, 4, 3, 5]
def baseStart_264801 : Nat := 118140960795 + 264801 * 2 ^ 59
def prefixEnd_264801 : Nat := 4983230072969 + 3 ^ 40 * 264801 * 2
def baseEnd_264801 : Nat := 40287463938169984761395

theorem tailTrace_264801 : CollatzResearch.WordTrace tailWord_264801 prefixEnd_264801 40287463938169984761395 := by
  unfold tailWord_264801
  simp only [CollatzResearch.WordTrace]
  refine ⟨9658085913678676255410257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6438723942452450836940171 9658085913678676255410257)
  ·
    refine ⟨7243564435259007191557693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9658085913678676255410257 7243564435259007191557693)
    ·
      refine ⟨2716336663222127696834135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7243564435259007191557693 2716336663222127696834135)
      ·
        refine ⟨4074504994833191545251203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2716336663222127696834135 4074504994833191545251203)
        ·
          refine ⟨6111757492249787317876805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4074504994833191545251203 6111757492249787317876805)
          ·
            refine ⟨1145954529796835122101901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6111757492249787317876805 1145954529796835122101901)
            ·
              refine ⟨429732948673813170788213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1145954529796835122101901 429732948673813170788213)
              ·
                refine ⟨40287463938169984761395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 429732948673813170788213 40287463938169984761395)
                ·
                  rfl

theorem cell20_264801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 5].length) (baseStart_264801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264801 prefixEnd_264801 := by exact prefixLift 264801
  have htrace : WordTrace (prefixWord ++ tailWord_264801) baseStart_264801 baseEnd_264801 := by
    simpa [prefixWord, tailWord_264801, baseEnd_264801] using wordTrace_append hprefix tailTrace_264801
  have hstable : (prefixWord ++ tailWord_264801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264801).length < 2 ^ (prefixWord ++ tailWord_264801).sum := by decide
  have hdescent : baseEnd_264801 < baseStart_264801 := by decide
  rcases family_descends (prefixWord ++ tailWord_264801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264815 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 6]
def baseStart_264815 : Nat := 118140960795 + 264815 * 2 ^ 59
def prefixEnd_264815 : Nat := 4983230072969 + 3 ^ 40 * 264815 * 2
def baseEnd_264815 : Nat := 120868781795988127817461

theorem tailTrace_264815 : CollatzResearch.WordTrace tailWord_264815 prefixEnd_264815 120868781795988127817461 := by
  unfold tailWord_264815
  simp only [CollatzResearch.WordTrace]
  refine ⟨9658596535627956646419899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6439064357085304430946599 9658596535627956646419899)
  ·
    refine ⟨14487894803441934969629849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9658596535627956646419899 14487894803441934969629849)
    ·
      refine ⟨10865921102581451227222387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14487894803441934969629849 10865921102581451227222387)
      ·
        refine ⟨16298881653872176840833581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10865921102581451227222387 16298881653872176840833581)
        ·
          refine ⟨6112080620202066315312593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16298881653872176840833581 6112080620202066315312593)
          ·
            refine ⟨4584060465151549736484445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6112080620202066315312593 4584060465151549736484445)
            ·
              refine ⟨1719022674431831151181667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4584060465151549736484445 1719022674431831151181667)
              ·
                refine ⟨2578534011647746726772501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1719022674431831151181667 2578534011647746726772501)
                ·
                  refine ⟨120868781795988127817461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2578534011647746726772501 120868781795988127817461)
                  ·
                    rfl

theorem cell20_264815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_264815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264815 prefixEnd_264815 := by exact prefixLift 264815
  have htrace : WordTrace (prefixWord ++ tailWord_264815) baseStart_264815 baseEnd_264815 := by
    simpa [prefixWord, tailWord_264815, baseEnd_264815] using wordTrace_append hprefix tailTrace_264815
  have hstable : (prefixWord ++ tailWord_264815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264815).length < 2 ^ (prefixWord ++ tailWord_264815).sum := by decide
  have hdescent : baseEnd_264815 < baseStart_264815 := by decide
  rcases family_descends (prefixWord ++ tailWord_264815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264834 : List Nat := [3, 4, 3, 1, 2, 1, 1, 2, 3]
def baseStart_264834 : Nat := 118140960795 + 264834 * 2 ^ 59
def prefixEnd_264834 : Nat := 4983230072969 + 3 ^ 40 * 264834 * 2
def baseEnd_264834 : Nat := 120877453913708506184051

theorem tailTrace_264834 : CollatzResearch.WordTrace tailWord_264834 prefixEnd_264834 120877453913708506184051 := by
  unfold tailWord_264834
  simp only [CollatzResearch.WordTrace]
  refine ⟨2414822380639780722840389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6439526348372748594241037 2414822380639780722840389)
  ·
    refine ⟨452779196369958885532573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2414822380639780722840389 452779196369958885532573)
    ·
      refine ⟨169792198638734582074715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 452779196369958885532573 169792198638734582074715)
      ·
        refine ⟨254688297958101873112073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169792198638734582074715 254688297958101873112073)
        ·
          refine ⟨191016223468576404834055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 254688297958101873112073 191016223468576404834055)
          ·
            refine ⟨286524335202864607251083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191016223468576404834055 286524335202864607251083)
            ·
              refine ⟨429786502804296910876625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286524335202864607251083 429786502804296910876625)
              ·
                refine ⟨322339877103222683157469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 429786502804296910876625 322339877103222683157469)
                ·
                  refine ⟨120877453913708506184051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322339877103222683157469 120877453913708506184051)
                  ·
                    rfl

theorem cell20_264834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_264834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264834 prefixEnd_264834 := by exact prefixLift 264834
  have htrace : WordTrace (prefixWord ++ tailWord_264834) baseStart_264834 baseEnd_264834 := by
    simpa [prefixWord, tailWord_264834, baseEnd_264834] using wordTrace_append hprefix tailTrace_264834
  have hstable : (prefixWord ++ tailWord_264834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264834).length < 2 ^ (prefixWord ++ tailWord_264834).sum := by decide
  have hdescent : baseEnd_264834 < baseStart_264834 := by decide
  rcases family_descends (prefixWord ++ tailWord_264834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264904 : List Nat := [2, 1, 3, 1, 2, 4, 3, 2, 2]
def baseStart_264904 : Nat := 118140960795 + 264904 * 2 ^ 59
def prefixEnd_264904 : Nat := 4983230072969 + 3 ^ 40 * 264904 * 2
def baseEnd_264904 : Nat := 120909403821099373850431

theorem tailTrace_264904 : CollatzResearch.WordTrace tailWord_264904 prefixEnd_264904 120909403821099373850431 := by
  unfold tailWord_264904
  simp only [CollatzResearch.WordTrace]
  refine ⟨4830921316152762423204883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6441228421537016564273177 4830921316152762423204883)
  ·
    refine ⟨7246381974229143634807325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4830921316152762423204883 7246381974229143634807325)
    ·
      refine ⟨2717393240335928863052747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7246381974229143634807325 2717393240335928863052747)
      ·
        refine ⟨4076089860503893294579121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2717393240335928863052747 4076089860503893294579121)
        ·
          refine ⟨3057067395377919970934341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4076089860503893294579121 3057067395377919970934341)
          ·
            refine ⟨573200136633359994550189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3057067395377919970934341 573200136633359994550189)
            ·
              refine ⟨214950051237509997956321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 573200136633359994550189 214950051237509997956321)
              ·
                refine ⟨161212538428132498467241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214950051237509997956321 161212538428132498467241)
                ·
                  refine ⟨120909403821099373850431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161212538428132498467241 120909403821099373850431)
                  ·
                    rfl

theorem cell20_264904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 2].length) (baseStart_264904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264904 prefixEnd_264904 := by exact prefixLift 264904
  have htrace : WordTrace (prefixWord ++ tailWord_264904) baseStart_264904 baseEnd_264904 := by
    simpa [prefixWord, tailWord_264904, baseEnd_264904] using wordTrace_append hprefix tailTrace_264904
  have hstable : (prefixWord ++ tailWord_264904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264904).length < 2 ^ (prefixWord ++ tailWord_264904).sum := by decide
  have hdescent : baseEnd_264904 < baseStart_264904 := by decide
  rcases family_descends (prefixWord ++ tailWord_264904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264914 : List Nat := [3, 2, 2, 2, 4, 1, 2, 1, 3]
def baseStart_264914 : Nat := 118140960795 + 264914 * 2 ^ 59
def prefixEnd_264914 : Nat := 4983230072969 + 3 ^ 40 * 264914 * 2
def baseEnd_264914 : Nat := 120913968093583783517057

theorem tailTrace_264914 : CollatzResearch.WordTrace tailWord_264914 prefixEnd_264914 120913968093583783517057 := by
  unfold tailWord_264914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2415551840567324138568449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6441471574846197702849197 2415551840567324138568449)
  ·
    refine ⟨1811663880425493103926337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2415551840567324138568449 1811663880425493103926337)
    ·
      refine ⟨1358747910319119827944753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1811663880425493103926337 1358747910319119827944753)
      ·
        refine ⟨1019060932739339870958565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1358747910319119827944753 1019060932739339870958565)
        ·
          refine ⟨191073924888626225804731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1019060932739339870958565 191073924888626225804731)
          ·
            refine ⟨286610887332939338707097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191073924888626225804731 286610887332939338707097)
            ·
              refine ⟨214958165499704504030323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286610887332939338707097 214958165499704504030323)
              ·
                refine ⟨322437248249556756045485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 214958165499704504030323 322437248249556756045485)
                ·
                  refine ⟨120913968093583783517057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322437248249556756045485 120913968093583783517057)
                  ·
                    rfl

theorem cell20_264914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_264914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264914 prefixEnd_264914 := by exact prefixLift 264914
  have htrace : WordTrace (prefixWord ++ tailWord_264914) baseStart_264914 baseEnd_264914 := by
    simpa [prefixWord, tailWord_264914, baseEnd_264914] using wordTrace_append hprefix tailTrace_264914
  have hstable : (prefixWord ++ tailWord_264914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264914).length < 2 ^ (prefixWord ++ tailWord_264914).sum := by decide
  have hdescent : baseEnd_264914 < baseStart_264914 := by decide
  rcases family_descends (prefixWord ++ tailWord_264914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_264949 : List Nat := [1, 3, 6, 1, 1, 8]
def baseStart_264949 : Nat := 118140960795 + 264949 * 2 ^ 59
def prefixEnd_264949 : Nat := 4983230072969 + 3 ^ 40 * 264949 * 2
def baseEnd_264949 : Nat := 4478886779528859901861

theorem tailTrace_264949 : CollatzResearch.WordTrace tailWord_264949 prefixEnd_264949 4478886779528859901861 := by
  unfold tailWord_264949
  simp only [CollatzResearch.WordTrace]
  refine ⟨9663483917142497531797901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6442322611428331687865267 9663483917142497531797901)
  ·
    refine ⟨3623806468928436574424213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9663483917142497531797901 3623806468928436574424213)
    ·
      refine ⟨169865928231020464426135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3623806468928436574424213 169865928231020464426135)
      ·
        refine ⟨254798892346530696639203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 169865928231020464426135 254798892346530696639203)
        ·
          refine ⟨382198338519796044958805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254798892346530696639203 382198338519796044958805)
          ·
            refine ⟨4478886779528859901861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 382198338519796044958805 4478886779528859901861)
            ·
              rfl

theorem cell20_264949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 8].length) (baseStart_264949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_264949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_264949 prefixEnd_264949 := by exact prefixLift 264949
  have htrace : WordTrace (prefixWord ++ tailWord_264949) baseStart_264949 baseEnd_264949 := by
    simpa [prefixWord, tailWord_264949, baseEnd_264949] using wordTrace_append hprefix tailTrace_264949
  have hstable : (prefixWord ++ tailWord_264949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_264949).length < 2 ^ (prefixWord ++ tailWord_264949).sum := by decide
  have hdescent : baseEnd_264949 < baseStart_264949 := by decide
  rcases family_descends (prefixWord ++ tailWord_264949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265028 : List Nat := [2, 3, 4, 2, 1, 1, 3, 1, 3]
def baseStart_265028 : Nat := 118140960795 + 265028 * 2 ^ 59
def prefixEnd_265028 : Nat := 4983230072969 + 3 ^ 40 * 265028 * 2
def baseEnd_265028 : Nat := 120966000799906053716591

theorem tailTrace_265028 : CollatzResearch.WordTrace tailWord_265028 prefixEnd_265028 120966000799906053716591 := by
  unfold tailWord_265028
  simp only [CollatzResearch.WordTrace]
  refine ⟨4833182641928147011961869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6444243522570862682615825 4833182641928147011961869)
  ·
    refine ⟨1812443490723055129485701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4833182641928147011961869 1812443490723055129485701)
    ·
      refine ⟨339833154510572836778569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1812443490723055129485701 339833154510572836778569)
      ·
        refine ⟨254874865882929627583927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339833154510572836778569 254874865882929627583927)
        ·
          refine ⟨382312298824394441375891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254874865882929627583927 382312298824394441375891)
          ·
            refine ⟨573468448236591662063837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382312298824394441375891 573468448236591662063837)
            ·
              refine ⟨215050668088721873273939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 573468448236591662063837 215050668088721873273939)
              ·
                refine ⟨322576002133082809910909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215050668088721873273939 322576002133082809910909)
                ·
                  refine ⟨120966000799906053716591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322576002133082809910909 120966000799906053716591)
                  ·
                    rfl

theorem cell20_265028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_265028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265028 prefixEnd_265028 := by exact prefixLift 265028
  have htrace : WordTrace (prefixWord ++ tailWord_265028) baseStart_265028 baseEnd_265028 := by
    simpa [prefixWord, tailWord_265028, baseEnd_265028] using wordTrace_append hprefix tailTrace_265028
  have hstable : (prefixWord ++ tailWord_265028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265028).length < 2 ^ (prefixWord ++ tailWord_265028).sum := by decide
  have hdescent : baseEnd_265028 < baseStart_265028 := by decide
  rcases family_descends (prefixWord ++ tailWord_265028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265074 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_265074 : Nat := 118140960795 + 265074 * 2 ^ 59
def prefixEnd_265074 : Nat := 4983230072969 + 3 ^ 40 * 265074 * 2
def baseEnd_265074 : Nat := 120986996453334338183069

theorem tailTrace_265074 : CollatzResearch.WordTrace tailWord_265074 prefixEnd_265074 120986996453334338183069 := by
  unfold tailWord_265074
  simp only [CollatzResearch.WordTrace]
  refine ⟨2417010760422410970024569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6445362027793095920065517 2417010760422410970024569)
  ·
    refine ⟨1812758070316808227518427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2417010760422410970024569 1812758070316808227518427)
    ·
      refine ⟨2719137105475212341277641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1812758070316808227518427 2719137105475212341277641)
      ·
        refine ⟨2039352829106409255958231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2719137105475212341277641 2039352829106409255958231)
        ·
          refine ⟨3059029243659613883937347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2039352829106409255958231 3059029243659613883937347)
          ·
            refine ⟨4588543865489420825906021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3059029243659613883937347 4588543865489420825906021)
            ·
              refine ⟨860351974779266404857379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4588543865489420825906021 860351974779266404857379)
              ·
                refine ⟨1290527962168899607286069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 860351974779266404857379 1290527962168899607286069)
                ·
                  refine ⟨120986996453334338183069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1290527962168899607286069 120986996453334338183069)
                  ·
                    rfl

theorem cell20_265074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_265074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265074 prefixEnd_265074 := by exact prefixLift 265074
  have htrace : WordTrace (prefixWord ++ tailWord_265074) baseStart_265074 baseEnd_265074 := by
    simpa [prefixWord, tailWord_265074, baseEnd_265074] using wordTrace_append hprefix tailTrace_265074
  have hstable : (prefixWord ++ tailWord_265074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265074).length < 2 ^ (prefixWord ++ tailWord_265074).sum := by decide
  have hdescent : baseEnd_265074 < baseStart_265074 := by decide
  rcases family_descends (prefixWord ++ tailWord_265074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265077 : List Nat := [1, 3, 4, 1, 1, 4, 1, 1, 4]
def baseStart_265077 : Nat := 118140960795 + 265077 * 2 ^ 59
def prefixEnd_265077 : Nat := 4983230072969 + 3 ^ 40 * 265077 * 2
def baseEnd_265077 : Nat := 120988365735079661083057

theorem tailTrace_265077 : CollatzResearch.WordTrace tailWord_265077 prefixEnd_265077 120988365735079661083057 := by
  unfold tailWord_265077
  simp only [CollatzResearch.WordTrace]
  refine ⟨9668152460678775392457485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6445434973785850261638323 9668152460678775392457485)
  ·
    refine ⟨3625557172754540772171557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9668152460678775392457485 3625557172754540772171557)
    ·
      refine ⟨679791969891476394782167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3625557172754540772171557 679791969891476394782167)
      ·
        refine ⟨1019687954837214592173251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679791969891476394782167 1019687954837214592173251)
        ·
          refine ⟨1529531932255821888259877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1019687954837214592173251 1529531932255821888259877)
          ·
            refine ⟨286787237297966604048727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1529531932255821888259877 286787237297966604048727)
            ·
              refine ⟨430180855946949906073091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286787237297966604048727 430180855946949906073091)
              ·
                refine ⟨645271283920424859109637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430180855946949906073091 645271283920424859109637)
                ·
                  refine ⟨120988365735079661083057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 645271283920424859109637 120988365735079661083057)
                  ·
                    rfl

theorem cell20_265077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_265077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265077 prefixEnd_265077 := by exact prefixLift 265077
  have htrace : WordTrace (prefixWord ++ tailWord_265077) baseStart_265077 baseEnd_265077 := by
    simpa [prefixWord, tailWord_265077, baseEnd_265077] using wordTrace_append hprefix tailTrace_265077
  have hstable : (prefixWord ++ tailWord_265077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265077).length < 2 ^ (prefixWord ++ tailWord_265077).sum := by decide
  have hdescent : baseEnd_265077 < baseStart_265077 := by decide
  rcases family_descends (prefixWord ++ tailWord_265077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265160 : List Nat := [2, 1, 3, 1, 5, 1, 3, 4]
def baseStart_265160 : Nat := 118140960795 + 265160 * 2 ^ 59
def prefixEnd_265160 : Nat := 4983230072969 + 3 ^ 40 * 265160 * 2
def baseEnd_265160 : Nat := 40342083065566753772017

theorem tailTrace_265160 : CollatzResearch.WordTrace tailWord_265160 prefixEnd_265160 40342083065566753772017 := by
  unfold tailWord_265160
  simp only [CollatzResearch.WordTrace]
  refine ⟨4835589859689040283864467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6447453146252053711819289 4835589859689040283864467)
  ·
    refine ⟨7253384789533560425796701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4835589859689040283864467 7253384789533560425796701)
    ·
      refine ⟨2720019296075085159673763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7253384789533560425796701 2720019296075085159673763)
      ·
        refine ⟨4080028944112627739510645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2720019296075085159673763 4080028944112627739510645)
        ·
          refine ⟨382502713510558850579123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4080028944112627739510645 382502713510558850579123)
          ·
            refine ⟨573754070265838275868685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382502713510558850579123 573754070265838275868685)
            ·
              refine ⟨215157776349689353450757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 573754070265838275868685 215157776349689353450757)
              ·
                refine ⟨40342083065566753772017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215157776349689353450757 40342083065566753772017)
                ·
                  rfl

theorem cell20_265160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 4].length) (baseStart_265160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265160 prefixEnd_265160 := by exact prefixLift 265160
  have htrace : WordTrace (prefixWord ++ tailWord_265160) baseStart_265160 baseEnd_265160 := by
    simpa [prefixWord, tailWord_265160, baseEnd_265160] using wordTrace_append hprefix tailTrace_265160
  have hstable : (prefixWord ++ tailWord_265160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265160).length < 2 ^ (prefixWord ++ tailWord_265160).sum := by decide
  have hdescent : baseEnd_265160 < baseStart_265160 := by decide
  rcases family_descends (prefixWord ++ tailWord_265160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265170 : List Nat := [3, 2, 2, 3, 1, 2, 2, 3, 2]
def baseStart_265170 : Nat := 118140960795 + 265170 * 2 ^ 59
def prefixEnd_265170 : Nat := 4983230072969 + 3 ^ 40 * 265170 * 2
def baseEnd_265170 : Nat := 121030813469184670982677

theorem tailTrace_265170 : CollatzResearch.WordTrace tailWord_265170 prefixEnd_265170 121030813469184670982677 := by
  unfold tailWord_265170
  simp only [CollatzResearch.WordTrace]
  refine ⟨2417886112335463068898241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6447696299561234850395309 2417886112335463068898241)
  ·
    refine ⟨1813414584251597301673681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2417886112335463068898241 1813414584251597301673681)
    ·
      refine ⟨1360060938188697976255261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1813414584251597301673681 1360060938188697976255261)
      ·
        refine ⟨510022851820761741095723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1360060938188697976255261 510022851820761741095723)
        ·
          refine ⟨765034277731142611643585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510022851820761741095723 765034277731142611643585)
          ·
            refine ⟨573775708298356958732689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765034277731142611643585 573775708298356958732689)
            ·
              refine ⟨430331781223767719049517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573775708298356958732689 430331781223767719049517)
              ·
                refine ⟨161374417958912894643569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 430331781223767719049517 161374417958912894643569)
                ·
                  refine ⟨121030813469184670982677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161374417958912894643569 121030813469184670982677)
                  ·
                    rfl

theorem cell20_265170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 2].length) (baseStart_265170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265170 prefixEnd_265170 := by exact prefixLift 265170
  have htrace : WordTrace (prefixWord ++ tailWord_265170) baseStart_265170 baseEnd_265170 := by
    simpa [prefixWord, tailWord_265170, baseEnd_265170] using wordTrace_append hprefix tailTrace_265170
  have hstable : (prefixWord ++ tailWord_265170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265170).length < 2 ^ (prefixWord ++ tailWord_265170).sum := by decide
  have hdescent : baseEnd_265170 < baseStart_265170 := by decide
  rcases family_descends (prefixWord ++ tailWord_265170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265181 : List Nat := [1, 4, 3, 1, 2, 2, 7]
def baseStart_265181 : Nat := 118140960795 + 265181 * 2 ^ 59
def prefixEnd_265181 : Nat := 4983230072969 + 3 ^ 40 * 265181 * 2
def baseEnd_265181 : Nat := 13448426018768613512885

theorem tailTrace_265181 : CollatzResearch.WordTrace tailWord_265181 prefixEnd_265181 13448426018768613512885 := by
  unfold tailWord_265181
  simp only [CollatzResearch.WordTrace]
  refine ⟨9671945652302001154243397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6447963768201334102828931 9671945652302001154243397)
  ·
    refine ⟨1813489809806625216420637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9671945652302001154243397 1813489809806625216420637)
    ·
      refine ⟨680058678677484456157739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1813489809806625216420637 680058678677484456157739)
      ·
        refine ⟨1020088018016226684236609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680058678677484456157739 1020088018016226684236609)
        ·
          refine ⟨765066013512170013177457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1020088018016226684236609 765066013512170013177457)
          ·
            refine ⟨573799510134127509883093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765066013512170013177457 573799510134127509883093)
            ·
              refine ⟨13448426018768613512885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 573799510134127509883093 13448426018768613512885)
              ·
                rfl

theorem cell20_265181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 7].length) (baseStart_265181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265181 prefixEnd_265181 := by exact prefixLift 265181
  have htrace : WordTrace (prefixWord ++ tailWord_265181) baseStart_265181 baseEnd_265181 := by
    simpa [prefixWord, tailWord_265181, baseEnd_265181] using wordTrace_append hprefix tailTrace_265181
  have hstable : (prefixWord ++ tailWord_265181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265181).length < 2 ^ (prefixWord ++ tailWord_265181).sum := by decide
  have hdescent : baseEnd_265181 < baseStart_265181 := by decide
  rcases family_descends (prefixWord ++ tailWord_265181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265188 : List Nat := [2, 3, 1, 1, 1, 1, 2, 6, 3]
def baseStart_265188 : Nat := 118140960795 + 265188 * 2 ^ 59
def prefixEnd_265188 : Nat := 4983230072969 + 3 ^ 40 * 265188 * 2
def baseEnd_265188 : Nat := 121039029159656608382603

theorem tailTrace_265188 : CollatzResearch.WordTrace tailWord_265188 prefixEnd_265188 121039029159656608382603 := by
  unfold tailWord_265188
  simp only [CollatzResearch.WordTrace]
  refine ⟨4836100481638320674874109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6448133975517760899832145 4836100481638320674874109)
  ·
    refine ⟨1813537680614370253077791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4836100481638320674874109 1813537680614370253077791)
    ·
      refine ⟨2720306520921555379616687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1813537680614370253077791 2720306520921555379616687)
      ·
        refine ⟨4080459781382333069425031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2720306520921555379616687 4080459781382333069425031)
        ·
          refine ⟨6120689672073499604137547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4080459781382333069425031 6120689672073499604137547)
          ·
            refine ⟨9181034508110249406206321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6120689672073499604137547 9181034508110249406206321)
            ·
              refine ⟨6885775881082687054654741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9181034508110249406206321 6885775881082687054654741)
              ·
                refine ⟨322770744425750955686941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6885775881082687054654741 322770744425750955686941)
                ·
                  refine ⟨121039029159656608382603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322770744425750955686941 121039029159656608382603)
                  ·
                    rfl

theorem cell20_265188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_265188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265188 prefixEnd_265188 := by exact prefixLift 265188
  have htrace : WordTrace (prefixWord ++ tailWord_265188) baseStart_265188 baseEnd_265188 := by
    simpa [prefixWord, tailWord_265188, baseEnd_265188] using wordTrace_append hprefix tailTrace_265188
  have hstable : (prefixWord ++ tailWord_265188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265188).length < 2 ^ (prefixWord ++ tailWord_265188).sum := by decide
  have hdescent : baseEnd_265188 < baseStart_265188 := by decide
  rcases family_descends (prefixWord ++ tailWord_265188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265191 : List Nat := [1, 1, 5, 2, 2, 1, 2, 4, 2]
def baseStart_265191 : Nat := 118140960795 + 265191 * 2 ^ 59
def prefixEnd_265191 : Nat := 4983230072969 + 3 ^ 40 * 265191 * 2
def baseEnd_265191 : Nat := 121040398441401931282591

theorem tailTrace_265191 : CollatzResearch.WordTrace tailWord_265191 prefixEnd_265191 121040398441401931282591 := by
  unfold tailWord_265191
  simp only [CollatzResearch.WordTrace]
  refine ⟨9672310382265772862107427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6448206921510515241404951 9672310382265772862107427)
  ·
    refine ⟨14508465573398659293161141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9672310382265772862107427 14508465573398659293161141)
    ·
      refine ⟨1360168647506124308733857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14508465573398659293161141 1360168647506124308733857)
      ·
        refine ⟨1020126485629593231550393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1360168647506124308733857 1020126485629593231550393)
        ·
          refine ⟨765094864222194923662795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1020126485629593231550393 765094864222194923662795)
          ·
            refine ⟨1147642296333292385494193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765094864222194923662795 1147642296333292385494193)
            ·
              refine ⟨860731722249969289120645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1147642296333292385494193 860731722249969289120645)
              ·
                refine ⟨161387197921869241710121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 860731722249969289120645 161387197921869241710121)
                ·
                  refine ⟨121040398441401931282591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161387197921869241710121 121040398441401931282591)
                  ·
                    rfl

theorem cell20_265191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 2].length) (baseStart_265191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265191 prefixEnd_265191 := by exact prefixLift 265191
  have htrace : WordTrace (prefixWord ++ tailWord_265191) baseStart_265191 baseEnd_265191 := by
    simpa [prefixWord, tailWord_265191, baseEnd_265191] using wordTrace_append hprefix tailTrace_265191
  have hstable : (prefixWord ++ tailWord_265191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265191).length < 2 ^ (prefixWord ++ tailWord_265191).sum := by decide
  have hdescent : baseEnd_265191 < baseStart_265191 := by decide
  rcases family_descends (prefixWord ++ tailWord_265191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265226 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_265226 : Nat := 118140960795 + 265226 * 2 ^ 59
def prefixEnd_265226 : Nat := 4983230072969 + 3 ^ 40 * 265226 * 2
def baseEnd_265226 : Nat := 121056373395097365115781

theorem tailTrace_265226 : CollatzResearch.WordTrace tailWord_265226 prefixEnd_265226 121056373395097365115781 := by
  unfold tailWord_265226
  simp only [CollatzResearch.WordTrace]
  refine ⟨2418396734284743459907883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6449057958092649226421021 2418396734284743459907883)
  ·
    refine ⟨3627595101427115189861825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2418396734284743459907883 3627595101427115189861825)
    ·
      refine ⟨2720696326070336392396369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3627595101427115189861825 2720696326070336392396369)
      ·
        refine ⟨2040522244552752294297277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2720696326070336392396369 2040522244552752294297277)
        ·
          refine ⟨765195841707282110361479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2040522244552752294297277 765195841707282110361479)
          ·
            refine ⟨1147793762560923165542219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765195841707282110361479 1147793762560923165542219)
            ·
              refine ⟨1721690643841384748313329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1147793762560923165542219 1721690643841384748313329)
              ·
                refine ⟨1291267982881038561234997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1721690643841384748313329 1291267982881038561234997)
                ·
                  refine ⟨121056373395097365115781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1291267982881038561234997 121056373395097365115781)
                  ·
                    rfl

theorem cell20_265226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_265226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265226 prefixEnd_265226 := by exact prefixLift 265226
  have htrace : WordTrace (prefixWord ++ tailWord_265226) baseStart_265226 baseEnd_265226 := by
    simpa [prefixWord, tailWord_265226, baseEnd_265226] using wordTrace_append hprefix tailTrace_265226
  have hstable : (prefixWord ++ tailWord_265226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265226).length < 2 ^ (prefixWord ++ tailWord_265226).sum := by decide
  have hdescent : baseEnd_265226 < baseStart_265226 := by decide
  rcases family_descends (prefixWord ++ tailWord_265226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265240 : List Nat := [2, 1, 2, 3, 2, 2, 8]
def baseStart_265240 : Nat := 118140960795 + 265240 * 2 ^ 59
def prefixEnd_265240 : Nat := 4983230072969 + 3 ^ 40 * 265240 * 2
def baseEnd_265240 : Nat := 13451418152952837627673

theorem tailTrace_265240 : CollatzResearch.WordTrace tailWord_265240 prefixEnd_265240 13451418152952837627673 := by
  unfold tailWord_265240
  simp only [CollatzResearch.WordTrace]
  refine ⟨4837048779544127115320587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6449398372725502820427449 4837048779544127115320587)
  ·
    refine ⟨7255573169316190672980881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4837048779544127115320587 7255573169316190672980881)
    ·
      refine ⟨5441679876987143004735661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7255573169316190672980881 5441679876987143004735661)
      ·
        refine ⟨2040629953870178626775873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5441679876987143004735661 2040629953870178626775873)
        ·
          refine ⟨1530472465402633970081905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2040629953870178626775873 1530472465402633970081905)
          ·
            refine ⟨1147854349051975477561429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1530472465402633970081905 1147854349051975477561429)
            ·
              refine ⟨13451418152952837627673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1147854349051975477561429 13451418152952837627673)
              ·
                rfl

theorem cell20_265240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 8].length) (baseStart_265240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265240 prefixEnd_265240 := by exact prefixLift 265240
  have htrace : WordTrace (prefixWord ++ tailWord_265240) baseStart_265240 baseEnd_265240 := by
    simpa [prefixWord, tailWord_265240, baseEnd_265240] using wordTrace_append hprefix tailTrace_265240
  have hstable : (prefixWord ++ tailWord_265240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265240).length < 2 ^ (prefixWord ++ tailWord_265240).sum := by decide
  have hdescent : baseEnd_265240 < baseStart_265240 := by decide
  rcases family_descends (prefixWord ++ tailWord_265240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265250 : List Nat := [3, 3, 1, 1, 1, 3, 3, 1, 4]
def baseStart_265250 : Nat := 118140960795 + 265250 * 2 ^ 59
def prefixEnd_265250 : Nat := 4983230072969 + 3 ^ 40 * 265250 * 2
def baseEnd_265250 : Nat := 121067327649059948315683

theorem tailTrace_265250 : CollatzResearch.WordTrace tailWord_265250 prefixEnd_265250 121067327649059948315683 := by
  unfold tailWord_265250
  simp only [CollatzResearch.WordTrace]
  refine ⟨2418615572263006484626301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6449641526034683959003469 2418615572263006484626301)
  ·
    refine ⟨906980839598627431734863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2418615572263006484626301 906980839598627431734863)
    ·
      refine ⟨1360471259397941147602295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 906980839598627431734863 1360471259397941147602295)
      ·
        refine ⟨2040706889096911721403443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1360471259397941147602295 2040706889096911721403443)
        ·
          refine ⟨3061060333645367582105165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2040706889096911721403443 3061060333645367582105165)
          ·
            refine ⟨1147897625117012843289437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3061060333645367582105165 1147897625117012843289437)
            ·
              refine ⟨430461609418879816233539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1147897625117012843289437 430461609418879816233539)
              ·
                refine ⟨645692414128319724350309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430461609418879816233539 645692414128319724350309)
                ·
                  refine ⟨121067327649059948315683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 645692414128319724350309 121067327649059948315683)
                  ·
                    rfl

theorem cell20_265250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_265250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265250 prefixEnd_265250 := by exact prefixLift 265250
  have htrace : WordTrace (prefixWord ++ tailWord_265250) baseStart_265250 baseEnd_265250 := by
    simpa [prefixWord, tailWord_265250, baseEnd_265250] using wordTrace_append hprefix tailTrace_265250
  have hstable : (prefixWord ++ tailWord_265250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265250).length < 2 ^ (prefixWord ++ tailWord_265250).sum := by decide
  have hdescent : baseEnd_265250 < baseStart_265250 := by decide
  rcases family_descends (prefixWord ++ tailWord_265250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265264 : List Nat := [2, 1, 1, 1, 2, 4, 3, 3, 3]
def baseStart_265264 : Nat := 118140960795 + 265264 * 2 ^ 59
def prefixEnd_265264 : Nat := 4983230072969 + 3 ^ 40 * 265264 * 2
def baseEnd_265264 : Nat := 121073717630538121848959

theorem tailTrace_265264 : CollatzResearch.WordTrace tailWord_265264 prefixEnd_265264 121073717630538121848959 := by
  unfold tailWord_265264
  simp only [CollatzResearch.WordTrace]
  refine ⟨4837486455500653164757423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6449981940667537553009897 4837486455500653164757423)
  ·
    refine ⟨7256229683250979747136135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4837486455500653164757423 7256229683250979747136135)
    ·
      refine ⟨10884344524876469620704203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7256229683250979747136135 10884344524876469620704203)
      ·
        refine ⟨16326516787314704431056305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10884344524876469620704203 16326516787314704431056305)
        ·
          refine ⟨12244887590486028323292229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16326516787314704431056305 12244887590486028323292229)
          ·
            refine ⟨2295916423216130310617293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12244887590486028323292229 2295916423216130310617293)
            ·
              refine ⟨860968658706048866481485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2295916423216130310617293 860968658706048866481485)
              ·
                refine ⟨322863247014768324930557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 860968658706048866481485 322863247014768324930557)
                ·
                  refine ⟨121073717630538121848959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322863247014768324930557 121073717630538121848959)
                  ·
                    rfl

theorem cell20_265264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_265264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265264 prefixEnd_265264 := by exact prefixLift 265264
  have htrace : WordTrace (prefixWord ++ tailWord_265264) baseStart_265264 baseEnd_265264 := by
    simpa [prefixWord, tailWord_265264, baseEnd_265264] using wordTrace_append hprefix tailTrace_265264
  have hstable : (prefixWord ++ tailWord_265264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265264).length < 2 ^ (prefixWord ++ tailWord_265264).sum := by decide
  have hdescent : baseEnd_265264 < baseStart_265264 := by decide
  rcases family_descends (prefixWord ++ tailWord_265264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265285 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 7]
def baseStart_265285 : Nat := 118140960795 + 265285 * 2 ^ 59
def prefixEnd_265285 : Nat := 4983230072969 + 3 ^ 40 * 265285 * 2
def baseEnd_265285 : Nat := 121083302602755382148873

theorem tailTrace_265285 : CollatzResearch.WordTrace tailWord_265285 prefixEnd_265285 121083302602755382148873 := by
  unfold tailWord_265285
  simp only [CollatzResearch.WordTrace]
  refine ⟨9675738843925226916029309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6450492562616817944019539 9675738843925226916029309)
  ·
    refine ⟨3628402066471960093510991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9675738843925226916029309 3628402066471960093510991)
    ·
      refine ⟨5442603099707940140266487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3628402066471960093510991 5442603099707940140266487)
      ·
        refine ⟨8163904649561910210399731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5442603099707940140266487 8163904649561910210399731)
        ·
          refine ⟨12245856974342865315599597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8163904649561910210399731 12245856974342865315599597)
          ·
            refine ⟨4592196365378574493349849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12245856974342865315599597 4592196365378574493349849)
            ·
              refine ⟨3444147274033930870012387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4592196365378574493349849 3444147274033930870012387)
              ·
                refine ⟨5166220911050896305018581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3444147274033930870012387 5166220911050896305018581)
                ·
                  refine ⟨121083302602755382148873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5166220911050896305018581 121083302602755382148873)
                  ·
                    rfl

theorem cell20_265285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_265285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265285 prefixEnd_265285 := by exact prefixLift 265285
  have htrace : WordTrace (prefixWord ++ tailWord_265285) baseStart_265285 baseEnd_265285 := by
    simpa [prefixWord, tailWord_265285, baseEnd_265285] using wordTrace_append hprefix tailTrace_265285
  have hstable : (prefixWord ++ tailWord_265285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265285).length < 2 ^ (prefixWord ++ tailWord_265285).sum := by decide
  have hdescent : baseEnd_265285 < baseStart_265285 := by decide
  rcases family_descends (prefixWord ++ tailWord_265285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265288 : List Nat := [2, 1, 3, 1, 1, 1, 4, 5, 2]
def baseStart_265288 : Nat := 118140960795 + 265288 * 2 ^ 59
def prefixEnd_265288 : Nat := 4983230072969 + 3 ^ 40 * 265288 * 2
def baseEnd_265288 : Nat := 121084671884500705048861

theorem tailTrace_265288 : CollatzResearch.WordTrace tailWord_265288 prefixEnd_265288 121084671884500705048861 := by
  unfold tailWord_265288
  simp only [CollatzResearch.WordTrace]
  refine ⟨4837924131457179214194259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6450565508609572285592345 4837924131457179214194259)
  ·
    refine ⟨7256886197185768821291389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4837924131457179214194259 7256886197185768821291389)
    ·
      refine ⟨2721332323944663307984271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7256886197185768821291389 2721332323944663307984271)
      ·
        refine ⟨4081998485916994961976407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2721332323944663307984271 4081998485916994961976407)
        ·
          refine ⟨6122997728875492442964611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4081998485916994961976407 6122997728875492442964611)
          ·
            refine ⟨9184496593313238664446917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6122997728875492442964611 9184496593313238664446917)
            ·
              refine ⟨1722093111246232249583797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9184496593313238664446917 1722093111246232249583797)
              ·
                refine ⟨161446229179334273398481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1722093111246232249583797 161446229179334273398481)
                ·
                  refine ⟨121084671884500705048861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161446229179334273398481 121084671884500705048861)
                  ·
                    rfl

theorem cell20_265288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 2].length) (baseStart_265288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265288 prefixEnd_265288 := by exact prefixLift 265288
  have htrace : WordTrace (prefixWord ++ tailWord_265288) baseStart_265288 baseEnd_265288 := by
    simpa [prefixWord, tailWord_265288, baseEnd_265288] using wordTrace_append hprefix tailTrace_265288
  have hstable : (prefixWord ++ tailWord_265288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265288).length < 2 ^ (prefixWord ++ tailWord_265288).sum := by decide
  have hdescent : baseEnd_265288 < baseStart_265288 := by decide
  rcases family_descends (prefixWord ++ tailWord_265288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265326 : List Nat := [4, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_265326 : Nat := 118140960795 + 265326 * 2 ^ 59
def prefixEnd_265326 : Nat := 4983230072969 + 3 ^ 40 * 265326 * 2
def baseEnd_265326 : Nat := 121102016119941461782039

theorem tailTrace_265326 : CollatzResearch.WordTrace tailWord_265326 prefixEnd_265326 121102016119941461782039 := by
  unfold tailWord_265326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1209654279597086364783979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6451489491184460612181221 1209654279597086364783979)
  ·
    refine ⟨1814481419395629547175969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1209654279597086364783979 1814481419395629547175969)
    ·
      refine ⟨1360861064546722160381977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1814481419395629547175969 1360861064546722160381977)
      ·
        refine ⟨1020645798410041620286483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1360861064546722160381977 1020645798410041620286483)
        ·
          refine ⟨1530968697615062430429725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020645798410041620286483 1530968697615062430429725)
          ·
            refine ⟨574113261605648411411147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1530968697615062430429725 574113261605648411411147)
            ·
              refine ⟨861169892408472617116721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574113261605648411411147 861169892408472617116721)
              ·
                refine ⟨645877419306354462837541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 861169892408472617116721 645877419306354462837541)
                ·
                  refine ⟨121102016119941461782039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 645877419306354462837541 121102016119941461782039)
                  ·
                    rfl

theorem cell20_265326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_265326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265326 prefixEnd_265326 := by exact prefixLift 265326
  have htrace : WordTrace (prefixWord ++ tailWord_265326) baseStart_265326 baseEnd_265326 := by
    simpa [prefixWord, tailWord_265326, baseEnd_265326] using wordTrace_append hprefix tailTrace_265326
  have hstable : (prefixWord ++ tailWord_265326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265326).length < 2 ^ (prefixWord ++ tailWord_265326).sum := by decide
  have hdescent : baseEnd_265326 < baseStart_265326 := by decide
  rcases family_descends (prefixWord ++ tailWord_265326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265354 : List Nat := [3, 1, 2, 3, 1, 1, 9]
def baseStart_265354 : Nat := 118140960795 + 265354 * 2 ^ 59
def prefixEnd_265354 : Nat := 4983230072969 + 3 ^ 40 * 265354 * 2
def baseEnd_265354 : Nat := 13457199564766423205399

theorem tailTrace_265354 : CollatzResearch.WordTrace tailWord_265354 prefixEnd_265354 13457199564766423205399 := by
  unfold tailWord_265354
  simp only [CollatzResearch.WordTrace]
  refine ⟨2419563870168812925072779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6452170320450167800194077 2419563870168812925072779)
  ·
    refine ⟨3629345805253219387609169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2419563870168812925072779 3629345805253219387609169)
    ·
      refine ⟨2722009353939914540706877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3629345805253219387609169 2722009353939914540706877)
      ·
        refine ⟨1020753507727467952765079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2722009353939914540706877 1020753507727467952765079)
        ·
          refine ⟨1531130261591201929147619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020753507727467952765079 1531130261591201929147619)
          ·
            refine ⟨2296695392386802893721429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1531130261591201929147619 2296695392386802893721429)
            ·
              refine ⟨13457199564766423205399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2296695392386802893721429 13457199564766423205399)
              ·
                rfl

theorem cell20_265354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 9].length) (baseStart_265354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265354 prefixEnd_265354 := by exact prefixLift 265354
  have htrace : WordTrace (prefixWord ++ tailWord_265354) baseStart_265354 baseEnd_265354 := by
    simpa [prefixWord, tailWord_265354, baseEnd_265354] using wordTrace_append hprefix tailTrace_265354
  have hstable : (prefixWord ++ tailWord_265354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265354).length < 2 ^ (prefixWord ++ tailWord_265354).sum := by decide
  have hdescent : baseEnd_265354 < baseStart_265354 := by decide
  rcases family_descends (prefixWord ++ tailWord_265354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265399 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 7]
def baseStart_265399 : Nat := 118140960795 + 265399 * 2 ^ 59
def prefixEnd_265399 : Nat := 4983230072969 + 3 ^ 40 * 265399 * 2
def baseEnd_265399 : Nat := 121135335309077652348407

theorem tailTrace_265399 : CollatzResearch.WordTrace tailWord_265399 prefixEnd_265399 121135335309077652348407 := by
  unfold tailWord_265399
  simp only [CollatzResearch.WordTrace]
  refine ⟨9679896765512224385679251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6453264510341482923786167 9679896765512224385679251)
  ·
    refine ⟨14519845148268336578518877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9679896765512224385679251 14519845148268336578518877)
    ·
      refine ⟨5444941930600626216944579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14519845148268336578518877 5444941930600626216944579)
      ·
        refine ⟨8167412895900939325416869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5444941930600626216944579 8167412895900939325416869)
        ·
          refine ⟨1531389917981426123515663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8167412895900939325416869 1531389917981426123515663)
          ·
            refine ⟨2297084876972139185273495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1531389917981426123515663 2297084876972139185273495)
            ·
              refine ⟨3445627315458208777910243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2297084876972139185273495 3445627315458208777910243)
              ·
                refine ⟨5168440973187313166865365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3445627315458208777910243 5168440973187313166865365)
                ·
                  refine ⟨121135335309077652348407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5168440973187313166865365 121135335309077652348407)
                  ·
                    rfl

theorem cell20_265399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_265399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265399 prefixEnd_265399 := by exact prefixLift 265399
  have htrace : WordTrace (prefixWord ++ tailWord_265399) baseStart_265399 baseEnd_265399 := by
    simpa [prefixWord, tailWord_265399, baseEnd_265399] using wordTrace_append hprefix tailTrace_265399
  have hstable : (prefixWord ++ tailWord_265399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265399).length < 2 ^ (prefixWord ++ tailWord_265399).sum := by decide
  have hdescent : baseEnd_265399 < baseStart_265399 := by decide
  rcases family_descends (prefixWord ++ tailWord_265399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265409 : List Nat := [1, 2, 6, 1, 1, 1, 8]
def baseStart_265409 : Nat := 118140960795 + 265409 * 2 ^ 59
def prefixEnd_265409 : Nat := 4983230072969 + 3 ^ 40 * 265409 * 2
def baseEnd_265409 : Nat := 13459988842395784668337

theorem tailTrace_265409 : CollatzResearch.WordTrace tailWord_265409 prefixEnd_265409 13459988842395784668337 := by
  unfold tailWord_265409
  simp only [CollatzResearch.WordTrace]
  refine ⟨9680261495475996093543281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6453507663650664062362187 9680261495475996093543281)
  ·
    refine ⟨7260196121606997070157461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9680261495475996093543281 7260196121606997070157461)
    ·
      refine ⟨340321693200327987663631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7260196121606997070157461 340321693200327987663631)
      ·
        refine ⟨510482539800491981495447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340321693200327987663631 510482539800491981495447)
        ·
          refine ⟨765723809700737972243171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510482539800491981495447 765723809700737972243171)
          ·
            refine ⟨1148585714551106958364757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765723809700737972243171 1148585714551106958364757)
            ·
              refine ⟨13459988842395784668337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1148585714551106958364757 13459988842395784668337)
              ·
                rfl

theorem cell20_265409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 8].length) (baseStart_265409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265409 prefixEnd_265409 := by exact prefixLift 265409
  have htrace : WordTrace (prefixWord ++ tailWord_265409) baseStart_265409 baseEnd_265409 := by
    simpa [prefixWord, tailWord_265409, baseEnd_265409] using wordTrace_append hprefix tailTrace_265409
  have hstable : (prefixWord ++ tailWord_265409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265409).length < 2 ^ (prefixWord ++ tailWord_265409).sum := by decide
  have hdescent : baseEnd_265409 < baseStart_265409 := by decide
  rcases family_descends (prefixWord ++ tailWord_265409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265468 : List Nat := [2, 2, 2, 1, 5, 8]
def baseStart_265468 : Nat := 118140960795 + 265468 * 2 ^ 59
def prefixEnd_265468 : Nat := 4983230072969 + 3 ^ 40 * 265468 * 2
def baseEnd_265468 : Nat := 4487660325526669594375

theorem tailTrace_265468 : CollatzResearch.WordTrace tailWord_265468 prefixEnd_265468 4487660325526669594375 := by
  unfold tailWord_265468
  simp only [CollatzResearch.WordTrace]
  refine ⟨4841206701131124584970529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6454942268174832779960705 4841206701131124584970529)
  ·
    refine ⟨3630905025848343438727897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4841206701131124584970529 3630905025848343438727897)
    ·
      refine ⟨2723178769386257579045923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3630905025848343438727897 2723178769386257579045923)
      ·
        refine ⟨4084768154079386368568885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2723178769386257579045923 4084768154079386368568885)
        ·
          refine ⟨382947014444942472053333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4084768154079386368568885 382947014444942472053333)
          ·
            refine ⟨4487660325526669594375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 382947014444942472053333 4487660325526669594375)
            ·
              rfl

theorem cell20_265468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 8].length) (baseStart_265468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265468 prefixEnd_265468 := by exact prefixLift 265468
  have htrace : WordTrace (prefixWord ++ tailWord_265468) baseStart_265468 baseEnd_265468 := by
    simpa [prefixWord, tailWord_265468, baseEnd_265468] using wordTrace_append hprefix tailTrace_265468
  have hstable : (prefixWord ++ tailWord_265468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265468).length < 2 ^ (prefixWord ++ tailWord_265468).sum := by decide
  have hdescent : baseEnd_265468 < baseStart_265468 := by decide
  rcases family_descends (prefixWord ++ tailWord_265468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265474 : List Nat := [3, 4, 1, 1, 3, 1, 1, 4, 2]
def baseStart_265474 : Nat := 118140960795 + 265474 * 2 ^ 59
def prefixEnd_265474 : Nat := 4983230072969 + 3 ^ 40 * 265474 * 2
def baseEnd_265474 : Nat := 121169567352710724848101

theorem tailTrace_265474 : CollatzResearch.WordTrace tailWord_265474 prefixEnd_265474 121169567352710724848101 := by
  unfold tailWord_265474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2420658060060128048664869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6455088160160341463106317 2420658060060128048664869)
  ·
    refine ⟨453873386261274009124663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2420658060060128048664869 453873386261274009124663)
    ·
      refine ⟨680810079391911013686995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453873386261274009124663 680810079391911013686995)
      ·
        refine ⟨1021215119087866520530493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680810079391911013686995 1021215119087866520530493)
        ·
          refine ⟨382955669657949945198935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1021215119087866520530493 382955669657949945198935)
          ·
            refine ⟨574433504486924917798403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382955669657949945198935 574433504486924917798403)
            ·
              refine ⟨861650256730387376697605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574433504486924917798403 861650256730387376697605)
              ·
                refine ⟨161559423136947633130801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 861650256730387376697605 161559423136947633130801)
                ·
                  refine ⟨121169567352710724848101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161559423136947633130801 121169567352710724848101)
                  ·
                    rfl

theorem cell20_265474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_265474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265474 prefixEnd_265474 := by exact prefixLift 265474
  have htrace : WordTrace (prefixWord ++ tailWord_265474) baseStart_265474 baseEnd_265474 := by
    simpa [prefixWord, tailWord_265474, baseEnd_265474] using wordTrace_append hprefix tailTrace_265474
  have hstable : (prefixWord ++ tailWord_265474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265474).length < 2 ^ (prefixWord ++ tailWord_265474).sum := by decide
  have hdescent : baseEnd_265474 < baseStart_265474 := by decide
  rcases family_descends (prefixWord ++ tailWord_265474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265520 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 6]
def baseStart_265520 : Nat := 118140960795 + 265520 * 2 ^ 59
def prefixEnd_265520 : Nat := 4983230072969 + 3 ^ 40 * 265520 * 2
def baseEnd_265520 : Nat := 121190563006139009314579

theorem tailTrace_265520 : CollatzResearch.WordTrace tailWord_265520 prefixEnd_265520 121190563006139009314579 := by
  unfold tailWord_265520
  simp only [CollatzResearch.WordTrace]
  refine ⟨4842154999036931025417007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6456206665382574700556009 4842154999036931025417007)
  ·
    refine ⟨7263232498555396538125511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4842154999036931025417007 7263232498555396538125511)
    ·
      refine ⟨10894848747833094807188267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7263232498555396538125511 10894848747833094807188267)
      ·
        refine ⟨16342273121749642210782401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10894848747833094807188267 16342273121749642210782401)
        ·
          refine ⟨12256704841312231658086801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16342273121749642210782401 12256704841312231658086801)
          ·
            refine ⟨9192528630984173743565101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12256704841312231658086801 9192528630984173743565101)
            ·
              refine ⟨3447198236619065153836913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9192528630984173743565101 3447198236619065153836913)
              ·
                refine ⟨2585398677464298865377685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3447198236619065153836913 2585398677464298865377685)
                ·
                  refine ⟨121190563006139009314579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2585398677464298865377685 121190563006139009314579)
                  ·
                    rfl

theorem cell20_265520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_265520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265520 prefixEnd_265520 := by exact prefixLift 265520
  have htrace : WordTrace (prefixWord ++ tailWord_265520) baseStart_265520 baseEnd_265520 := by
    simpa [prefixWord, tailWord_265520, baseEnd_265520] using wordTrace_append hprefix tailTrace_265520
  have hstable : (prefixWord ++ tailWord_265520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265520).length < 2 ^ (prefixWord ++ tailWord_265520).sum := by decide
  have hdescent : baseEnd_265520 < baseStart_265520 := by decide
  rcases family_descends (prefixWord ++ tailWord_265520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265526 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_265526 : Nat := 118140960795 + 265526 * 2 ^ 59
def prefixEnd_265526 : Nat := 4983230072969 + 3 ^ 40 * 265526 * 2
def baseEnd_265526 : Nat := 121193301569629655114555

theorem tailTrace_265526 : CollatzResearch.WordTrace tailWord_265526 prefixEnd_265526 121193301569629655114555 := by
  unfold tailWord_265526
  simp only [CollatzResearch.WordTrace]
  refine ⟨605283052253257817222027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6456352557368083383701621 605283052253257817222027)
  ·
    refine ⟨907924578379886725833041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 605283052253257817222027 907924578379886725833041)
    ·
      refine ⟨680943433784915044374781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 907924578379886725833041 680943433784915044374781)
      ·
        refine ⟨255353787669343141640543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 680943433784915044374781 255353787669343141640543)
        ·
          refine ⟨383030681504014712460815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255353787669343141640543 383030681504014712460815)
          ·
            refine ⟨574546022256022068691223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383030681504014712460815 574546022256022068691223)
            ·
              refine ⟨861819033384033103036835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574546022256022068691223 861819033384033103036835)
              ·
                refine ⟨1292728550076049654555253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 861819033384033103036835 1292728550076049654555253)
                ·
                  refine ⟨121193301569629655114555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1292728550076049654555253 121193301569629655114555)
                  ·
                    rfl

theorem cell20_265526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_265526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265526 prefixEnd_265526 := by exact prefixLift 265526
  have htrace : WordTrace (prefixWord ++ tailWord_265526) baseStart_265526 baseEnd_265526 := by
    simpa [prefixWord, tailWord_265526, baseEnd_265526] using wordTrace_append hprefix tailTrace_265526
  have hstable : (prefixWord ++ tailWord_265526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265526).length < 2 ^ (prefixWord ++ tailWord_265526).sum := by decide
  have hdescent : baseEnd_265526 < baseStart_265526 := by decide
  rcases family_descends (prefixWord ++ tailWord_265526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265533 : List Nat := [1, 4, 1, 5, 1, 1, 2, 1, 4]
def baseStart_265533 : Nat := 118140960795 + 265533 * 2 ^ 59
def prefixEnd_265533 : Nat := 4983230072969 + 3 ^ 40 * 265533 * 2
def baseEnd_265533 : Nat := 121196496560368741881193

theorem tailTrace_265533 : CollatzResearch.WordTrace tailWord_265533 prefixEnd_265533 121196496560368741881193 := by
  unfold tailWord_265533
  simp only [CollatzResearch.WordTrace]
  refine ⟨9684784147026765271057253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6456522764684510180704835 9684784147026765271057253)
  ·
    refine ⟨1815897027567518488323235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9684784147026765271057253 1815897027567518488323235)
    ·
      refine ⟨2723845541351277732484853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1815897027567518488323235 2723845541351277732484853)
      ·
        refine ⟨255360519501682287420455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2723845541351277732484853 255360519501682287420455)
        ·
          refine ⟨383040779252523431130683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255360519501682287420455 383040779252523431130683)
          ·
            refine ⟨574561168878785146696025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383040779252523431130683 574561168878785146696025)
            ·
              refine ⟨430920876659088860022019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574561168878785146696025 430920876659088860022019)
              ·
                refine ⟨646381314988633290033029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430920876659088860022019 646381314988633290033029)
                ·
                  refine ⟨121196496560368741881193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 646381314988633290033029 121196496560368741881193)
                  ·
                    rfl

theorem cell20_265533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_265533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265533 prefixEnd_265533 := by exact prefixLift 265533
  have htrace : WordTrace (prefixWord ++ tailWord_265533) baseStart_265533 baseEnd_265533 := by
    simpa [prefixWord, tailWord_265533, baseEnd_265533] using wordTrace_append hprefix tailTrace_265533
  have hstable : (prefixWord ++ tailWord_265533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265533).length < 2 ^ (prefixWord ++ tailWord_265533).sum := by decide
  have hdescent : baseEnd_265533 < baseStart_265533 := by decide
  rcases family_descends (prefixWord ++ tailWord_265533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265571 : List Nat := [1, 1, 1, 5, 2, 4, 1, 3, 2]
def baseStart_265571 : Nat := 118140960795 + 265571 * 2 ^ 59
def prefixEnd_265571 : Nat := 4983230072969 + 3 ^ 40 * 265571 * 2
def baseEnd_265571 : Nat := 121213840795809498614371

theorem tailTrace_265571 : CollatzResearch.WordTrace tailWord_265571 prefixEnd_265571 121213840795809498614371 := by
  unfold tailWord_265571
  simp only [CollatzResearch.WordTrace]
  refine ⟨9686170120889097760940567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6457446747259398507293711 9686170120889097760940567)
  ·
    refine ⟨14529255181333646641410851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9686170120889097760940567 14529255181333646641410851)
    ·
      refine ⟨21793882772000469962116277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14529255181333646641410851 21793882772000469962116277)
      ·
        refine ⟨2043176509875044058948401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21793882772000469962116277 2043176509875044058948401)
        ·
          refine ⟨1532382382406283044211301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2043176509875044058948401 1532382382406283044211301)
          ·
            refine ⟨287321696701178070789619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1532382382406283044211301 287321696701178070789619)
            ·
              refine ⟨430982545051767106184429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287321696701178070789619 430982545051767106184429)
              ·
                refine ⟨161618454394412664819161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 430982545051767106184429 161618454394412664819161)
                ·
                  refine ⟨121213840795809498614371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161618454394412664819161 121213840795809498614371)
                  ·
                    rfl

theorem cell20_265571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 3, 2].length) (baseStart_265571 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265571 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265571 prefixEnd_265571 := by exact prefixLift 265571
  have htrace : WordTrace (prefixWord ++ tailWord_265571) baseStart_265571 baseEnd_265571 := by
    simpa [prefixWord, tailWord_265571, baseEnd_265571] using wordTrace_append hprefix tailTrace_265571
  have hstable : (prefixWord ++ tailWord_265571).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265571).length < 2 ^ (prefixWord ++ tailWord_265571).sum := by decide
  have hdescent : baseEnd_265571 < baseStart_265571 := by decide
  rcases family_descends (prefixWord ++ tailWord_265571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265578 : List Nat := [3, 1, 3, 3, 3, 1, 6]
def baseStart_265578 : Nat := 118140960795 + 265578 * 2 ^ 59
def prefixEnd_265578 : Nat := 4983230072969 + 3 ^ 40 * 265578 * 2
def baseEnd_265578 : Nat := 13468559531838731709001

theorem tailTrace_265578 : CollatzResearch.WordTrace tailWord_265578 prefixEnd_265578 13468559531838731709001 := by
  unfold tailWord_265578
  simp only [CollatzResearch.WordTrace]
  refine ⟨2421606357965934489111347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6457616954575825304296925 2421606357965934489111347)
  ·
    refine ⟨3632409536948901733667021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2421606357965934489111347 3632409536948901733667021)
    ·
      refine ⟨1362153576355838150125133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3632409536948901733667021 1362153576355838150125133)
      ·
        refine ⟨510807591133439306296925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1362153576355838150125133 510807591133439306296925)
        ·
          refine ⟨191552846675039739861347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 510807591133439306296925 191552846675039739861347)
          ·
            refine ⟨287329270012559609792021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191552846675039739861347 287329270012559609792021)
            ·
              refine ⟨13468559531838731709001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 287329270012559609792021 13468559531838731709001)
              ·
                rfl

theorem cell20_265578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 6].length) (baseStart_265578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265578 prefixEnd_265578 := by exact prefixLift 265578
  have htrace : WordTrace (prefixWord ++ tailWord_265578) baseStart_265578 baseEnd_265578 := by
    simpa [prefixWord, tailWord_265578, baseEnd_265578] using wordTrace_append hprefix tailTrace_265578
  have hstable : (prefixWord ++ tailWord_265578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265578).length < 2 ^ (prefixWord ++ tailWord_265578).sum := by decide
  have hdescent : baseEnd_265578 < baseStart_265578 := by decide
  rcases family_descends (prefixWord ++ tailWord_265578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265598 : List Nat := [4, 2, 3, 2, 1, 2, 2, 1, 3]
def baseStart_265598 : Nat := 118140960795 + 265598 * 2 ^ 59
def prefixEnd_265598 : Nat := 4983230072969 + 3 ^ 40 * 265598 * 2
def baseEnd_265598 : Nat := 121226164331517404714261

theorem tailTrace_265598 : CollatzResearch.WordTrace tailWord_265598 prefixEnd_265598 121226164331517404714261 := by
  unfold tailWord_265598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1210894361473910171521681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6458103261194187581448965 1210894361473910171521681)
  ·
    refine ⟨908170771105432628641261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1210894361473910171521681 908170771105432628641261)
    ·
      refine ⟨340564039164537235740473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 908170771105432628641261 340564039164537235740473)
      ·
        refine ⟨255423029373402926805355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340564039164537235740473 255423029373402926805355)
        ·
          refine ⟨383134544060104390208033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255423029373402926805355 383134544060104390208033)
          ·
            refine ⟨287350908045078292656025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 383134544060104390208033 287350908045078292656025)
            ·
              refine ⟨215513181033808719492019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287350908045078292656025 215513181033808719492019)
              ·
                refine ⟨323269771550713079238029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215513181033808719492019 323269771550713079238029)
                ·
                  refine ⟨121226164331517404714261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323269771550713079238029 121226164331517404714261)
                  ·
                    rfl

theorem cell20_265598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_265598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265598 prefixEnd_265598 := by exact prefixLift 265598
  have htrace : WordTrace (prefixWord ++ tailWord_265598) baseStart_265598 baseEnd_265598 := by
    simpa [prefixWord, tailWord_265598, baseEnd_265598] using wordTrace_append hprefix tailTrace_265598
  have hstable : (prefixWord ++ tailWord_265598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265598).length < 2 ^ (prefixWord ++ tailWord_265598).sum := by decide
  have hdescent : baseEnd_265598 < baseStart_265598 := by decide
  rcases family_descends (prefixWord ++ tailWord_265598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265602 : List Nat := [3, 4, 2, 1, 1, 2, 1, 3, 3]
def baseStart_265602 : Nat := 118140960795 + 265602 * 2 ^ 59
def prefixEnd_265602 : Nat := 4983230072969 + 3 ^ 40 * 265602 * 2
def baseEnd_265602 : Nat := 121227990040511168580911

theorem tailTrace_265602 : CollatzResearch.WordTrace tailWord_265602 prefixEnd_265602 121227990040511168580911 := by
  unfold tailWord_265602
  simp only [CollatzResearch.WordTrace]
  refine ⟨2421825195944197513829765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6458200522517860036879373 2421825195944197513829765)
  ·
    refine ⟨454092224239537033843081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2421825195944197513829765 454092224239537033843081)
    ·
      refine ⟨340569168179652775382311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 454092224239537033843081 340569168179652775382311)
      ·
        refine ⟨510853752269479163073467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340569168179652775382311 510853752269479163073467)
        ·
          refine ⟨766280628404218744610201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510853752269479163073467 766280628404218744610201)
          ·
            refine ⟨574710471303164058457651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 766280628404218744610201 574710471303164058457651)
            ·
              refine ⟨862065706954746087686477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574710471303164058457651 862065706954746087686477)
              ·
                refine ⟨323274640108029782882429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 862065706954746087686477 323274640108029782882429)
                ·
                  refine ⟨121227990040511168580911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323274640108029782882429 121227990040511168580911)
                  ·
                    rfl

theorem cell20_265602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_265602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265602 prefixEnd_265602 := by exact prefixLift 265602
  have htrace : WordTrace (prefixWord ++ tailWord_265602) baseStart_265602 baseEnd_265602 := by
    simpa [prefixWord, tailWord_265602, baseEnd_265602] using wordTrace_append hprefix tailTrace_265602
  have hstable : (prefixWord ++ tailWord_265602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265602).length < 2 ^ (prefixWord ++ tailWord_265602).sum := by decide
  have hdescent : baseEnd_265602 < baseStart_265602 := by decide
  rcases family_descends (prefixWord ++ tailWord_265602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265640 : List Nat := [2, 1, 6, 1, 2, 1, 2, 2, 3]
def baseStart_265640 : Nat := 118140960795 + 265640 * 2 ^ 59
def prefixEnd_265640 : Nat := 4983230072969 + 3 ^ 40 * 265640 * 2
def baseEnd_265640 : Nat := 121245334275951925314089

theorem tailTrace_265640 : CollatzResearch.WordTrace tailWord_265640 prefixEnd_265640 121245334275951925314089 := by
  unfold tailWord_265640
  simp only [CollatzResearch.WordTrace]
  refine ⟨4844343378819561272601187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6459124505092748363468249 4844343378819561272601187)
  ·
    refine ⟨7266515068229341908901781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4844343378819561272601187 7266515068229341908901781)
    ·
      refine ⟨340617893823250401979771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7266515068229341908901781 340617893823250401979771)
      ·
        refine ⟨510926840734875602969657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340617893823250401979771 510926840734875602969657)
        ·
          refine ⟨383195130551156702227243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510926840734875602969657 383195130551156702227243)
          ·
            refine ⟨574792695826735053340865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383195130551156702227243 574792695826735053340865)
            ·
              refine ⟨431094521870051290005649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574792695826735053340865 431094521870051290005649)
              ·
                refine ⟨323320891402538467504237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431094521870051290005649 323320891402538467504237)
                ·
                  refine ⟨121245334275951925314089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323320891402538467504237 121245334275951925314089)
                  ·
                    rfl

theorem cell20_265640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_265640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265640 prefixEnd_265640 := by exact prefixLift 265640
  have htrace : WordTrace (prefixWord ++ tailWord_265640) baseStart_265640 baseEnd_265640 := by
    simpa [prefixWord, tailWord_265640, baseEnd_265640] using wordTrace_append hprefix tailTrace_265640
  have hstable : (prefixWord ++ tailWord_265640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265640).length < 2 ^ (prefixWord ++ tailWord_265640).sum := by decide
  have hdescent : baseEnd_265640 < baseStart_265640 := by decide
  rcases family_descends (prefixWord ++ tailWord_265640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265668 : List Nat := [2, 3, 3, 2, 1, 2, 1, 2, 4]
def baseStart_265668 : Nat := 118140960795 + 265668 * 2 ^ 59
def prefixEnd_265668 : Nat := 4983230072969 + 3 ^ 40 * 265668 * 2
def baseEnd_265668 : Nat := 121258114238908272380641

theorem tailTrace_265668 : CollatzResearch.WordTrace tailWord_265668 prefixEnd_265668 121258114238908272380641 := by
  unfold tailWord_265668
  simp only [CollatzResearch.WordTrace]
  refine ⟨4844854000768841663610829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6459805334358455551481105 4844854000768841663610829)
  ·
    refine ⟨1816820250288315623854061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4844854000768841663610829 1816820250288315623854061)
    ·
      refine ⟨681307593858118358945273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1816820250288315623854061 681307593858118358945273)
      ·
        refine ⟨510980695393588769208955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681307593858118358945273 510980695393588769208955)
        ·
          refine ⟨766471043090383153813433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510980695393588769208955 766471043090383153813433)
          ·
            refine ⟨574853282317787365360075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 766471043090383153813433 574853282317787365360075)
            ·
              refine ⟨862279923476681048040113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574853282317787365360075 862279923476681048040113)
              ·
                refine ⟨646709942607510786030085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 862279923476681048040113 646709942607510786030085)
                ·
                  refine ⟨121258114238908272380641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 646709942607510786030085 121258114238908272380641)
                  ·
                    rfl

theorem cell20_265668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_265668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265668 prefixEnd_265668 := by exact prefixLift 265668
  have htrace : WordTrace (prefixWord ++ tailWord_265668) baseStart_265668 baseEnd_265668 := by
    simpa [prefixWord, tailWord_265668, baseEnd_265668] using wordTrace_append hprefix tailTrace_265668
  have hstable : (prefixWord ++ tailWord_265668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265668).length < 2 ^ (prefixWord ++ tailWord_265668).sum := by decide
  have hdescent : baseEnd_265668 < baseStart_265668 := by decide
  rcases family_descends (prefixWord ++ tailWord_265668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265679 : List Nat := [1, 1, 2, 1, 1, 4, 2, 8]
def baseStart_265679 : Nat := 118140960795 + 265679 * 2 ^ 59
def prefixEnd_265679 : Nat := 4983230072969 + 3 ^ 40 * 265679 * 2
def baseEnd_265679 : Nat := 40421044979547041004643

theorem tailTrace_265679 : CollatzResearch.WordTrace tailWord_265679 prefixEnd_265679 40421044979547041004643 := by
  unfold tailWord_265679
  simp only [CollatzResearch.WordTrace]
  refine ⟨9690109204497832205872091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6460072802998554803914727 9690109204497832205872091)
  ·
    refine ⟨14535163806746748308808137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9690109204497832205872091 14535163806746748308808137)
    ·
      refine ⟨10901372855060061231606103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14535163806746748308808137 10901372855060061231606103)
      ·
        refine ⟨16352059282590091847409155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10901372855060061231606103 16352059282590091847409155)
        ·
          refine ⟨24528088923885137771113733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16352059282590091847409155 24528088923885137771113733)
          ·
            refine ⟨4599016673228463332083825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24528088923885137771113733 4599016673228463332083825)
            ·
              refine ⟨3449262504921347499062869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4599016673228463332083825 3449262504921347499062869)
              ·
                refine ⟨40421044979547041004643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3449262504921347499062869 40421044979547041004643)
                ·
                  rfl

theorem cell20_265679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 8].length) (baseStart_265679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265679 prefixEnd_265679 := by exact prefixLift 265679
  have htrace : WordTrace (prefixWord ++ tailWord_265679) baseStart_265679 baseEnd_265679 := by
    simpa [prefixWord, tailWord_265679, baseEnd_265679] using wordTrace_append hprefix tailTrace_265679
  have hstable : (prefixWord ++ tailWord_265679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265679).length < 2 ^ (prefixWord ++ tailWord_265679).sum := by decide
  have hdescent : baseEnd_265679 < baseStart_265679 := by decide
  rcases family_descends (prefixWord ++ tailWord_265679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265699 : List Nat := [1, 1, 1, 6, 2, 3, 1, 2, 3]
def baseStart_265699 : Nat := 118140960795 + 265699 * 2 ^ 59
def prefixEnd_265699 : Nat := 4983230072969 + 3 ^ 40 * 265699 * 2
def baseEnd_265699 : Nat := 121272263483609942347181

theorem tailTrace_265699 : CollatzResearch.WordTrace tailWord_265699 prefixEnd_265699 121272263483609942347181 := by
  unfold tailWord_265699
  simp only [CollatzResearch.WordTrace]
  refine ⟨9690838664425375621600151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6460559109616917081066767 9690838664425375621600151)
  ·
    refine ⟨14536257996638063432400227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9690838664425375621600151 14536257996638063432400227)
    ·
      refine ⟨21804386994957095148600341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14536257996638063432400227 21804386994957095148600341)
      ·
        refine ⟨1022080640388613835090641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21804386994957095148600341 1022080640388613835090641)
        ·
          refine ⟨766560480291460376317981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1022080640388613835090641 766560480291460376317981)
          ·
            refine ⟨287460180109297641119243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 766560480291460376317981 287460180109297641119243)
            ·
              refine ⟨431190270163946461678865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287460180109297641119243 431190270163946461678865)
              ·
                refine ⟨323392702622959846259149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431190270163946461678865 323392702622959846259149)
                ·
                  refine ⟨121272263483609942347181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323392702622959846259149 121272263483609942347181)
                  ·
                    rfl

theorem cell20_265699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 3].length) (baseStart_265699 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265699 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265699 prefixEnd_265699 := by exact prefixLift 265699
  have htrace : WordTrace (prefixWord ++ tailWord_265699) baseStart_265699 baseEnd_265699 := by
    simpa [prefixWord, tailWord_265699, baseEnd_265699] using wordTrace_append hprefix tailTrace_265699
  have hstable : (prefixWord ++ tailWord_265699).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265699).length < 2 ^ (prefixWord ++ tailWord_265699).sum := by decide
  have hdescent : baseEnd_265699 < baseStart_265699 := by decide
  rcases family_descends (prefixWord ++ tailWord_265699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265706 : List Nat := [3, 1, 3, 1, 4, 1, 2, 1, 4]
def baseStart_265706 : Nat := 118140960795 + 265706 * 2 ^ 59
def prefixEnd_265706 : Nat := 4983230072969 + 3 ^ 40 * 265706 * 2
def baseEnd_265706 : Nat := 121275458474349029113819

theorem tailTrace_265706 : CollatzResearch.WordTrace tailWord_265706 prefixEnd_265706 121275458474349029113819 := by
  unfold tailWord_265706
  simp only [CollatzResearch.WordTrace]
  refine ⟨2422773493850003954276243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6460729316933343878069981 2422773493850003954276243)
  ·
    refine ⟨3634160240775005931414365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2422773493850003954276243 3634160240775005931414365)
    ·
      refine ⟨1362810090290627224280387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3634160240775005931414365 1362810090290627224280387)
      ·
        refine ⟨2044215135435940836420581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1362810090290627224280387 2044215135435940836420581)
        ·
          refine ⟨383290337894238906828859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2044215135435940836420581 383290337894238906828859)
          ·
            refine ⟨574935506841358360243289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 383290337894238906828859 574935506841358360243289)
            ·
              refine ⟨431201630131018770182467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 574935506841358360243289 431201630131018770182467)
              ·
                refine ⟨646802445196528155273701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431201630131018770182467 646802445196528155273701)
                ·
                  refine ⟨121275458474349029113819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 646802445196528155273701 121275458474349029113819)
                  ·
                    rfl

theorem cell20_265706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_265706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265706 prefixEnd_265706 := by exact prefixLift 265706
  have htrace : WordTrace (prefixWord ++ tailWord_265706) baseStart_265706 baseEnd_265706 := by
    simpa [prefixWord, tailWord_265706, baseEnd_265706] using wordTrace_append hprefix tailTrace_265706
  have hstable : (prefixWord ++ tailWord_265706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265706).length < 2 ^ (prefixWord ++ tailWord_265706).sum := by decide
  have hdescent : baseEnd_265706 < baseStart_265706 := by decide
  rcases family_descends (prefixWord ++ tailWord_265706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265726 : List Nat := [4, 2, 2, 3, 2, 1, 2, 4]
def baseStart_265726 : Nat := 118140960795 + 265726 * 2 ^ 59
def prefixEnd_265726 : Nat := 4983230072969 + 3 ^ 40 * 265726 * 2
def baseEnd_265726 : Nat := 40428195673105949482357

theorem tailTrace_265726 : CollatzResearch.WordTrace tailWord_265726 prefixEnd_265726 40428195673105949482357 := by
  unfold tailWord_265726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1211477929415944904104129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6461215623551706155222021 1211477929415944904104129)
  ·
    refine ⟨908608447061958678078097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1211477929415944904104129 908608447061958678078097)
    ·
      refine ⟨681456335296469008558573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 908608447061958678078097 681456335296469008558573)
      ·
        refine ⟨255546125736175878209465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 681456335296469008558573 255546125736175878209465)
        ·
          refine ⟨191659594302131908657099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255546125736175878209465 191659594302131908657099)
          ·
            refine ⟨287489391453197862985649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191659594302131908657099 287489391453197862985649)
            ·
              refine ⟨215617043589898397239237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287489391453197862985649 215617043589898397239237)
              ·
                refine ⟨40428195673105949482357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215617043589898397239237 40428195673105949482357)
                ·
                  rfl

theorem cell20_265726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_265726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265726 prefixEnd_265726 := by exact prefixLift 265726
  have htrace : WordTrace (prefixWord ++ tailWord_265726) baseStart_265726 baseEnd_265726 := by
    simpa [prefixWord, tailWord_265726, baseEnd_265726] using wordTrace_append hprefix tailTrace_265726
  have hstable : (prefixWord ++ tailWord_265726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265726).length < 2 ^ (prefixWord ++ tailWord_265726).sum := by decide
  have hdescent : baseEnd_265726 < baseStart_265726 := by decide
  rcases family_descends (prefixWord ++ tailWord_265726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265730 : List Nat := [3, 4, 1, 2, 1, 1, 4, 4]
def baseStart_265730 : Nat := 118140960795 + 265730 * 2 ^ 59
def prefixEnd_265730 : Nat := 4983230072969 + 3 ^ 40 * 265730 * 2
def baseEnd_265730 : Nat := 40428804242770537437907

theorem tailTrace_265730 : CollatzResearch.WordTrace tailWord_265730 prefixEnd_265730 40428804242770537437907 := by
  unfold tailWord_265730
  simp only [CollatzResearch.WordTrace]
  refine ⟨2422992331828266978994661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6461312884875378610652429 2422992331828266978994661)
  ·
    refine ⟨454311062217800058561499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2422992331828266978994661 454311062217800058561499)
    ·
      refine ⟨681466593326700087842249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 454311062217800058561499 681466593326700087842249)
      ·
        refine ⟨511099944995025065881687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 681466593326700087842249 511099944995025065881687)
        ·
          refine ⟨766649917492537598822531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 511099944995025065881687 766649917492537598822531)
          ·
            refine ⟨1149974876238806398233797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766649917492537598822531 1149974876238806398233797)
            ·
              refine ⟨215620289294776199668837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1149974876238806398233797 215620289294776199668837)
              ·
                refine ⟨40428804242770537437907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215620289294776199668837 40428804242770537437907)
                ·
                  rfl

theorem cell20_265730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_265730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265730 prefixEnd_265730 := by exact prefixLift 265730
  have htrace : WordTrace (prefixWord ++ tailWord_265730) baseStart_265730 baseEnd_265730 := by
    simpa [prefixWord, tailWord_265730, baseEnd_265730] using wordTrace_append hprefix tailTrace_265730
  have hstable : (prefixWord ++ tailWord_265730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265730).length < 2 ^ (prefixWord ++ tailWord_265730).sum := by decide
  have hdescent : baseEnd_265730 < baseStart_265730 := by decide
  rcases family_descends (prefixWord ++ tailWord_265730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265740 : List Nat := [2, 2, 1, 2, 6, 1, 1, 3, 2]
def baseStart_265740 : Nat := 118140960795 + 265740 * 2 ^ 59
def prefixEnd_265740 : Nat := 4983230072969 + 3 ^ 40 * 265740 * 2
def baseEnd_265740 : Nat := 121290977000796021980347

theorem tailTrace_265740 : CollatzResearch.WordTrace tailWord_265740 prefixEnd_265740 121290977000796021980347 := by
  unfold tailWord_265740
  simp only [CollatzResearch.WordTrace]
  refine ⟨4846167028638419811921337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6461556038184559749228449 4846167028638419811921337)
  ·
    refine ⟨3634625271478814858941003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4846167028638419811921337 3634625271478814858941003)
    ·
      refine ⟨5451937907218222288411505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3634625271478814858941003 5451937907218222288411505)
      ·
        refine ⟨4088953430413666716308629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5451937907218222288411505 4088953430413666716308629)
        ·
          refine ⟨191669692050640627326967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4088953430413666716308629 191669692050640627326967)
          ·
            refine ⟨287504538075960940990451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191669692050640627326967 287504538075960940990451)
            ·
              refine ⟨431256807113941411485677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287504538075960940990451 431256807113941411485677)
              ·
                refine ⟨161721302667728029307129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 431256807113941411485677 161721302667728029307129)
                ·
                  refine ⟨121290977000796021980347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161721302667728029307129 121290977000796021980347)
                  ·
                    rfl

theorem cell20_265740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_265740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265740 prefixEnd_265740 := by exact prefixLift 265740
  have htrace : WordTrace (prefixWord ++ tailWord_265740) baseStart_265740 baseEnd_265740 := by
    simpa [prefixWord, tailWord_265740, baseEnd_265740] using wordTrace_append hprefix tailTrace_265740
  have hstable : (prefixWord ++ tailWord_265740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265740).length < 2 ^ (prefixWord ++ tailWord_265740).sum := by decide
  have hdescent : baseEnd_265740 < baseStart_265740 := by decide
  rcases family_descends (prefixWord ++ tailWord_265740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265761 : List Nat := [1, 2, 3, 2, 2, 3, 3, 2, 2]
def baseStart_265761 : Nat := 118140960795 + 265761 * 2 ^ 59
def prefixEnd_265761 : Nat := 4983230072969 + 3 ^ 40 * 265761 * 2
def baseEnd_265761 : Nat := 121300561973013282280261

theorem tailTrace_265761 : CollatzResearch.WordTrace tailWord_265761 prefixEnd_265761 121300561973013282280261 := by
  unfold tailWord_265761
  simp only [CollatzResearch.WordTrace]
  refine ⟨9693099990200760210357137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6462066660133840140238091 9693099990200760210357137)
  ·
    refine ⟨7269824992650570157767853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9693099990200760210357137 7269824992650570157767853)
    ·
      refine ⟨2726184372243963809162945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7269824992650570157767853 2726184372243963809162945)
      ·
        refine ⟨2044638279182972856872209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2726184372243963809162945 2044638279182972856872209)
        ·
          refine ⟨1533478709387229642654157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2044638279182972856872209 1533478709387229642654157)
          ·
            refine ⟨575054516020211115995309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1533478709387229642654157 575054516020211115995309)
            ·
              refine ⟨215645443507579168498241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 575054516020211115995309 215645443507579168498241)
              ·
                refine ⟨161734082630684376373681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215645443507579168498241 161734082630684376373681)
                ·
                  refine ⟨121300561973013282280261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161734082630684376373681 121300561973013282280261)
                  ·
                    rfl

theorem cell20_265761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 2].length) (baseStart_265761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265761 prefixEnd_265761 := by exact prefixLift 265761
  have htrace : WordTrace (prefixWord ++ tailWord_265761) baseStart_265761 baseEnd_265761 := by
    simpa [prefixWord, tailWord_265761, baseEnd_265761] using wordTrace_append hprefix tailTrace_265761
  have hstable : (prefixWord ++ tailWord_265761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265761).length < 2 ^ (prefixWord ++ tailWord_265761).sum := by decide
  have hdescent : baseEnd_265761 < baseStart_265761 := by decide
  rcases family_descends (prefixWord ++ tailWord_265761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265786 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_265786 : Nat := 118140960795 + 265786 * 2 ^ 59
def prefixEnd_265786 : Nat := 4983230072969 + 3 ^ 40 * 265786 * 2
def baseEnd_265786 : Nat := 121311972654224306446825

theorem tailTrace_265786 : CollatzResearch.WordTrace tailWord_265786 prefixEnd_265786 121311972654224306446825 := by
  unfold tailWord_265786
  simp only [CollatzResearch.WordTrace]
  refine ⟨2423502953777547370004303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6462674543406792986678141 2423502953777547370004303)
  ·
    refine ⟨3635254430666321055006455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2423502953777547370004303 3635254430666321055006455)
    ·
      refine ⟨5452881645999481582509683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3635254430666321055006455 5452881645999481582509683)
      ·
        refine ⟨8179322468999222373764525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5452881645999481582509683 8179322468999222373764525)
        ·
          refine ⟨3067245925874708390161697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8179322468999222373764525 3067245925874708390161697)
          ·
            refine ⟨2300434444406031292621273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3067245925874708390161697 2300434444406031292621273)
            ·
              refine ⟨1725325833304523469465955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2300434444406031292621273 1725325833304523469465955)
              ·
                refine ⟨2587988749956785204198933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1725325833304523469465955 2587988749956785204198933)
                ·
                  refine ⟨121311972654224306446825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2587988749956785204198933 121311972654224306446825)
                  ·
                    rfl

theorem cell20_265786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_265786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265786 prefixEnd_265786 := by exact prefixLift 265786
  have htrace : WordTrace (prefixWord ++ tailWord_265786) baseStart_265786 baseEnd_265786 := by
    simpa [prefixWord, tailWord_265786, baseEnd_265786] using wordTrace_append hprefix tailTrace_265786
  have hstable : (prefixWord ++ tailWord_265786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265786).length < 2 ^ (prefixWord ++ tailWord_265786).sum := by decide
  have hdescent : baseEnd_265786 < baseStart_265786 := by decide
  rcases family_descends (prefixWord ++ tailWord_265786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265803 : List Nat := [1, 1, 1, 1, 3, 1, 3, 7, 2]
def baseStart_265803 : Nat := 118140960795 + 265803 * 2 ^ 59
def prefixEnd_265803 : Nat := 4983230072969 + 3 ^ 40 * 265803 * 2
def baseEnd_265803 : Nat := 121319731917447802880089

theorem tailTrace_265803 : CollatzResearch.WordTrace tailWord_265803 prefixEnd_265803 121319731917447802880089 := by
  unfold tailWord_265803
  simp only [CollatzResearch.WordTrace]
  refine ⟨9694631856048601383386063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6463087904032400922257375 9694631856048601383386063)
  ·
    refine ⟨14541947784072902075079095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9694631856048601383386063 14541947784072902075079095)
    ·
      refine ⟨21812921676109353112618643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14541947784072902075079095 21812921676109353112618643)
      ·
        refine ⟨32719382514164029668927965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21812921676109353112618643 32719382514164029668927965)
        ·
          refine ⟨12269768442811511125847987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32719382514164029668927965 12269768442811511125847987)
          ·
            refine ⟨18404652664217266688771981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12269768442811511125847987 18404652664217266688771981)
            ·
              refine ⟨6901744749081475008289493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18404652664217266688771981 6901744749081475008289493)
              ·
                refine ⟨161759642556597070506785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6901744749081475008289493 161759642556597070506785)
                ·
                  refine ⟨121319731917447802880089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161759642556597070506785 121319731917447802880089)
                  ·
                    rfl

theorem cell20_265803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 7, 2].length) (baseStart_265803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265803 prefixEnd_265803 := by exact prefixLift 265803
  have htrace : WordTrace (prefixWord ++ tailWord_265803) baseStart_265803 baseEnd_265803 := by
    simpa [prefixWord, tailWord_265803, baseEnd_265803] using wordTrace_append hprefix tailTrace_265803
  have hstable : (prefixWord ++ tailWord_265803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265803).length < 2 ^ (prefixWord ++ tailWord_265803).sum := by decide
  have hdescent : baseEnd_265803 < baseStart_265803 := by decide
  rcases family_descends (prefixWord ++ tailWord_265803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265824 : List Nat := [2, 1, 1, 3, 2, 1, 1, 5, 4]
def baseStart_265824 : Nat := 118140960795 + 265824 * 2 ^ 59
def prefixEnd_265824 : Nat := 4983230072969 + 3 ^ 40 * 265824 * 2
def baseEnd_265824 : Nat := 121329316889665063180003

theorem tailTrace_265824 : CollatzResearch.WordTrace tailWord_265824 prefixEnd_265824 121329316889665063180003 := by
  unfold tailWord_265824
  simp only [CollatzResearch.WordTrace]
  refine ⟨4847698894486260984950263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6463598525981681313267017 4847698894486260984950263)
  ·
    refine ⟨7271548341729391477425395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4847698894486260984950263 7271548341729391477425395)
    ·
      refine ⟨10907322512594087216138093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7271548341729391477425395 10907322512594087216138093)
      ·
        refine ⟨4090245942222782706051785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10907322512594087216138093 4090245942222782706051785)
        ·
          refine ⟨3067684456667087029538839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4090245942222782706051785 3067684456667087029538839)
          ·
            refine ⟨4601526685000630544308259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3067684456667087029538839 4601526685000630544308259)
            ·
              refine ⟨6902290027500945816462389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4601526685000630544308259 6902290027500945816462389)
              ·
                refine ⟨647089690078213670293349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6902290027500945816462389 647089690078213670293349)
                ·
                  refine ⟨121329316889665063180003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 647089690078213670293349 121329316889665063180003)
                  ·
                    rfl

theorem cell20_265824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_265824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265824 prefixEnd_265824 := by exact prefixLift 265824
  have htrace : WordTrace (prefixWord ++ tailWord_265824) baseStart_265824 baseEnd_265824 := by
    simpa [prefixWord, tailWord_265824, baseEnd_265824] using wordTrace_append hprefix tailTrace_265824
  have hstable : (prefixWord ++ tailWord_265824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265824).length < 2 ^ (prefixWord ++ tailWord_265824).sum := by decide
  have hdescent : baseEnd_265824 < baseStart_265824 := by decide
  rcases family_descends (prefixWord ++ tailWord_265824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265834 : List Nat := [3, 1, 3, 2, 1, 2, 2, 3, 3]
def baseStart_265834 : Nat := 118140960795 + 265834 * 2 ^ 59
def prefixEnd_265834 : Nat := 4983230072969 + 3 ^ 40 * 265834 * 2
def baseEnd_265834 : Nat := 121333881162149472846629

theorem tailTrace_265834 : CollatzResearch.WordTrace tailWord_265834 prefixEnd_265834 121333881162149472846629 := by
  unfold tailWord_265834
  simp only [CollatzResearch.WordTrace]
  refine ⟨2423940629734073419441139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6463841679290862451843037 2423940629734073419441139)
  ·
    refine ⟨3635910944601110129161709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2423940629734073419441139 3635910944601110129161709)
    ·
      refine ⟨1363466604225416298435641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3635910944601110129161709 1363466604225416298435641)
      ·
        refine ⟨1022599953169062223826731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1363466604225416298435641 1022599953169062223826731)
        ·
          refine ⟨1533899929753593335740097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022599953169062223826731 1533899929753593335740097)
          ·
            refine ⟨1150424947315195001805073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1533899929753593335740097 1150424947315195001805073)
            ·
              refine ⟨862818710486396251353805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1150424947315195001805073 862818710486396251353805)
              ·
                refine ⟨323557016432398594257677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 862818710486396251353805 323557016432398594257677)
                ·
                  refine ⟨121333881162149472846629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323557016432398594257677 121333881162149472846629)
                  ·
                    rfl

theorem cell20_265834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_265834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265834 prefixEnd_265834 := by exact prefixLift 265834
  have htrace : WordTrace (prefixWord ++ tailWord_265834) baseStart_265834 baseEnd_265834 := by
    simpa [prefixWord, tailWord_265834, baseEnd_265834] using wordTrace_append hprefix tailTrace_265834
  have hstable : (prefixWord ++ tailWord_265834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265834).length < 2 ^ (prefixWord ++ tailWord_265834).sum := by decide
  have hdescent : baseEnd_265834 < baseStart_265834 := by decide
  rcases family_descends (prefixWord ++ tailWord_265834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265879 : List Nat := [1, 1, 3, 3, 2, 3, 2, 1, 4]
def baseStart_265879 : Nat := 118140960795 + 265879 * 2 ^ 59
def prefixEnd_265879 : Nat := 4983230072969 + 3 ^ 40 * 265879 * 2
def baseEnd_265879 : Nat := 121354420388329316346445

theorem tailTrace_265879 : CollatzResearch.WordTrace tailWord_265879 prefixEnd_265879 121354420388329316346445 := by
  unfold tailWord_265879
  simp only [CollatzResearch.WordTrace]
  refine ⟨9697403803773266363152691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6464935869182177575435127 9697403803773266363152691)
  ·
    refine ⟨14546105705659899544729037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9697403803773266363152691 14546105705659899544729037)
    ·
      refine ⟨5454789639622462329273389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14546105705659899544729037 5454789639622462329273389)
      ·
        refine ⟨2045546114858423373477521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5454789639622462329273389 2045546114858423373477521)
        ·
          refine ⟨1534159586143817530108141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2045546114858423373477521 1534159586143817530108141)
          ·
            refine ⟨575309844803931573790553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1534159586143817530108141 575309844803931573790553)
            ·
              refine ⟨431482383602948680342915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575309844803931573790553 431482383602948680342915)
              ·
                refine ⟨647223575404423020514373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 431482383602948680342915 647223575404423020514373)
                ·
                  refine ⟨121354420388329316346445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 647223575404423020514373 121354420388329316346445)
                  ·
                    rfl

theorem cell20_265879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 4].length) (baseStart_265879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265879 prefixEnd_265879 := by exact prefixLift 265879
  have htrace : WordTrace (prefixWord ++ tailWord_265879) baseStart_265879 baseEnd_265879 := by
    simpa [prefixWord, tailWord_265879, baseEnd_265879] using wordTrace_append hprefix tailTrace_265879
  have hstable : (prefixWord ++ tailWord_265879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265879).length < 2 ^ (prefixWord ++ tailWord_265879).sum := by decide
  have hdescent : baseEnd_265879 < baseStart_265879 := by decide
  rcases family_descends (prefixWord ++ tailWord_265879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265889 : List Nat := [1, 2, 3, 3, 2, 2, 3, 1, 3]
def baseStart_265889 : Nat := 118140960795 + 265889 * 2 ^ 59
def prefixEnd_265889 : Nat := 4983230072969 + 3 ^ 40 * 265889 * 2
def baseEnd_265889 : Nat := 121358984660813726013071

theorem tailTrace_265889 : CollatzResearch.WordTrace tailWord_265889 prefixEnd_265889 121358984660813726013071 := by
  unfold tailWord_265889
  simp only [CollatzResearch.WordTrace]
  refine ⟨9697768533737038071016721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6465179022491358714011147 9697768533737038071016721)
  ·
    refine ⟨7273326400302778553262541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9697768533737038071016721 7273326400302778553262541)
    ·
      refine ⟨2727497400113541957473453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7273326400302778553262541 2727497400113541957473453)
      ·
        refine ⟨1022811525042578234052545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2727497400113541957473453 1022811525042578234052545)
        ·
          refine ⟨767108643781933675539409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1022811525042578234052545 767108643781933675539409)
          ·
            refine ⟨575331482836450256654557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 767108643781933675539409 575331482836450256654557)
            ·
              refine ⟨215749306063668846245459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 575331482836450256654557 215749306063668846245459)
              ·
                refine ⟨323623959095503269368189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215749306063668846245459 323623959095503269368189)
                ·
                  refine ⟨121358984660813726013071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323623959095503269368189 121358984660813726013071)
                  ·
                    rfl

theorem cell20_265889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 3].length) (baseStart_265889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265889 prefixEnd_265889 := by exact prefixLift 265889
  have htrace : WordTrace (prefixWord ++ tailWord_265889) baseStart_265889 baseEnd_265889 := by
    simpa [prefixWord, tailWord_265889, baseEnd_265889] using wordTrace_append hprefix tailTrace_265889
  have hstable : (prefixWord ++ tailWord_265889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265889).length < 2 ^ (prefixWord ++ tailWord_265889).sum := by decide
  have hdescent : baseEnd_265889 < baseStart_265889 := by decide
  rcases family_descends (prefixWord ++ tailWord_265889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265893 : List Nat := [1, 3, 1, 2, 1, 2, 2, 5, 3]
def baseStart_265893 : Nat := 118140960795 + 265893 * 2 ^ 59
def prefixEnd_265893 : Nat := 4983230072969 + 3 ^ 40 * 265893 * 2
def baseEnd_265893 : Nat := 121360810369807489879721

theorem tailTrace_265893 : CollatzResearch.WordTrace tailWord_265893 prefixEnd_265893 121360810369807489879721 := by
  unfold tailWord_265893
  simp only [CollatzResearch.WordTrace]
  refine ⟨9697914425722546754162333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6465276283815031169441555 9697914425722546754162333)
  ·
    refine ⟨3636717909645955032810875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9697914425722546754162333 3636717909645955032810875)
    ·
      refine ⟨5455076864468932549216313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3636717909645955032810875 5455076864468932549216313)
      ·
        refine ⟨4091307648351699411912235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5455076864468932549216313 4091307648351699411912235)
        ·
          refine ⟨6136961472527549117868353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4091307648351699411912235 6136961472527549117868353)
          ·
            refine ⟨4602721104395661838401265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6136961472527549117868353 4602721104395661838401265)
            ·
              refine ⟨3452040828296746378800949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4602721104395661838401265 3452040828296746378800949)
              ·
                refine ⟨323628827652819973012589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3452040828296746378800949 323628827652819973012589)
                ·
                  refine ⟨121360810369807489879721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323628827652819973012589 121360810369807489879721)
                  ·
                    rfl

theorem cell20_265893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_265893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265893 prefixEnd_265893 := by exact prefixLift 265893
  have htrace : WordTrace (prefixWord ++ tailWord_265893) baseStart_265893 baseEnd_265893 := by
    simpa [prefixWord, tailWord_265893, baseEnd_265893] using wordTrace_append hprefix tailTrace_265893
  have hstable : (prefixWord ++ tailWord_265893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265893).length < 2 ^ (prefixWord ++ tailWord_265893).sum := by decide
  have hdescent : baseEnd_265893 < baseStart_265893 := by decide
  rcases family_descends (prefixWord ++ tailWord_265893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265907 : List Nat := [1, 1, 1, 2, 3, 3, 3, 6]
def baseStart_265907 : Nat := 118140960795 + 265907 * 2 ^ 59
def prefixEnd_265907 : Nat := 4983230072969 + 3 ^ 40 * 265907 * 2
def baseEnd_265907 : Nat := 40455733450428554470999

theorem tailTrace_265907 : CollatzResearch.WordTrace tailWord_265907 prefixEnd_265907 40455733450428554470999 := by
  unfold tailWord_265907
  simp only [CollatzResearch.WordTrace]
  refine ⟨9698425047671827145171975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6465616698447884763447983 9698425047671827145171975)
  ·
    refine ⟨14547637571507740717757963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9698425047671827145171975 14547637571507740717757963)
    ·
      refine ⟨21821456357261611076636945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14547637571507740717757963 21821456357261611076636945)
      ·
        refine ⟨16366092267946208307477709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21821456357261611076636945 16366092267946208307477709)
        ·
          refine ⟨6137284600479828115304141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16366092267946208307477709 6137284600479828115304141)
          ·
            refine ⟨2301481725179935543239053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6137284600479828115304141 2301481725179935543239053)
            ·
              refine ⟨863055646942475828714645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2301481725179935543239053 863055646942475828714645)
              ·
                refine ⟨40455733450428554470999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 863055646942475828714645 40455733450428554470999)
                ·
                  rfl

theorem cell20_265907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 6].length) (baseStart_265907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265907 prefixEnd_265907 := by exact prefixLift 265907
  have htrace : WordTrace (prefixWord ++ tailWord_265907) baseStart_265907 baseEnd_265907 := by
    simpa [prefixWord, tailWord_265907, baseEnd_265907] using wordTrace_append hprefix tailTrace_265907
  have hstable : (prefixWord ++ tailWord_265907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265907).length < 2 ^ (prefixWord ++ tailWord_265907).sum := by decide
  have hdescent : baseEnd_265907 < baseStart_265907 := by decide
  rcases family_descends (prefixWord ++ tailWord_265907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_265945 : List Nat := [1, 2, 1, 2, 3, 3, 1, 7]
def baseStart_265945 : Nat := 118140960795 + 265945 * 2 ^ 59
def prefixEnd_265945 : Nat := 4983230072969 + 3 ^ 40 * 265945 * 2
def baseEnd_265945 : Nat := 40461514862242140048725

theorem tailTrace_265945 : CollatzResearch.WordTrace tailWord_265945 prefixEnd_265945 40461514862242140048725 := by
  unfold tailWord_265945
  simp only [CollatzResearch.WordTrace]
  refine ⟨9699811021534159635055289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6466540681022773090036859 9699811021534159635055289)
  ·
    refine ⟨7274858266150619726291467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9699811021534159635055289 7274858266150619726291467)
    ·
      refine ⟨10912287399225929589437201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7274858266150619726291467 10912287399225929589437201)
      ·
        refine ⟨8184215549419447192077901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10912287399225929589437201 8184215549419447192077901)
        ·
          refine ⟨3069080831032292697029213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8184215549419447192077901 3069080831032292697029213)
          ·
            refine ⟨1150905311637109761385955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3069080831032292697029213 1150905311637109761385955)
            ·
              refine ⟨1726357967455664642078933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1150905311637109761385955 1726357967455664642078933)
              ·
                refine ⟨40461514862242140048725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1726357967455664642078933 40461514862242140048725)
                ·
                  rfl

theorem cell20_265945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 7].length) (baseStart_265945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_265945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_265945 prefixEnd_265945 := by exact prefixLift 265945
  have htrace : WordTrace (prefixWord ++ tailWord_265945) baseStart_265945 baseEnd_265945 := by
    simpa [prefixWord, tailWord_265945, baseEnd_265945] using wordTrace_append hprefix tailTrace_265945
  have hstable : (prefixWord ++ tailWord_265945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_265945).length < 2 ^ (prefixWord ++ tailWord_265945).sum := by decide
  have hdescent : baseEnd_265945 < baseStart_265945 := by decide
  rcases family_descends (prefixWord ++ tailWord_265945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266113 : List Nat := [1, 2, 4, 4, 2, 1, 2, 1, 3]
def baseStart_266113 : Nat := 118140960795 + 266113 * 2 ^ 59
def prefixEnd_266113 : Nat := 4983230072969 + 3 ^ 40 * 266113 * 2
def baseEnd_266113 : Nat := 121461224364464502545489

theorem tailTrace_266113 : CollatzResearch.WordTrace tailWord_266113 prefixEnd_266113 121461224364464502545489 := by
  unfold tailWord_266113
  simp only [CollatzResearch.WordTrace]
  refine ⟨9705938484925524327170993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6470625656617016218113995 9705938484925524327170993)
  ·
    refine ⟨7279453863694143245378245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9705938484925524327170993 7279453863694143245378245)
    ·
      refine ⟨1364897599442651858508421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7279453863694143245378245 1364897599442651858508421)
      ·
        refine ⟨255918299895497223470329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1364897599442651858508421 255918299895497223470329)
        ·
          refine ⟨191938724921622917602747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255918299895497223470329 191938724921622917602747)
          ·
            refine ⟨287908087382434376404121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191938724921622917602747 287908087382434376404121)
            ·
              refine ⟨215931065536825782303091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287908087382434376404121 215931065536825782303091)
              ·
                refine ⟨323896598305238673454637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215931065536825782303091 323896598305238673454637)
                ·
                  refine ⟨121461224364464502545489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323896598305238673454637 121461224364464502545489)
                  ·
                    rfl

theorem cell20_266113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 2, 1, 3].length) (baseStart_266113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266113 prefixEnd_266113 := by exact prefixLift 266113
  have htrace : WordTrace (prefixWord ++ tailWord_266113) baseStart_266113 baseEnd_266113 := by
    simpa [prefixWord, tailWord_266113, baseEnd_266113] using wordTrace_append hprefix tailTrace_266113
  have hstable : (prefixWord ++ tailWord_266113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266113).length < 2 ^ (prefixWord ++ tailWord_266113).sum := by decide
  have hdescent : baseEnd_266113 < baseStart_266113 := by decide
  rcases family_descends (prefixWord ++ tailWord_266113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266121 : List Nat := [1, 2, 1, 1, 5, 1, 3, 3, 3]
def baseStart_266121 : Nat := 118140960795 + 266121 * 2 ^ 59
def prefixEnd_266121 : Nat := 4983230072969 + 3 ^ 40 * 266121 * 2
def baseEnd_266121 : Nat := 121464875782452030278789

theorem tailTrace_266121 : CollatzResearch.WordTrace tailWord_266121 prefixEnd_266121 121464875782452030278789 := by
  unfold tailWord_266121
  simp only [CollatzResearch.WordTrace]
  refine ⟨9706230268896541693462217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6470820179264361128974811 9706230268896541693462217)
  ·
    refine ⟨7279672701672406270096663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9706230268896541693462217 7279672701672406270096663)
    ·
      refine ⟨10919509052508609405144995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7279672701672406270096663 10919509052508609405144995)
      ·
        refine ⟨16379263578762914107717493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10919509052508609405144995 16379263578762914107717493)
        ·
          refine ⟨1535555960509023197598515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16379263578762914107717493 1535555960509023197598515)
          ·
            refine ⟨2303333940763534796397773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1535555960509023197598515 2303333940763534796397773)
            ·
              refine ⟨863750227786325548649165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2303333940763534796397773 863750227786325548649165)
              ·
                refine ⟨323906335419872080743437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 863750227786325548649165 323906335419872080743437)
                ·
                  refine ⟨121464875782452030278789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323906335419872080743437 121464875782452030278789)
                  ·
                    rfl

theorem cell20_266121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_266121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266121 prefixEnd_266121 := by exact prefixLift 266121
  have htrace : WordTrace (prefixWord ++ tailWord_266121) baseStart_266121 baseEnd_266121 := by
    simpa [prefixWord, tailWord_266121, baseEnd_266121] using wordTrace_append hprefix tailTrace_266121
  have hstable : (prefixWord ++ tailWord_266121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266121).length < 2 ^ (prefixWord ++ tailWord_266121).sum := by decide
  have hdescent : baseEnd_266121 < baseStart_266121 := by decide
  rcases family_descends (prefixWord ++ tailWord_266121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266135 : List Nat := [1, 1, 3, 3, 1, 3, 2, 6]
def baseStart_266135 : Nat := 118140960795 + 266135 * 2 ^ 59
def prefixEnd_266135 : Nat := 4983230072969 + 3 ^ 40 * 266135 * 2
def baseEnd_266135 : Nat := 40490421921310067937355

theorem tailTrace_266135 : CollatzResearch.WordTrace tailWord_266135 prefixEnd_266135 40490421921310067937355 := by
  unfold tailWord_266135
  simp only [CollatzResearch.WordTrace]
  refine ⟨9706740890845822084471859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6471160593897214722981239 9706740890845822084471859)
  ·
    refine ⟨14560111336268733126707789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9706740890845822084471859 14560111336268733126707789)
    ·
      refine ⟨5460041751100774922515421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14560111336268733126707789 5460041751100774922515421)
      ·
        refine ⟨2047515656662790595943283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5460041751100774922515421 2047515656662790595943283)
        ·
          refine ⟨3071273484994185893914925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2047515656662790595943283 3071273484994185893914925)
          ·
            refine ⟨1151727556872819710218097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3071273484994185893914925 1151727556872819710218097)
            ·
              refine ⟨863795667654614782663573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1151727556872819710218097 863795667654614782663573)
              ·
                refine ⟨40490421921310067937355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 863795667654614782663573 40490421921310067937355)
                ·
                  rfl

theorem cell20_266135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 6].length) (baseStart_266135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266135 prefixEnd_266135 := by exact prefixLift 266135
  have htrace : WordTrace (prefixWord ++ tailWord_266135) baseStart_266135 baseEnd_266135 := by
    simpa [prefixWord, tailWord_266135, baseEnd_266135] using wordTrace_append hprefix tailTrace_266135
  have hstable : (prefixWord ++ tailWord_266135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266135).length < 2 ^ (prefixWord ++ tailWord_266135).sum := by decide
  have hdescent : baseEnd_266135 < baseStart_266135 := by decide
  rcases family_descends (prefixWord ++ tailWord_266135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266152 : List Nat := [2, 1, 6, 2, 9]
def baseStart_266152 : Nat := 118140960795 + 266152 * 2 ^ 59
def prefixEnd_266152 : Nat := 4983230072969 + 3 ^ 40 * 266152 * 2
def baseEnd_266152 : Nat := 1499741049717946916609

theorem tailTrace_266152 : CollatzResearch.WordTrace tailWord_266152 prefixEnd_266152 1499741049717946916609 := by
  unfold tailWord_266152
  simp only [CollatzResearch.WordTrace]
  refine ⟨4853680465892116993920355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6471573954522822658560473 4853680465892116993920355)
  ·
    refine ⟨7280520698838175490880533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4853680465892116993920355 7280520698838175490880533)
    ·
      refine ⟨341274407758039476135025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7280520698838175490880533 341274407758039476135025)
      ·
        refine ⟨255955805818529607101269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 341274407758039476135025 255955805818529607101269)
        ·
          refine ⟨1499741049717946916609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 255955805818529607101269 1499741049717946916609)
          ·
            rfl

theorem cell20_266152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 9].length) (baseStart_266152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266152 prefixEnd_266152 := by exact prefixLift 266152
  have htrace : WordTrace (prefixWord ++ tailWord_266152) baseStart_266152 baseEnd_266152 := by
    simpa [prefixWord, tailWord_266152, baseEnd_266152] using wordTrace_append hprefix tailTrace_266152
  have hstable : (prefixWord ++ tailWord_266152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266152).length < 2 ^ (prefixWord ++ tailWord_266152).sum := by decide
  have hdescent : baseEnd_266152 < baseStart_266152 := by decide
  rcases family_descends (prefixWord ++ tailWord_266152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266159 : List Nat := [1, 1, 2, 1, 2, 2, 6, 2, 3]
def baseStart_266159 : Nat := 118140960795 + 266159 * 2 ^ 59
def prefixEnd_266159 : Nat := 4983230072969 + 3 ^ 40 * 266159 * 2
def baseEnd_266159 : Nat := 121482220017892787011967

theorem tailTrace_266159 : CollatzResearch.WordTrace tailWord_266159 prefixEnd_266159 121482220017892787011967 := by
  unfold tailWord_266159
  simp only [CollatzResearch.WordTrace]
  refine ⟨9707616242758874183345531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6471744161839249455563687 9707616242758874183345531)
  ·
    refine ⟨14561424364138311275018297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9707616242758874183345531 14561424364138311275018297)
    ·
      refine ⟨10921068273103733456263723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14561424364138311275018297 10921068273103733456263723)
      ·
        refine ⟨16381602409655600184395585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10921068273103733456263723 16381602409655600184395585)
        ·
          refine ⟨12286201807241700138296689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16381602409655600184395585 12286201807241700138296689)
          ·
            refine ⟨9214651355431275103722517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12286201807241700138296689 9214651355431275103722517)
            ·
              refine ⟨431936782285841020486993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 9214651355431275103722517 431936782285841020486993)
              ·
                refine ⟨323952586714380765365245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431936782285841020486993 323952586714380765365245)
                ·
                  refine ⟨121482220017892787011967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 323952586714380765365245 121482220017892787011967)
                  ·
                    rfl

theorem cell20_266159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 3].length) (baseStart_266159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266159 prefixEnd_266159 := by exact prefixLift 266159
  have htrace : WordTrace (prefixWord ++ tailWord_266159) baseStart_266159 baseEnd_266159 := by
    simpa [prefixWord, tailWord_266159, baseEnd_266159] using wordTrace_append hprefix tailTrace_266159
  have hstable : (prefixWord ++ tailWord_266159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266159).length < 2 ^ (prefixWord ++ tailWord_266159).sum := by decide
  have hdescent : baseEnd_266159 < baseStart_266159 := by decide
  rcases family_descends (prefixWord ++ tailWord_266159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266190 : List Nat := [4, 1, 1, 1, 2, 2, 5, 4]
def baseStart_266190 : Nat := 118140960795 + 266190 * 2 ^ 59
def prefixEnd_266190 : Nat := 4983230072969 + 3 ^ 40 * 266190 * 2
def baseEnd_266190 : Nat := 40498789754198152326169

theorem tailTrace_266190 : CollatzResearch.WordTrace tailWord_266190 prefixEnd_266190 40498789754198152326169 := by
  unfold tailWord_266190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1213593363205820809715503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6472497937097710985149349 1213593363205820809715503)
  ·
    refine ⟨1820390044808731214573255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1213593363205820809715503 1820390044808731214573255)
    ·
      refine ⟨2730585067213096821859883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1820390044808731214573255 2730585067213096821859883)
      ·
        refine ⟨4095877600819645232789825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2730585067213096821859883 4095877600819645232789825)
        ·
          refine ⟨3071908200614733924592369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4095877600819645232789825 3071908200614733924592369)
          ·
            refine ⟨2303931150461050443444277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3071908200614733924592369 2303931150461050443444277)
            ·
              refine ⟨215993545355723479072901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2303931150461050443444277 215993545355723479072901)
              ·
                refine ⟨40498789754198152326169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215993545355723479072901 40498789754198152326169)
                ·
                  rfl

theorem cell20_266190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_266190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266190 prefixEnd_266190 := by exact prefixLift 266190
  have htrace : WordTrace (prefixWord ++ tailWord_266190) baseStart_266190 baseEnd_266190 := by
    simpa [prefixWord, tailWord_266190, baseEnd_266190] using wordTrace_append hprefix tailTrace_266190
  have hstable : (prefixWord ++ tailWord_266190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266190).length < 2 ^ (prefixWord ++ tailWord_266190).sum := by decide
  have hdescent : baseEnd_266190 < baseStart_266190 := by decide
  rcases family_descends (prefixWord ++ tailWord_266190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266210 : List Nat := [3, 3, 3, 1, 2, 2, 1, 2, 3]
def baseStart_266210 : Nat := 118140960795 + 266210 * 2 ^ 59
def prefixEnd_266210 : Nat := 4983230072969 + 3 ^ 40 * 266210 * 2
def baseEnd_266210 : Nat := 121505497807563276311759

theorem tailTrace_266210 : CollatzResearch.WordTrace tailWord_266210 prefixEnd_266210 121505497807563276311759 := by
  unfold tailWord_266210
  simp only [CollatzResearch.WordTrace]
  refine ⟨2427369091393527473363021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6472984243716073262301389 2427369091393527473363021)
  ·
    refine ⟨910263409272572802511133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2427369091393527473363021 910263409272572802511133)
    ·
      refine ⟨341348778477214800941675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 910263409272572802511133 341348778477214800941675)
      ·
        refine ⟨512023167715822201412513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 341348778477214800941675 512023167715822201412513)
        ·
          refine ⟨384017375786866651059385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512023167715822201412513 384017375786866651059385)
          ·
            refine ⟨288013031840149988294539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384017375786866651059385 288013031840149988294539)
            ·
              refine ⟨432019547760224982441809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288013031840149988294539 432019547760224982441809)
              ·
                refine ⟨324014660820168736831357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432019547760224982441809 324014660820168736831357)
                ·
                  refine ⟨121505497807563276311759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324014660820168736831357 121505497807563276311759)
                  ·
                    rfl

theorem cell20_266210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_266210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266210 prefixEnd_266210 := by exact prefixLift 266210
  have htrace : WordTrace (prefixWord ++ tailWord_266210) baseStart_266210 baseEnd_266210 := by
    simpa [prefixWord, tailWord_266210, baseEnd_266210] using wordTrace_append hprefix tailTrace_266210
  have hstable : (prefixWord ++ tailWord_266210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266210).length < 2 ^ (prefixWord ++ tailWord_266210).sum := by decide
  have hdescent : baseEnd_266210 < baseStart_266210 := by decide
  rcases family_descends (prefixWord ++ tailWord_266210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266211 : List Nat := [1, 1, 1, 6, 1, 3, 7]
def baseStart_266211 : Nat := 118140960795 + 266211 * 2 ^ 59
def prefixEnd_266211 : Nat := 4983230072969 + 3 ^ 40 * 266211 * 2
def baseEnd_266211 : Nat := 13500661581645746364269

theorem tailTrace_266211 : CollatzResearch.WordTrace tailWord_266211 prefixEnd_266211 13500661581645746364269 := by
  unfold tailWord_266211
  simp only [CollatzResearch.WordTrace]
  refine ⟨9709512838570487064238487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6473008559046991376158991 9709512838570487064238487)
  ·
    refine ⟨14564269257855730596357731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9709512838570487064238487 14564269257855730596357731)
    ·
      refine ⟨21846403886783595894536597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14564269257855730596357731 21846403886783595894536597)
      ·
        refine ⟨1024050182192981057556403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21846403886783595894536597 1024050182192981057556403)
        ·
          refine ⟨1536075273289471586334605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1024050182192981057556403 1536075273289471586334605)
          ·
            refine ⟨576028227483551844875477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1536075273289471586334605 576028227483551844875477)
            ·
              refine ⟨13500661581645746364269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 576028227483551844875477 13500661581645746364269)
              ·
                rfl

theorem cell20_266211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 7].length) (baseStart_266211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266211 prefixEnd_266211 := by exact prefixLift 266211
  have htrace : WordTrace (prefixWord ++ tailWord_266211) baseStart_266211 baseEnd_266211 := by
    simpa [prefixWord, tailWord_266211, baseEnd_266211] using wordTrace_append hprefix tailTrace_266211
  have hstable : (prefixWord ++ tailWord_266211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266211).length < 2 ^ (prefixWord ++ tailWord_266211).sum := by decide
  have hdescent : baseEnd_266211 < baseStart_266211 := by decide
  rcases family_descends (prefixWord ++ tailWord_266211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266259 : List Nat := [1, 1, 1, 2, 1, 4, 5, 3, 2]
def baseStart_266259 : Nat := 118140960795 + 266259 * 2 ^ 59
def prefixEnd_266259 : Nat := 4983230072969 + 3 ^ 40 * 266259 * 2
def baseEnd_266259 : Nat := 121527862742736883678225

theorem tailTrace_266259 : CollatzResearch.WordTrace tailWord_266259 prefixEnd_266259 121527862742736883678225 := by
  unfold tailWord_266259
  simp only [CollatzResearch.WordTrace]
  refine ⟨9711263542396591261985831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6474175694931060841323887 9711263542396591261985831)
  ·
    refine ⟨14566895313594886892978747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9711263542396591261985831 14566895313594886892978747)
    ·
      refine ⟨21850342970392330339468121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14566895313594886892978747 21850342970392330339468121)
      ·
        refine ⟨16387757227794247754601091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21850342970392330339468121 16387757227794247754601091)
        ·
          refine ⟨24581635841691371631901637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16387757227794247754601091 24581635841691371631901637)
          ·
            refine ⟨4609056720317132180981557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24581635841691371631901637 4609056720317132180981557)
            ·
              refine ⟨432099067529731141967021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4609056720317132180981557 432099067529731141967021)
              ·
                refine ⟨162037150323649178237633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 432099067529731141967021 162037150323649178237633)
                ·
                  refine ⟨121527862742736883678225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162037150323649178237633 121527862742736883678225)
                  ·
                    rfl

theorem cell20_266259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 2].length) (baseStart_266259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266259 prefixEnd_266259 := by exact prefixLift 266259
  have htrace : WordTrace (prefixWord ++ tailWord_266259) baseStart_266259 baseEnd_266259 := by
    simpa [prefixWord, tailWord_266259, baseEnd_266259] using wordTrace_append hprefix tailTrace_266259
  have hstable : (prefixWord ++ tailWord_266259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266259).length < 2 ^ (prefixWord ++ tailWord_266259).sum := by decide
  have hdescent : baseEnd_266259 < baseStart_266259 := by decide
  rcases family_descends (prefixWord ++ tailWord_266259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266276 : List Nat := [2, 3, 1, 4, 2, 2, 1, 1, 4]
def baseStart_266276 : Nat := 118140960795 + 266276 * 2 ^ 59
def prefixEnd_266276 : Nat := 4983230072969 + 3 ^ 40 * 266276 * 2
def baseEnd_266276 : Nat := 121535622005960380111489

theorem tailTrace_266276 : CollatzResearch.WordTrace tailWord_266276 prefixEnd_266276 121535622005960380111489 := by
  unfold tailWord_266276
  simp only [CollatzResearch.WordTrace]
  refine ⟨4855941791667501582677341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6474589055556668776903121 4855941791667501582677341)
  ·
    refine ⟨1820978171875313093504003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4855941791667501582677341 1820978171875313093504003)
    ·
      refine ⟨2731467257812969640256005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1820978171875313093504003 2731467257812969640256005)
      ·
        refine ⟨512150110839931807548001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2731467257812969640256005 512150110839931807548001)
        ·
          refine ⟨384112583129948855661001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512150110839931807548001 384112583129948855661001)
          ·
            refine ⟨288084437347461641745751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384112583129948855661001 288084437347461641745751)
            ·
              refine ⟨432126656021192462618627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288084437347461641745751 432126656021192462618627)
              ·
                refine ⟨648189984031788693927941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432126656021192462618627 648189984031788693927941)
                ·
                  refine ⟨121535622005960380111489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 648189984031788693927941 121535622005960380111489)
                  ·
                    rfl

theorem cell20_266276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_266276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266276 prefixEnd_266276 := by exact prefixLift 266276
  have htrace : WordTrace (prefixWord ++ tailWord_266276) baseStart_266276 baseEnd_266276 := by
    simpa [prefixWord, tailWord_266276, baseEnd_266276] using wordTrace_append hprefix tailTrace_266276
  have hstable : (prefixWord ++ tailWord_266276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266276).length < 2 ^ (prefixWord ++ tailWord_266276).sum := by decide
  have hdescent : baseEnd_266276 < baseStart_266276 := by decide
  rcases family_descends (prefixWord ++ tailWord_266276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266290 : List Nat := [3, 2, 1, 1, 2, 3, 4, 1, 3]
def baseStart_266290 : Nat := 118140960795 + 266290 * 2 ^ 59
def prefixEnd_266290 : Nat := 4983230072969 + 3 ^ 40 * 266290 * 2
def baseEnd_266290 : Nat := 121542011987438553644765

theorem tailTrace_266290 : CollatzResearch.WordTrace tailWord_266290 prefixEnd_266290 121542011987438553644765 := by
  unfold tailWord_266290
  simp only [CollatzResearch.WordTrace]
  refine ⟨2428098551321070889091081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6474929470189522370909549 2428098551321070889091081)
  ·
    refine ⟨1821073913490803166818311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2428098551321070889091081 1821073913490803166818311)
    ·
      refine ⟨2731610870236204750227467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1821073913490803166818311 2731610870236204750227467)
      ·
        refine ⟨4097416305354307125341201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2731610870236204750227467 4097416305354307125341201)
        ·
          refine ⟨3073062229015730344005901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4097416305354307125341201 3073062229015730344005901)
          ·
            refine ⟨1152398335880898879002213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3073062229015730344005901 1152398335880898879002213)
            ·
              refine ⟨216074687977668539812915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1152398335880898879002213 216074687977668539812915)
              ·
                refine ⟨324112031966502809719373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216074687977668539812915 324112031966502809719373)
                ·
                  refine ⟨121542011987438553644765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324112031966502809719373 121542011987438553644765)
                  ·
                    rfl

theorem cell20_266290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_266290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266290 prefixEnd_266290 := by exact prefixLift 266290
  have htrace : WordTrace (prefixWord ++ tailWord_266290) baseStart_266290 baseEnd_266290 := by
    simpa [prefixWord, tailWord_266290, baseEnd_266290] using wordTrace_append hprefix tailTrace_266290
  have hstable : (prefixWord ++ tailWord_266290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266290).length < 2 ^ (prefixWord ++ tailWord_266290).sum := by decide
  have hdescent : baseEnd_266290 < baseStart_266290 := by decide
  rcases family_descends (prefixWord ++ tailWord_266290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266338 : List Nat := [3, 3, 2, 2, 3, 1, 1, 5]
def baseStart_266338 : Nat := 118140960795 + 266338 * 2 ^ 59
def prefixEnd_266338 : Nat := 4983230072969 + 3 ^ 40 * 266338 * 2
def baseEnd_266338 : Nat := 40521306831787906681523

theorem tailTrace_266338 : CollatzResearch.WordTrace tailWord_266338 prefixEnd_266338 40521306831787906681523 := by
  unfold tailWord_266338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2428536227277596938527917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6476096606073591836074445 2428536227277596938527917)
  ·
    refine ⟨910701085229098851947969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2428536227277596938527917 910701085229098851947969)
    ·
      refine ⟨683025813921824138960977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 910701085229098851947969 683025813921824138960977)
      ·
        refine ⟨512269360441368104220733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 683025813921824138960977 512269360441368104220733)
        ·
          refine ⟨192101010165513039082775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 512269360441368104220733 192101010165513039082775)
          ·
            refine ⟨288151515248269558624163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192101010165513039082775 288151515248269558624163)
            ·
              refine ⟨432227272872404337936245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288151515248269558624163 432227272872404337936245)
              ·
                refine ⟨40521306831787906681523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 432227272872404337936245 40521306831787906681523)
                ·
                  rfl

theorem cell20_266338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_266338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266338 prefixEnd_266338 := by exact prefixLift 266338
  have htrace : WordTrace (prefixWord ++ tailWord_266338) baseStart_266338 baseEnd_266338 := by
    simpa [prefixWord, tailWord_266338, baseEnd_266338] using wordTrace_append hprefix tailTrace_266338
  have hstable : (prefixWord ++ tailWord_266338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266338).length < 2 ^ (prefixWord ++ tailWord_266338).sum := by decide
  have hdescent : baseEnd_266338 < baseStart_266338 := by decide
  rcases family_descends (prefixWord ++ tailWord_266338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266349 : List Nat := [1, 5, 1, 1, 2, 1, 1, 5, 3]
def baseStart_266349 : Nat := 118140960795 + 266349 * 2 ^ 59
def prefixEnd_266349 : Nat := 4983230072969 + 3 ^ 40 * 266349 * 2
def baseEnd_266349 : Nat := 121568941195096570677857

theorem tailTrace_266349 : CollatzResearch.WordTrace tailWord_266349 prefixEnd_266349 121568941195096570677857 := by
  unfold tailWord_266349
  simp only [CollatzResearch.WordTrace]
  refine ⟨9714546112070536632762101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6476364074713691088508067 9714546112070536632762101)
  ·
    refine ⟨910738698006612809321447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9714546112070536632762101 910738698006612809321447)
    ·
      refine ⟨1366108047009919213982171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 910738698006612809321447 1366108047009919213982171)
      ·
        refine ⟨2049162070514878820973257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1366108047009919213982171 2049162070514878820973257)
        ·
          refine ⟨1536871552886159115729943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2049162070514878820973257 1536871552886159115729943)
          ·
            refine ⟨2305307329329238673594915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1536871552886159115729943 2305307329329238673594915)
            ·
              refine ⟨3457960993993858010392373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2305307329329238673594915 3457960993993858010392373)
              ·
                refine ⟨324183843186924188474285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3457960993993858010392373 324183843186924188474285)
                ·
                  refine ⟨121568941195096570677857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324183843186924188474285 121568941195096570677857)
                  ·
                    rfl

theorem cell20_266349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_266349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266349 prefixEnd_266349 := by exact prefixLift 266349
  have htrace : WordTrace (prefixWord ++ tailWord_266349) baseStart_266349 baseEnd_266349 := by
    simpa [prefixWord, tailWord_266349, baseEnd_266349] using wordTrace_append hprefix tailTrace_266349
  have hstable : (prefixWord ++ tailWord_266349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266349).length < 2 ^ (prefixWord ++ tailWord_266349).sum := by decide
  have hdescent : baseEnd_266349 < baseStart_266349 := by decide
  rcases family_descends (prefixWord ++ tailWord_266349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266373 : List Nat := [1, 3, 1, 1, 5, 1, 1, 5, 2]
def baseStart_266373 : Nat := 118140960795 + 266373 * 2 ^ 59
def prefixEnd_266373 : Nat := 4983230072969 + 3 ^ 40 * 266373 * 2
def baseEnd_266373 : Nat := 121579895449059153877759

theorem tailTrace_266373 : CollatzResearch.WordTrace tailWord_266373 prefixEnd_266373 121579895449059153877759 := by
  unfold tailWord_266373
  simp only [CollatzResearch.WordTrace]
  refine ⟨9715421463983588731635773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6476947642655725821090515 9715421463983588731635773)
  ·
    refine ⟨3643283048993845774363415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9715421463983588731635773 3643283048993845774363415)
    ·
      refine ⟨5464924573490768661545123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3643283048993845774363415 5464924573490768661545123)
      ·
        refine ⟨8197386860236152992317685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5464924573490768661545123 8197386860236152992317685)
        ·
          refine ⟨768505018147139343029783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8197386860236152992317685 768505018147139343029783)
          ·
            refine ⟨1152757527220709014544675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768505018147139343029783 1152757527220709014544675)
            ·
              refine ⟨1729136290831063521817013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1152757527220709014544675 1729136290831063521817013)
              ·
                refine ⟨162106527265412205170345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1729136290831063521817013 162106527265412205170345)
                ·
                  refine ⟨121579895449059153877759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162106527265412205170345 121579895449059153877759)
                  ·
                    rfl

theorem cell20_266373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_266373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266373 prefixEnd_266373 := by exact prefixLift 266373
  have htrace : WordTrace (prefixWord ++ tailWord_266373) baseStart_266373 baseEnd_266373 := by
    simpa [prefixWord, tailWord_266373, baseEnd_266373] using wordTrace_append hprefix tailTrace_266373
  have hstable : (prefixWord ++ tailWord_266373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266373).length < 2 ^ (prefixWord ++ tailWord_266373).sum := by decide
  have hdescent : baseEnd_266373 < baseStart_266373 := by decide
  rcases family_descends (prefixWord ++ tailWord_266373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266377 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 6]
def baseStart_266377 : Nat := 118140960795 + 266377 * 2 ^ 59
def prefixEnd_266377 : Nat := 4983230072969 + 3 ^ 40 * 266377 * 2
def baseEnd_266377 : Nat := 121581721158052917744409

theorem tailTrace_266377 : CollatzResearch.WordTrace tailWord_266377 prefixEnd_266377 121581721158052917744409 := by
  unfold tailWord_266377
  simp only [CollatzResearch.WordTrace]
  refine ⟨9715567355969097414781385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6477044903979398276520923 9715567355969097414781385)
  ·
    refine ⟨7286675516976823061086039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9715567355969097414781385 7286675516976823061086039)
    ·
      refine ⟨10930013275465234591629059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7286675516976823061086039 10930013275465234591629059)
      ·
        refine ⟨16395019913197851887443589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10930013275465234591629059 16395019913197851887443589)
        ·
          refine ⟨3074066233724597228895673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16395019913197851887443589 3074066233724597228895673)
          ·
            refine ⟨2305549675293447921671755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3074066233724597228895673 2305549675293447921671755)
            ·
              refine ⟨3458324512940171882507633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2305549675293447921671755 3458324512940171882507633)
              ·
                refine ⟨2593743384705128911880725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3458324512940171882507633 2593743384705128911880725)
                ·
                  refine ⟨121581721158052917744409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2593743384705128911880725 121581721158052917744409)
                  ·
                    rfl

theorem cell20_266377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_266377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266377 prefixEnd_266377 := by exact prefixLift 266377
  have htrace : WordTrace (prefixWord ++ tailWord_266377) baseStart_266377 baseEnd_266377 := by
    simpa [prefixWord, tailWord_266377, baseEnd_266377] using wordTrace_append hprefix tailTrace_266377
  have hstable : (prefixWord ++ tailWord_266377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266377).length < 2 ^ (prefixWord ++ tailWord_266377).sum := by decide
  have hdescent : baseEnd_266377 < baseStart_266377 := by decide
  rcases family_descends (prefixWord ++ tailWord_266377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266384 : List Nat := [2, 1, 1, 1, 1, 1, 13]
def baseStart_266384 : Nat := 118140960795 + 266384 * 2 ^ 59
def prefixEnd_266384 : Nat := 4983230072969 + 3 ^ 40 * 266384 * 2
def baseEnd_266384 : Nat := 13509435127643556056783

theorem tailTrace_266384 : CollatzResearch.WordTrace tailWord_266384 prefixEnd_266384 13509435127643556056783 := by
  unfold tailWord_266384
  simp only [CollatzResearch.WordTrace]
  refine ⟨4857911333471868805143103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6477215111295825073524137 4857911333471868805143103)
  ·
    refine ⟨7286867000207803207714655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4857911333471868805143103 7286867000207803207714655)
    ·
      refine ⟨10930300500311704811571983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7286867000207803207714655 10930300500311704811571983)
      ·
        refine ⟨16395450750467557217357975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10930300500311704811571983 16395450750467557217357975)
        ·
          refine ⟨24593176125701335826036963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16395450750467557217357975 24593176125701335826036963)
          ·
            refine ⟨36889764188552003739055445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24593176125701335826036963 36889764188552003739055445)
            ·
              refine ⟨13509435127643556056783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 36889764188552003739055445 13509435127643556056783)
              ·
                rfl

theorem cell20_266384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 13].length) (baseStart_266384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266384 prefixEnd_266384 := by exact prefixLift 266384
  have htrace : WordTrace (prefixWord ++ tailWord_266384) baseStart_266384 baseEnd_266384 := by
    simpa [prefixWord, tailWord_266384, baseEnd_266384] using wordTrace_append hprefix tailTrace_266384
  have hstable : (prefixWord ++ tailWord_266384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266384).length < 2 ^ (prefixWord ++ tailWord_266384).sum := by decide
  have hdescent : baseEnd_266384 < baseStart_266384 := by decide
  rcases family_descends (prefixWord ++ tailWord_266384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266420 : List Nat := [2, 5, 3, 1, 2, 1, 1, 3, 2]
def baseStart_266420 : Nat := 118140960795 + 266420 * 2 ^ 59
def prefixEnd_266420 : Nat := 4983230072969 + 3 ^ 40 * 266420 * 2
def baseEnd_266420 : Nat := 121601347529735879310901

theorem tailTrace_266420 : CollatzResearch.WordTrace tailWord_266420 prefixEnd_266420 121601347529735879310901 := by
  unfold tailWord_266420
  simp only [CollatzResearch.WordTrace]
  refine ⟨4858567847406657879298357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6478090463208877172397809 4858567847406657879298357)
  ·
    refine ⟨455490735694374176184221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4858567847406657879298357 455490735694374176184221)
    ·
      refine ⟨170809025885390316069083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 455490735694374176184221 170809025885390316069083)
      ·
        refine ⟨256213538828085474103625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170809025885390316069083 256213538828085474103625)
        ·
          refine ⟨192160154121064105577719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 256213538828085474103625 192160154121064105577719)
          ·
            refine ⟨288240231181596158366579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192160154121064105577719 288240231181596158366579)
            ·
              refine ⟨432360346772394237549869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288240231181596158366579 432360346772394237549869)
              ·
                refine ⟨162135130039647839081201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 432360346772394237549869 162135130039647839081201)
                ·
                  refine ⟨121601347529735879310901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162135130039647839081201 121601347529735879310901)
                  ·
                    rfl

theorem cell20_266420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_266420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266420 prefixEnd_266420 := by exact prefixLift 266420
  have htrace : WordTrace (prefixWord ++ tailWord_266420) baseStart_266420 baseEnd_266420 := by
    simpa [prefixWord, tailWord_266420, baseEnd_266420] using wordTrace_append hprefix tailTrace_266420
  have hstable : (prefixWord ++ tailWord_266420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266420).length < 2 ^ (prefixWord ++ tailWord_266420).sum := by decide
  have hdescent : baseEnd_266420 < baseStart_266420 := by decide
  rcases family_descends (prefixWord ++ tailWord_266420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266500 : List Nat := [2, 3, 2, 2, 4, 1, 2, 2, 2]
def baseStart_266500 : Nat := 118140960795 + 266500 * 2 ^ 59
def prefixEnd_266500 : Nat := 4983230072969 + 3 ^ 40 * 266500 * 2
def baseEnd_266500 : Nat := 121637861709611156643907

theorem tailTrace_266500 : CollatzResearch.WordTrace tailWord_266500 prefixEnd_266500 121637861709611156643907 := by
  unfold tailWord_266500
  simp only [CollatzResearch.WordTrace]
  refine ⟨4860026767261744710754477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6480035689682326281005969 4860026767261744710754477)
  ·
    refine ⟨1822510037723154266532929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4860026767261744710754477 1822510037723154266532929)
    ·
      refine ⟨1366882528292365699899697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1822510037723154266532929 1366882528292365699899697)
      ·
        refine ⟨1025161896219274274924773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1366882528292365699899697 1025161896219274274924773)
        ·
          refine ⟨192217855541113926548395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1025161896219274274924773 192217855541113926548395)
          ·
            refine ⟨288326783311670889822593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192217855541113926548395 288326783311670889822593)
            ·
              refine ⟨216245087483753167366945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288326783311670889822593 216245087483753167366945)
              ·
                refine ⟨162183815612814875525209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216245087483753167366945 162183815612814875525209)
                ·
                  refine ⟨121637861709611156643907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162183815612814875525209 121637861709611156643907)
                  ·
                    rfl

theorem cell20_266500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_266500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266500 prefixEnd_266500 := by exact prefixLift 266500
  have htrace : WordTrace (prefixWord ++ tailWord_266500) baseStart_266500 baseEnd_266500 := by
    simpa [prefixWord, tailWord_266500, baseEnd_266500] using wordTrace_append hprefix tailTrace_266500
  have hstable : (prefixWord ++ tailWord_266500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266500).length < 2 ^ (prefixWord ++ tailWord_266500).sum := by decide
  have hdescent : baseEnd_266500 < baseStart_266500 := by decide
  rcases family_descends (prefixWord ++ tailWord_266500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266504 : List Nat := [2, 1, 3, 2, 3, 1, 4, 2, 2]
def baseStart_266504 : Nat := 118140960795 + 266504 * 2 ^ 59
def prefixEnd_266504 : Nat := 4983230072969 + 3 ^ 40 * 266504 * 2
def baseEnd_266504 : Nat := 121639687418604920510557

theorem tailTrace_266504 : CollatzResearch.WordTrace tailWord_266504 prefixEnd_266504 121639687418604920510557 := by
  unfold tailWord_266504
  simp only [CollatzResearch.WordTrace]
  refine ⟨4860099713254499052327283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6480132951005998736436377 4860099713254499052327283)
  ·
    refine ⟨7290149569881748578490925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4860099713254499052327283 7290149569881748578490925)
    ·
      refine ⟨2733806088705655716934097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7290149569881748578490925 2733806088705655716934097)
      ·
        refine ⟨2050354566529241787700573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2733806088705655716934097 2050354566529241787700573)
        ·
          refine ⟨768882962448465670387715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2050354566529241787700573 768882962448465670387715)
          ·
            refine ⟨1153324443672698505581573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768882962448465670387715 1153324443672698505581573)
            ·
              refine ⟨216248333188630969796545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1153324443672698505581573 216248333188630969796545)
              ·
                refine ⟨162186249891473227347409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216248333188630969796545 162186249891473227347409)
                ·
                  refine ⟨121639687418604920510557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162186249891473227347409 121639687418604920510557)
                  ·
                    rfl

theorem cell20_266504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 2].length) (baseStart_266504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266504 prefixEnd_266504 := by exact prefixLift 266504
  have htrace : WordTrace (prefixWord ++ tailWord_266504) baseStart_266504 baseEnd_266504 := by
    simpa [prefixWord, tailWord_266504, baseEnd_266504] using wordTrace_append hprefix tailTrace_266504
  have hstable : (prefixWord ++ tailWord_266504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266504).length < 2 ^ (prefixWord ++ tailWord_266504).sum := by decide
  have hdescent : baseEnd_266504 < baseStart_266504 := by decide
  rcases family_descends (prefixWord ++ tailWord_266504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266525 : List Nat := [1, 4, 2, 3, 2, 1, 1, 2, 4]
def baseStart_266525 : Nat := 118140960795 + 266525 * 2 ^ 59
def prefixEnd_266525 : Nat := 4983230072969 + 3 ^ 40 * 266525 * 2
def baseEnd_266525 : Nat := 121649272390822180810471

theorem tailTrace_266525 : CollatzResearch.WordTrace tailWord_266525 prefixEnd_266525 121649272390822180810471 := by
  unfold tailWord_266525
  simp only [CollatzResearch.WordTrace]
  refine ⟨9720965359432918691169029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6480643572955279127446019 9720965359432918691169029)
  ·
    refine ⟨1822681004893672254594193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9720965359432918691169029 1822681004893672254594193)
    ·
      refine ⟨1367010753670254190945645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1822681004893672254594193 1367010753670254190945645)
      ·
        refine ⟨512629032626345321604617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1367010753670254190945645 512629032626345321604617)
        ·
          refine ⟨384471774469758991203463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 512629032626345321604617 384471774469758991203463)
          ·
            refine ⟨576707661704638486805195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384471774469758991203463 576707661704638486805195)
            ·
              refine ⟨865061492556957730207793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 576707661704638486805195 865061492556957730207793)
              ·
                refine ⟨648796119417718297655845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 865061492556957730207793 648796119417718297655845)
                ·
                  refine ⟨121649272390822180810471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 648796119417718297655845 121649272390822180810471)
                  ·
                    rfl

theorem cell20_266525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_266525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266525 prefixEnd_266525 := by exact prefixLift 266525
  have htrace : WordTrace (prefixWord ++ tailWord_266525) baseStart_266525 baseEnd_266525 := by
    simpa [prefixWord, tailWord_266525, baseEnd_266525] using wordTrace_append hprefix tailTrace_266525
  have hstable : (prefixWord ++ tailWord_266525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266525).length < 2 ^ (prefixWord ++ tailWord_266525).sum := by decide
  have hdescent : baseEnd_266525 < baseStart_266525 := by decide
  rcases family_descends (prefixWord ++ tailWord_266525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266529 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 6]
def baseStart_266529 : Nat := 118140960795 + 266529 * 2 ^ 59
def prefixEnd_266529 : Nat := 4983230072969 + 3 ^ 40 * 266529 * 2
def baseEnd_266529 : Nat := 121651098099815944677121

theorem tailTrace_266529 : CollatzResearch.WordTrace tailWord_266529 prefixEnd_266529 121651098099815944677121 := by
  unfold tailWord_266529
  simp only [CollatzResearch.WordTrace]
  refine ⟨9721111251418427374314641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6480740834278951582876427 9721111251418427374314641)
  ·
    refine ⟨7290833438563820530735981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9721111251418427374314641 7290833438563820530735981)
    ·
      refine ⟨2734062539461432699025993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7290833438563820530735981 2734062539461432699025993)
      ·
        refine ⟨2050546904596074524269495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2734062539461432699025993 2050546904596074524269495)
        ·
          refine ⟨3075820356894111786404243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2050546904596074524269495 3075820356894111786404243)
          ·
            refine ⟨4613730535341167679606365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3075820356894111786404243 4613730535341167679606365)
            ·
              refine ⟨1730148950752937879852387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4613730535341167679606365 1730148950752937879852387)
              ·
                refine ⟨2595223426129406819778581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1730148950752937879852387 2595223426129406819778581)
                ·
                  refine ⟨121651098099815944677121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2595223426129406819778581 121651098099815944677121)
                  ·
                    rfl

theorem cell20_266529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_266529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266529 prefixEnd_266529 := by exact prefixLift 266529
  have htrace : WordTrace (prefixWord ++ tailWord_266529) baseStart_266529 baseEnd_266529 := by
    simpa [prefixWord, tailWord_266529, baseEnd_266529] using wordTrace_append hprefix tailTrace_266529
  have hstable : (prefixWord ++ tailWord_266529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266529).length < 2 ^ (prefixWord ++ tailWord_266529).sum := by decide
  have hdescent : baseEnd_266529 < baseStart_266529 := by decide
  rcases family_descends (prefixWord ++ tailWord_266529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266532 : List Nat := [2, 3, 1, 3, 1, 3, 3, 4]
def baseStart_266532 : Nat := 118140960795 + 266532 * 2 ^ 59
def prefixEnd_266532 : Nat := 4983230072969 + 3 ^ 40 * 266532 * 2
def baseEnd_266532 : Nat := 40550822460520422525703

theorem tailTrace_266532 : CollatzResearch.WordTrace tailWord_266532 prefixEnd_266532 40550822460520422525703 := by
  unfold tailWord_266532
  simp only [CollatzResearch.WordTrace]
  refine ⟨4860610335203779443336925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6480813780271705924449233 4860610335203779443336925)
  ·
    refine ⟨1822728875701417291251347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4860610335203779443336925 1822728875701417291251347)
    ·
      refine ⟨2734093313552125936877021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1822728875701417291251347 2734093313552125936877021)
      ·
        refine ⟨1025284992582047226328883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2734093313552125936877021 1025284992582047226328883)
        ·
          refine ⟨1537927488873070839493325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1025284992582047226328883 1537927488873070839493325)
          ·
            refine ⟨576722808327401564809997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1537927488873070839493325 576722808327401564809997)
            ·
              refine ⟨216271053122775586803749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 576722808327401564809997 216271053122775586803749)
              ·
                refine ⟨40550822460520422525703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216271053122775586803749 40550822460520422525703)
                ·
                  rfl

theorem cell20_266532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 4].length) (baseStart_266532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266532 prefixEnd_266532 := by exact prefixLift 266532
  have htrace : WordTrace (prefixWord ++ tailWord_266532) baseStart_266532 baseEnd_266532 := by
    simpa [prefixWord, tailWord_266532, baseEnd_266532] using wordTrace_append hprefix tailTrace_266532
  have hstable : (prefixWord ++ tailWord_266532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266532).length < 2 ^ (prefixWord ++ tailWord_266532).sum := by decide
  have hdescent : baseEnd_266532 < baseStart_266532 := by decide
  rcases family_descends (prefixWord ++ tailWord_266532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266553 : List Nat := [1, 2, 1, 6, 1, 2, 7]
def baseStart_266553 : Nat := 118140960795 + 266553 * 2 ^ 59
def prefixEnd_266553 : Nat := 4983230072969 + 3 ^ 40 * 266553 * 2
def baseEnd_266553 : Nat := 13518005817086503097447

theorem tailTrace_266553 : CollatzResearch.WordTrace tailWord_266553 prefixEnd_266553 13518005817086503097447 := by
  unfold tailWord_266553
  simp only [CollatzResearch.WordTrace]
  refine ⟨9721986603331479473188313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6481324402220986315458875 9721986603331479473188313)
  ·
    refine ⟨7291489952498609604891235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9721986603331479473188313 7291489952498609604891235)
    ·
      refine ⟨10937234928747914407336853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7291489952498609604891235 10937234928747914407336853)
      ·
        refine ⟨512682887285058487843915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10937234928747914407336853 512682887285058487843915)
        ·
          refine ⟨769024330927587731765873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512682887285058487843915 769024330927587731765873)
          ·
            refine ⟨576768248195690798824405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 769024330927587731765873 576768248195690798824405)
            ·
              refine ⟨13518005817086503097447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 576768248195690798824405 13518005817086503097447)
              ·
                rfl

theorem cell20_266553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 7].length) (baseStart_266553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266553 prefixEnd_266553 := by exact prefixLift 266553
  have htrace : WordTrace (prefixWord ++ tailWord_266553) baseStart_266553 baseEnd_266553 := by
    simpa [prefixWord, tailWord_266553, baseEnd_266553] using wordTrace_append hprefix tailTrace_266553
  have hstable : (prefixWord ++ tailWord_266553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266553).length < 2 ^ (prefixWord ++ tailWord_266553).sum := by decide
  have hdescent : baseEnd_266553 < baseStart_266553 := by decide
  rcases family_descends (prefixWord ++ tailWord_266553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266560 : List Nat := [2, 1, 1, 2, 2, 1, 2, 6, 3]
def baseStart_266560 : Nat := 118140960795 + 266560 * 2 ^ 59
def prefixEnd_266560 : Nat := 4983230072969 + 3 ^ 40 * 266560 * 2
def baseEnd_266560 : Nat := 121665247344517614643661

theorem tailTrace_266560 : CollatzResearch.WordTrace tailWord_266560 prefixEnd_266560 121665247344517614643661 := by
  unfold tailWord_266560
  simp only [CollatzResearch.WordTrace]
  refine ⟨4861120957153059834346567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6481494609537413112462089 4861120957153059834346567)
  ·
    refine ⟨7291681435729589751519851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4861120957153059834346567 7291681435729589751519851)
    ·
      refine ⟨10937522153594384627279777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7291681435729589751519851 10937522153594384627279777)
      ·
        refine ⟨8203141615195788470459833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10937522153594384627279777 8203141615195788470459833)
        ·
          refine ⟨6152356211396841352844875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8203141615195788470459833 6152356211396841352844875)
          ·
            refine ⟨9228534317095262029267313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6152356211396841352844875 9228534317095262029267313)
            ·
              refine ⟨6921400737821446521950485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9228534317095262029267313 6921400737821446521950485)
              ·
                refine ⟨324440659585380305716429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6921400737821446521950485 324440659585380305716429)
                ·
                  refine ⟨121665247344517614643661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324440659585380305716429 121665247344517614643661)
                  ·
                    rfl

theorem cell20_266560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_266560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266560 prefixEnd_266560 := by exact prefixLift 266560
  have htrace : WordTrace (prefixWord ++ tailWord_266560) baseStart_266560 baseEnd_266560 := by
    simpa [prefixWord, tailWord_266560, baseEnd_266560] using wordTrace_append hprefix tailTrace_266560
  have hstable : (prefixWord ++ tailWord_266560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266560).length < 2 ^ (prefixWord ++ tailWord_266560).sum := by decide
  have hdescent : baseEnd_266560 < baseStart_266560 := by decide
  rcases family_descends (prefixWord ++ tailWord_266560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266591 : List Nat := [1, 1, 2, 3, 1, 2, 6, 4]
def baseStart_266591 : Nat := 118140960795 + 266591 * 2 ^ 59
def prefixEnd_266591 : Nat := 4983230072969 + 3 ^ 40 * 266591 * 2
def baseEnd_266591 : Nat := 40559798863073094870067

theorem tailTrace_266591 : CollatzResearch.WordTrace tailWord_266591 prefixEnd_266591 40559798863073094870067 := by
  unfold tailWord_266591
  simp only [CollatzResearch.WordTrace]
  refine ⟨9723372577193811963071627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6482248384795874642047751 9723372577193811963071627)
  ·
    refine ⟨14585058865790717944607441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9723372577193811963071627 14585058865790717944607441)
    ·
      refine ⟨10938794149343038458455581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14585058865790717944607441 10938794149343038458455581)
      ·
        refine ⟨4102047806003639421920843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10938794149343038458455581 4102047806003639421920843)
        ·
          refine ⟨6153071709005459132881265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4102047806003639421920843 6153071709005459132881265)
          ·
            refine ⟨4614803781754094349660949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6153071709005459132881265 4614803781754094349660949)
            ·
              refine ⟨216318927269723172640357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4614803781754094349660949 216318927269723172640357)
              ·
                refine ⟨40559798863073094870067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216318927269723172640357 40559798863073094870067)
                ·
                  rfl

theorem cell20_266591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 4].length) (baseStart_266591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266591 prefixEnd_266591 := by exact prefixLift 266591
  have htrace : WordTrace (prefixWord ++ tailWord_266591) baseStart_266591 baseEnd_266591 := by
    simpa [prefixWord, tailWord_266591, baseEnd_266591] using wordTrace_append hprefix tailTrace_266591
  have hstable : (prefixWord ++ tailWord_266591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266591).length < 2 ^ (prefixWord ++ tailWord_266591).sum := by decide
  have hdescent : baseEnd_266591 < baseStart_266591 := by decide
  rcases family_descends (prefixWord ++ tailWord_266591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266614 : List Nat := [5, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_266614 : Nat := 118140960795 + 266614 * 2 ^ 59
def prefixEnd_266614 : Nat := 4983230072969 + 3 ^ 40 * 266614 * 2
def baseEnd_266614 : Nat := 121689894415933426843441

theorem tailTrace_266614 : CollatzResearch.WordTrace tailWord_266614 prefixEnd_266614 121689894415933426843441 := by
  unfold tailWord_266614
  simp only [CollatzResearch.WordTrace]
  refine ⟨607763216006905430697431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6482807637406991260772597 607763216006905430697431)
  ·
    refine ⟨911644824010358146046147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 607763216006905430697431 911644824010358146046147)
    ·
      refine ⟨1367467236015537219069221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 911644824010358146046147 1367467236015537219069221)
      ·
        refine ⟨256400106752913228575479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1367467236015537219069221 256400106752913228575479)
        ·
          refine ⟨384600160129369842863219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256400106752913228575479 384600160129369842863219)
          ·
            refine ⟨576900240194054764294829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384600160129369842863219 576900240194054764294829)
            ·
              refine ⟨216337590072770536610561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 576900240194054764294829 216337590072770536610561)
              ·
                refine ⟨162253192554577902457921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216337590072770536610561 162253192554577902457921)
                ·
                  refine ⟨121689894415933426843441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162253192554577902457921 121689894415933426843441)
                  ·
                    rfl

theorem cell20_266614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_266614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266614 prefixEnd_266614 := by exact prefixLift 266614
  have htrace : WordTrace (prefixWord ++ tailWord_266614) baseStart_266614 baseEnd_266614 := by
    simpa [prefixWord, tailWord_266614, baseEnd_266614] using wordTrace_append hprefix tailTrace_266614
  have hstable : (prefixWord ++ tailWord_266614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266614).length < 2 ^ (prefixWord ++ tailWord_266614).sum := by decide
  have hdescent : baseEnd_266614 < baseStart_266614 := by decide
  rcases family_descends (prefixWord ++ tailWord_266614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266666 : List Nat := [3, 1, 6, 1, 1, 1, 2, 2, 3]
def baseStart_266666 : Nat := 118140960795 + 266666 * 2 ^ 59
def prefixEnd_266666 : Nat := 4983230072969 + 3 ^ 40 * 266666 * 2
def baseEnd_266666 : Nat := 121713628632852357109895

theorem tailTrace_266666 : CollatzResearch.WordTrace tailWord_266666 prefixEnd_266666 121713628632852357109895 := by
  unfold tailWord_266666
  simp only [CollatzResearch.WordTrace]
  refine ⟨2431527012980524943012963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6484072034614733181367901 2431527012980524943012963)
  ·
    refine ⟨3647290519470787414519445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2431527012980524943012963 3647290519470787414519445)
    ·
      refine ⟨170966743100193160055599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3647290519470787414519445 170966743100193160055599)
      ·
        refine ⟨256450114650289740083399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170966743100193160055599 256450114650289740083399)
        ·
          refine ⟨384675171975434610125099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256450114650289740083399 384675171975434610125099)
          ·
            refine ⟨577012757963151915187649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384675171975434610125099 577012757963151915187649)
            ·
              refine ⟨432759568472363936390737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577012757963151915187649 432759568472363936390737)
              ·
                refine ⟨324569676354272952293053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432759568472363936390737 324569676354272952293053)
                ·
                  refine ⟨121713628632852357109895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324569676354272952293053 121713628632852357109895)
                  ·
                    rfl

theorem cell20_266666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_266666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266666 prefixEnd_266666 := by exact prefixLift 266666
  have htrace : WordTrace (prefixWord ++ tailWord_266666) baseStart_266666 baseEnd_266666 := by
    simpa [prefixWord, tailWord_266666, baseEnd_266666] using wordTrace_append hprefix tailTrace_266666
  have hstable : (prefixWord ++ tailWord_266666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266666).length < 2 ^ (prefixWord ++ tailWord_266666).sum := by decide
  have hdescent : baseEnd_266666 < baseStart_266666 := by decide
  rcases family_descends (prefixWord ++ tailWord_266666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266684 : List Nat := [2, 2, 2, 4, 1, 3, 1, 5]
def baseStart_266684 : Nat := 118140960795 + 266684 * 2 ^ 59
def prefixEnd_266684 : Nat := 4983230072969 + 3 ^ 40 * 266684 * 2
def baseEnd_266684 : Nat := 40573948107774764836607

theorem tailTrace_266684 : CollatzResearch.WordTrace tailWord_266684 prefixEnd_266684 40573948107774764836607 := by
  unfold tailWord_266684
  simp only [CollatzResearch.WordTrace]
  refine ⟨4863382282928444423103553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6484509710571259230804737 4863382282928444423103553)
  ·
    refine ⟨3647536712196333317327665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4863382282928444423103553 3647536712196333317327665)
    ·
      refine ⟨2735652534147249987995749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3647536712196333317327665 2735652534147249987995749)
      ·
        refine ⟨512934850152609372749203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2735652534147249987995749 512934850152609372749203)
        ·
          refine ⟨769402275228914059123805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 512934850152609372749203 769402275228914059123805)
          ·
            refine ⟨288525853210842772171427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 769402275228914059123805 288525853210842772171427)
            ·
              refine ⟨432788779816264158257141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288525853210842772171427 432788779816264158257141)
              ·
                refine ⟨40573948107774764836607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 432788779816264158257141 40573948107774764836607)
                ·
                  rfl

theorem cell20_266684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 5].length) (baseStart_266684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266684 prefixEnd_266684 := by exact prefixLift 266684
  have htrace : WordTrace (prefixWord ++ tailWord_266684) baseStart_266684 baseEnd_266684 := by
    simpa [prefixWord, tailWord_266684, baseEnd_266684] using wordTrace_append hprefix tailTrace_266684
  have hstable : (prefixWord ++ tailWord_266684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266684).length < 2 ^ (prefixWord ++ tailWord_266684).sum := by decide
  have hdescent : baseEnd_266684 < baseStart_266684 := by decide
  rcases family_descends (prefixWord ++ tailWord_266684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266725 : List Nat := [1, 3, 1, 5, 3, 1, 1, 2, 3]
def baseStart_266725 : Nat := 118140960795 + 266725 * 2 ^ 59
def prefixEnd_266725 : Nat := 4983230072969 + 3 ^ 40 * 266725 * 2
def baseEnd_266725 : Nat := 121740557840510374142987

theorem tailTrace_266725 : CollatzResearch.WordTrace tailWord_266725 prefixEnd_266725 121740557840510374142987 := by
  unfold tailWord_266725
  simp only [CollatzResearch.WordTrace]
  refine ⟨9728259958708352848449629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6485506639138901898966419 9728259958708352848449629)
  ·
    refine ⟨3648097484515632318168611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9728259958708352848449629 3648097484515632318168611)
    ·
      refine ⟨5472146226773448477252917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3648097484515632318168611 5472146226773448477252917)
      ·
        refine ⟨513013708760010794742461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5472146226773448477252917 513013708760010794742461)
        ·
          refine ⟨192380140785004048028423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 513013708760010794742461 192380140785004048028423)
          ·
            refine ⟨288570211177506072042635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 192380140785004048028423 288570211177506072042635)
            ·
              refine ⟨432855316766259108063953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288570211177506072042635 432855316766259108063953)
              ·
                refine ⟨324641487574694331047965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 432855316766259108063953 324641487574694331047965)
                ·
                  refine ⟨121740557840510374142987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324641487574694331047965 121740557840510374142987)
                  ·
                    rfl

theorem cell20_266725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_266725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266725 prefixEnd_266725 := by exact prefixLift 266725
  have htrace : WordTrace (prefixWord ++ tailWord_266725) baseStart_266725 baseEnd_266725 := by
    simpa [prefixWord, tailWord_266725, baseEnd_266725] using wordTrace_append hprefix tailTrace_266725
  have hstable : (prefixWord ++ tailWord_266725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266725).length < 2 ^ (prefixWord ++ tailWord_266725).sum := by decide
  have hdescent : baseEnd_266725 < baseStart_266725 := by decide
  rcases family_descends (prefixWord ++ tailWord_266725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266736 : List Nat := [2, 1, 1, 1, 3, 3, 1, 6, 2]
def baseStart_266736 : Nat := 118140960795 + 266736 * 2 ^ 59
def prefixEnd_266736 : Nat := 4983230072969 + 3 ^ 40 * 266736 * 2
def baseEnd_266736 : Nat := 121745578540243224776275

theorem tailTrace_266736 : CollatzResearch.WordTrace tailWord_266736 prefixEnd_266736 121745578540243224776275 := by
  unfold tailWord_266736
  simp only [CollatzResearch.WordTrace]
  refine ⟨4864330580834250863550031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6485774107779001151400041 4864330580834250863550031)
  ·
    refine ⟨7296495871251376295325047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4864330580834250863550031 7296495871251376295325047)
    ·
      refine ⟨10944743806877064442987571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7296495871251376295325047 10944743806877064442987571)
      ·
        refine ⟨16417115710315596664481357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10944743806877064442987571 16417115710315596664481357)
        ·
          refine ⟨6156418391368348749180509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16417115710315596664481357 6156418391368348749180509)
          ·
            refine ⟨2308656896763130780942691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6156418391368348749180509 2308656896763130780942691)
            ·
              refine ⟨3462985345144696171414037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2308656896763130780942691 3462985345144696171414037)
              ·
                refine ⟨162327438053657633035033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3462985345144696171414037 162327438053657633035033)
                ·
                  refine ⟨121745578540243224776275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162327438053657633035033 121745578540243224776275)
                  ·
                    rfl

theorem cell20_266736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 6, 2].length) (baseStart_266736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266736 prefixEnd_266736 := by exact prefixLift 266736
  have htrace : WordTrace (prefixWord ++ tailWord_266736) baseStart_266736 baseEnd_266736 := by
    simpa [prefixWord, tailWord_266736, baseEnd_266736] using wordTrace_append hprefix tailTrace_266736
  have hstable : (prefixWord ++ tailWord_266736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266736).length < 2 ^ (prefixWord ++ tailWord_266736).sum := by decide
  have hdescent : baseEnd_266736 < baseStart_266736 := by decide
  rcases family_descends (prefixWord ++ tailWord_266736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266757 : List Nat := [1, 3, 1, 1, 2, 2, 4, 2, 4]
def baseStart_266757 : Nat := 118140960795 + 266757 * 2 ^ 59
def prefixEnd_266757 : Nat := 4983230072969 + 3 ^ 40 * 266757 * 2
def baseEnd_266757 : Nat := 121755163512460485076189

theorem tailTrace_266757 : CollatzResearch.WordTrace tailWord_266757 prefixEnd_266757 121755163512460485076189 := by
  unfold tailWord_266757
  simp only [CollatzResearch.WordTrace]
  refine ⟨9729427094592422313614525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6486284729728281542409683 9729427094592422313614525)
  ·
    refine ⟨3648535160472158367605447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9729427094592422313614525 3648535160472158367605447)
    ·
      refine ⟨5472802740708237551408171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3648535160472158367605447 5472802740708237551408171)
      ·
        refine ⟨8209204111062356327112257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5472802740708237551408171 8209204111062356327112257)
        ·
          refine ⟨6156903083296767245334193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8209204111062356327112257 6156903083296767245334193)
          ·
            refine ⟨4617677312472575434000645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6156903083296767245334193 4617677312472575434000645)
            ·
              refine ⟨865814496088607893875121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4617677312472575434000645 865814496088607893875121)
              ·
                refine ⟨649360872066455920406341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 865814496088607893875121 649360872066455920406341)
                ·
                  refine ⟨121755163512460485076189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 649360872066455920406341 121755163512460485076189)
                  ·
                    rfl

theorem cell20_266757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_266757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266757 prefixEnd_266757 := by exact prefixLift 266757
  have htrace : WordTrace (prefixWord ++ tailWord_266757) baseStart_266757 baseEnd_266757 := by
    simpa [prefixWord, tailWord_266757, baseEnd_266757] using wordTrace_append hprefix tailTrace_266757
  have hstable : (prefixWord ++ tailWord_266757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266757).length < 2 ^ (prefixWord ++ tailWord_266757).sum := by decide
  have hdescent : baseEnd_266757 < baseStart_266757 := by decide
  rcases family_descends (prefixWord ++ tailWord_266757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266771 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 7]
def baseStart_266771 : Nat := 118140960795 + 266771 * 2 ^ 59
def prefixEnd_266771 : Nat := 4983230072969 + 3 ^ 40 * 266771 * 2
def baseEnd_266771 : Nat := 121761553493938658609465

theorem tailTrace_266771 : CollatzResearch.WordTrace tailWord_266771 prefixEnd_266771 121761553493938658609465 := by
  unfold tailWord_266771
  simp only [CollatzResearch.WordTrace]
  refine ⟨9729937716541702704624167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6486625144361135136416111 9729937716541702704624167)
  ·
    refine ⟨14594906574812554056936251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9729937716541702704624167 14594906574812554056936251)
    ·
      refine ⟨21892359862218831085404377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14594906574812554056936251 21892359862218831085404377)
      ·
        refine ⟨16419269896664123314053283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21892359862218831085404377 16419269896664123314053283)
        ·
          refine ⟨24628904844996184971079925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16419269896664123314053283 24628904844996184971079925)
          ·
            refine ⟨2308959829218392341038743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 24628904844996184971079925 2308959829218392341038743)
            ·
              refine ⟨3463439743827588511558115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2308959829218392341038743 3463439743827588511558115)
              ·
                refine ⟨5195159615741382767337173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3463439743827588511558115 5195159615741382767337173)
                ·
                  refine ⟨121761553493938658609465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5195159615741382767337173 121761553493938658609465)
                  ·
                    rfl

theorem cell20_266771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_266771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266771 prefixEnd_266771 := by exact prefixLift 266771
  have htrace : WordTrace (prefixWord ++ tailWord_266771) baseStart_266771 baseEnd_266771 := by
    simpa [prefixWord, tailWord_266771, baseEnd_266771] using wordTrace_append hprefix tailTrace_266771
  have hstable : (prefixWord ++ tailWord_266771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266771).length < 2 ^ (prefixWord ++ tailWord_266771).sum := by decide
  have hdescent : baseEnd_266771 < baseStart_266771 := by decide
  rcases family_descends (prefixWord ++ tailWord_266771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266781 : List Nat := [1, 4, 2, 2, 1, 4, 6]
def baseStart_266781 : Nat := 118140960795 + 266781 * 2 ^ 59
def prefixEnd_266781 : Nat := 4983230072969 + 3 ^ 40 * 266781 * 2
def baseEnd_266781 : Nat := 13529568640713674252899

theorem tailTrace_266781 : CollatzResearch.WordTrace tailWord_266781 prefixEnd_266781 13529568640713674252899 := by
  unfold tailWord_266781
  simp only [CollatzResearch.WordTrace]
  refine ⟨9730302446505474412488197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6486868297670316274992131 9730302446505474412488197)
  ·
    refine ⟨1824431708719776452341537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9730302446505474412488197 1824431708719776452341537)
    ·
      refine ⟨1368323781539832339256153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1824431708719776452341537 1368323781539832339256153)
      ·
        refine ⟨1026242836154874254442115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1368323781539832339256153 1026242836154874254442115)
        ·
          refine ⟨1539364254232311381663173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1026242836154874254442115 1539364254232311381663173)
          ·
            refine ⟨288630797668558384061845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1539364254232311381663173 288630797668558384061845)
            ·
              refine ⟨13529568640713674252899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 288630797668558384061845 13529568640713674252899)
              ·
                rfl

theorem cell20_266781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 6].length) (baseStart_266781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266781 prefixEnd_266781 := by exact prefixLift 266781
  have htrace : WordTrace (prefixWord ++ tailWord_266781) baseStart_266781 baseEnd_266781 := by
    simpa [prefixWord, tailWord_266781, baseEnd_266781] using wordTrace_append hprefix tailTrace_266781
  have hstable : (prefixWord ++ tailWord_266781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266781).length < 2 ^ (prefixWord ++ tailWord_266781).sum := by decide
  have hdescent : baseEnd_266781 < baseStart_266781 := by decide
  rcases family_descends (prefixWord ++ tailWord_266781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266797 : List Nat := [1, 5, 4, 1, 1, 2, 2, 1, 3]
def baseStart_266797 : Nat := 118140960795 + 266797 * 2 ^ 59
def prefixEnd_266797 : Nat := 4983230072969 + 3 ^ 40 * 266797 * 2
def baseEnd_266797 : Nat := 121773420602398123742693

theorem tailTrace_266797 : CollatzResearch.WordTrace tailWord_266797 prefixEnd_266797 121773420602398123742693 := by
  unfold tailWord_266797
  simp only [CollatzResearch.WordTrace]
  refine ⟨9730886014447509145070645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6487257342965006096713763 9730886014447509145070645)
  ·
    refine ⟨912270563854453982350373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9730886014447509145070645 912270563854453982350373)
    ·
      refine ⟨171050730722710121690695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 912270563854453982350373 171050730722710121690695)
      ·
        refine ⟨256576096084065182536043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171050730722710121690695 256576096084065182536043)
        ·
          refine ⟨384864144126097773804065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256576096084065182536043 384864144126097773804065)
          ·
            refine ⟨288648108094573330353049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 384864144126097773804065 288648108094573330353049)
            ·
              refine ⟨216486081070929997764787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288648108094573330353049 216486081070929997764787)
              ·
                refine ⟨324729121606394996647181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216486081070929997764787 324729121606394996647181)
                ·
                  refine ⟨121773420602398123742693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324729121606394996647181 121773420602398123742693)
                  ·
                    rfl

theorem cell20_266797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_266797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266797 prefixEnd_266797 := by exact prefixLift 266797
  have htrace : WordTrace (prefixWord ++ tailWord_266797) baseStart_266797 baseEnd_266797 := by
    simpa [prefixWord, tailWord_266797, baseEnd_266797] using wordTrace_append hprefix tailTrace_266797
  have hstable : (prefixWord ++ tailWord_266797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266797).length < 2 ^ (prefixWord ++ tailWord_266797).sum := by decide
  have hdescent : baseEnd_266797 < baseStart_266797 := by decide
  rcases family_descends (prefixWord ++ tailWord_266797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266798 : List Nat := [4, 1, 3, 1, 3, 1, 2, 5]
def baseStart_266798 : Nat := 118140960795 + 266798 * 2 ^ 59
def prefixEnd_266798 : Nat := 4983230072969 + 3 ^ 40 * 266798 * 2
def baseEnd_266798 : Nat := 40591292343215521569785

theorem tailTrace_266798 : CollatzResearch.WordTrace tailWord_266798 prefixEnd_266798 40591292343215521569785 := by
  unfold tailWord_266798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1216365310930485789482131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6487281658295924210571365 1216365310930485789482131)
  ·
    refine ⟨1824547966395728684223197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1216365310930485789482131 1824547966395728684223197)
    ·
      refine ⟨684205487398398256583699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1824547966395728684223197 684205487398398256583699)
      ·
        refine ⟨1026308231097597384875549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684205487398398256583699 1026308231097597384875549)
        ·
          refine ⟨384865586661599019328331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1026308231097597384875549 384865586661599019328331)
          ·
            refine ⟨577298379992398528992497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384865586661599019328331 577298379992398528992497)
            ·
              refine ⟨432973784994298896744373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577298379992398528992497 432973784994298896744373)
              ·
                refine ⟨40591292343215521569785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 432973784994298896744373 40591292343215521569785)
                ·
                  rfl

theorem cell20_266798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_266798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266798 prefixEnd_266798 := by exact prefixLift 266798
  have htrace : WordTrace (prefixWord ++ tailWord_266798) baseStart_266798 baseEnd_266798 := by
    simpa [prefixWord, tailWord_266798, baseEnd_266798] using wordTrace_append hprefix tailTrace_266798
  have hstable : (prefixWord ++ tailWord_266798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266798).length < 2 ^ (prefixWord ++ tailWord_266798).sum := by decide
  have hdescent : baseEnd_266798 < baseStart_266798 := by decide
  rcases family_descends (prefixWord ++ tailWord_266798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266802 : List Nat := [3, 2, 1, 1, 2, 1, 3, 7]
def baseStart_266802 : Nat := 118140960795 + 266802 * 2 ^ 59
def prefixEnd_266802 : Nat := 4983230072969 + 3 ^ 40 * 266802 * 2
def baseEnd_266802 : Nat := 40591900912880109525335

theorem tailTrace_266802 : CollatzResearch.WordTrace tailWord_266802 prefixEnd_266802 40591900912880109525335 := by
  unfold tailWord_266802
  simp only [CollatzResearch.WordTrace]
  refine ⟨2432767094857348749750665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6487378919619596666001773 2432767094857348749750665)
  ·
    refine ⟨1824575321143011562312999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2432767094857348749750665 1824575321143011562312999)
    ·
      refine ⟨2736862981714517343469499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1824575321143011562312999 2736862981714517343469499)
      ·
        refine ⟨4105294472571776015204249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2736862981714517343469499 4105294472571776015204249)
        ·
          refine ⟨3078970854428832011403187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4105294472571776015204249 3078970854428832011403187)
          ·
            refine ⟨4618456281643248017104781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3078970854428832011403187 4618456281643248017104781)
            ·
              refine ⟨1731921105616218006414293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4618456281643248017104781 1731921105616218006414293)
              ·
                refine ⟨40591900912880109525335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1731921105616218006414293 40591900912880109525335)
                ·
                  rfl

theorem cell20_266802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_266802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266802 prefixEnd_266802 := by exact prefixLift 266802
  have htrace : WordTrace (prefixWord ++ tailWord_266802) baseStart_266802 baseEnd_266802 := by
    simpa [prefixWord, tailWord_266802, baseEnd_266802] using wordTrace_append hprefix tailTrace_266802
  have hstable : (prefixWord ++ tailWord_266802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266802).length < 2 ^ (prefixWord ++ tailWord_266802).sum := by decide
  have hdescent : baseEnd_266802 < baseStart_266802 := by decide
  rcases family_descends (prefixWord ++ tailWord_266802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266847 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 5]
def baseStart_266847 : Nat := 118140960795 + 266847 * 2 ^ 59
def prefixEnd_266847 : Nat := 4983230072969 + 3 ^ 40 * 266847 * 2
def baseEnd_266847 : Nat := 121796241964820172075821

theorem tailTrace_266847 : CollatzResearch.WordTrace tailWord_266847 prefixEnd_266847 121796241964820172075821 := by
  unfold tailWord_266847
  simp only [CollatzResearch.WordTrace]
  refine ⟨9732709664266367684390795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6488473109510911789593863 9732709664266367684390795)
  ·
    refine ⟨14599064496399551526586193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9732709664266367684390795 14599064496399551526586193)
    ·
      refine ⟨10949298372299663644939645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14599064496399551526586193 10949298372299663644939645)
      ·
        refine ⟨4105986889612373866852367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10949298372299663644939645 4105986889612373866852367)
        ·
          refine ⟨6158980334418560800278551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4105986889612373866852367 6158980334418560800278551)
          ·
            refine ⟨9238470501627841200417827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6158980334418560800278551 9238470501627841200417827)
            ·
              refine ⟨13857705752441761800626741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9238470501627841200417827 13857705752441761800626741)
              ·
                refine ⟨1299159914291415168808757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13857705752441761800626741 1299159914291415168808757)
                ·
                  refine ⟨121796241964820172075821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1299159914291415168808757 121796241964820172075821)
                  ·
                    rfl

theorem cell20_266847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_266847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266847 prefixEnd_266847 := by exact prefixLift 266847
  have htrace : WordTrace (prefixWord ++ tailWord_266847) baseStart_266847 baseEnd_266847 := by
    simpa [prefixWord, tailWord_266847, baseEnd_266847] using wordTrace_append hprefix tailTrace_266847
  have hstable : (prefixWord ++ tailWord_266847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266847).length < 2 ^ (prefixWord ++ tailWord_266847).sum := by decide
  have hdescent : baseEnd_266847 < baseStart_266847 := by decide
  rcases family_descends (prefixWord ++ tailWord_266847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266898 : List Nat := [3, 2, 3, 1, 2, 3, 1, 2, 3]
def baseStart_266898 : Nat := 118140960795 + 266898 * 2 ^ 59
def prefixEnd_266898 : Nat := 4983230072969 + 3 ^ 40 * 266898 * 2
def baseEnd_266898 : Nat := 121819519754490661375613

theorem tailTrace_266898 : CollatzResearch.WordTrace tailWord_266898 prefixEnd_266898 121819519754490661375613 := by
  unfold tailWord_266898
  simp only [CollatzResearch.WordTrace]
  refine ⟨2433642446770400848624337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6489713191387735596331565 2433642446770400848624337)
  ·
    refine ⟨1825231835077800636468253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2433642446770400848624337 1825231835077800636468253)
    ·
      refine ⟨684461938154175238675595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1825231835077800636468253 684461938154175238675595)
      ·
        refine ⟨1026692907231262858013393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 684461938154175238675595 1026692907231262858013393)
        ·
          refine ⟨770019680423447143510045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1026692907231262858013393 770019680423447143510045)
          ·
            refine ⟨288757380158792678816267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 770019680423447143510045 288757380158792678816267)
            ·
              refine ⟨433136070238189018224401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288757380158792678816267 433136070238189018224401)
              ·
                refine ⟨324852052678641763668301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433136070238189018224401 324852052678641763668301)
                ·
                  refine ⟨121819519754490661375613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324852052678641763668301 121819519754490661375613)
                  ·
                    rfl

theorem cell20_266898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_266898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266898 prefixEnd_266898 := by exact prefixLift 266898
  have htrace : WordTrace (prefixWord ++ tailWord_266898) baseStart_266898 baseEnd_266898 := by
    simpa [prefixWord, tailWord_266898, baseEnd_266898] using wordTrace_append hprefix tailTrace_266898
  have hstable : (prefixWord ++ tailWord_266898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266898).length < 2 ^ (prefixWord ++ tailWord_266898).sum := by decide
  have hdescent : baseEnd_266898 < baseStart_266898 := by decide
  rcases family_descends (prefixWord ++ tailWord_266898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266909 : List Nat := [1, 4, 2, 1, 1, 1, 3, 3, 4]
def baseStart_266909 : Nat := 118140960795 + 266909 * 2 ^ 59
def prefixEnd_266909 : Nat := 4983230072969 + 3 ^ 40 * 266909 * 2
def baseEnd_266909 : Nat := 121824540454223512008901

theorem tailTrace_266909 : CollatzResearch.WordTrace tailWord_266909 prefixEnd_266909 121824540454223512008901 := by
  unfold tailWord_266909
  simp only [CollatzResearch.WordTrace]
  refine ⟨9734970990041752273147781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6489980660027834848765187 9734970990041752273147781)
  ·
    refine ⟨1825307060632828551215209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9734970990041752273147781 1825307060632828551215209)
    ·
      refine ⟨1368980295474621413411407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1825307060632828551215209 1368980295474621413411407)
      ·
        refine ⟨2053470443211932120117111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1368980295474621413411407 2053470443211932120117111)
        ·
          refine ⟨3080205664817898180175667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2053470443211932120117111 3080205664817898180175667)
          ·
            refine ⟨4620308497226847270263501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3080205664817898180175667 4620308497226847270263501)
            ·
              refine ⟨1732615686460067726348813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4620308497226847270263501 1732615686460067726348813)
              ·
                refine ⟨649730882422525397380805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1732615686460067726348813 649730882422525397380805)
                ·
                  refine ⟨121824540454223512008901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 649730882422525397380805 121824540454223512008901)
                  ·
                    rfl

theorem cell20_266909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_266909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266909 prefixEnd_266909 := by exact prefixLift 266909
  have htrace : WordTrace (prefixWord ++ tailWord_266909) baseStart_266909 baseEnd_266909 := by
    simpa [prefixWord, tailWord_266909, baseEnd_266909] using wordTrace_append hprefix tailTrace_266909
  have hstable : (prefixWord ++ tailWord_266909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266909).length < 2 ^ (prefixWord ++ tailWord_266909).sum := by decide
  have hdescent : baseEnd_266909 < baseStart_266909 := by decide
  rcases family_descends (prefixWord ++ tailWord_266909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266916 : List Nat := [2, 3, 1, 2, 2, 1, 2, 7]
def baseStart_266916 : Nat := 118140960795 + 266916 * 2 ^ 59
def prefixEnd_266916 : Nat := 4983230072969 + 3 ^ 40 * 266916 * 2
def baseEnd_266916 : Nat := 40609245148320866258513

theorem tailTrace_266916 : CollatzResearch.WordTrace tailWord_266916 prefixEnd_266916 40609245148320866258513 := by
  unfold tailWord_266916
  simp only [CollatzResearch.WordTrace]
  refine ⟨4867613150508196234326301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6490150867344261645768401 4867613150508196234326301)
  ·
    refine ⟨1825354931440573587872363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4867613150508196234326301 1825354931440573587872363)
    ·
      refine ⟨2738032397160860381808545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1825354931440573587872363 2738032397160860381808545)
      ·
        refine ⟨2053524297870645286356409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2738032397160860381808545 2053524297870645286356409)
        ·
          refine ⟨1540143223402983964767307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2053524297870645286356409 1540143223402983964767307)
          ·
            refine ⟨2310214835104475947150961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1540143223402983964767307 2310214835104475947150961)
            ·
              refine ⟨1732661126328356960363221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2310214835104475947150961 1732661126328356960363221)
              ·
                refine ⟨40609245148320866258513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1732661126328356960363221 40609245148320866258513)
                ·
                  rfl

theorem cell20_266916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_266916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266916 prefixEnd_266916 := by exact prefixLift 266916
  have htrace : WordTrace (prefixWord ++ tailWord_266916) baseStart_266916 baseEnd_266916 := by
    simpa [prefixWord, tailWord_266916, baseEnd_266916] using wordTrace_append hprefix tailTrace_266916
  have hstable : (prefixWord ++ tailWord_266916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266916).length < 2 ^ (prefixWord ++ tailWord_266916).sum := by decide
  have hdescent : baseEnd_266916 < baseStart_266916 := by decide
  rcases family_descends (prefixWord ++ tailWord_266916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266929 : List Nat := [1, 2, 2, 6, 1, 2, 2, 4]
def baseStart_266929 : Nat := 118140960795 + 266929 * 2 ^ 59
def prefixEnd_266929 : Nat := 4983230072969 + 3 ^ 40 * 266929 * 2
def baseEnd_266929 : Nat := 40611222999730777114051

theorem tailTrace_266929 : CollatzResearch.WordTrace tailWord_266929 prefixEnd_266929 40611222999730777114051 := by
  unfold tailWord_266929
  simp only [CollatzResearch.WordTrace]
  refine ⟨9735700449969295688875841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6490466966646197125917227 9735700449969295688875841)
  ·
    refine ⟨7301775337476971766656881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9735700449969295688875841 7301775337476971766656881)
    ·
      refine ⟨5476331503107728824992661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7301775337476971766656881 5476331503107728824992661)
      ·
        refine ⟨256703039208174788671531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5476331503107728824992661 256703039208174788671531)
        ·
          refine ⟨385054558812262183007297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256703039208174788671531 385054558812262183007297)
          ·
            refine ⟨288790919109196637255473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385054558812262183007297 288790919109196637255473)
            ·
              refine ⟨216593189331897477941605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 288790919109196637255473 216593189331897477941605)
              ·
                refine ⟨40611222999730777114051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216593189331897477941605 40611222999730777114051)
                ·
                  rfl

theorem cell20_266929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 4].length) (baseStart_266929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266929 prefixEnd_266929 := by exact prefixLift 266929
  have htrace : WordTrace (prefixWord ++ tailWord_266929) baseStart_266929 baseEnd_266929 := by
    simpa [prefixWord, tailWord_266929, baseEnd_266929] using wordTrace_append hprefix tailTrace_266929
  have hstable : (prefixWord ++ tailWord_266929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266929).length < 2 ^ (prefixWord ++ tailWord_266929).sum := by decide
  have hdescent : baseEnd_266929 < baseStart_266929 := by decide
  rcases family_descends (prefixWord ++ tailWord_266929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266933 : List Nat := [1, 3, 3, 3, 1, 2, 1, 6]
def baseStart_266933 : Nat := 118140960795 + 266933 * 2 ^ 59
def prefixEnd_266933 : Nat := 4983230072969 + 3 ^ 40 * 266933 * 2
def baseEnd_266933 : Nat := 40611831569395365069601

theorem tailTrace_266933 : CollatzResearch.WordTrace tailWord_266933 prefixEnd_266933 40611831569395365069601 := by
  unfold tailWord_266933
  simp only [CollatzResearch.WordTrace]
  refine ⟨9735846341954804372021453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6490564227969869581347635 9735846341954804372021453)
  ·
    refine ⟨3650942378233051639508045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9735846341954804372021453 3650942378233051639508045)
    ·
      refine ⟨1369103391837394364815517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3650942378233051639508045 1369103391837394364815517)
      ·
        refine ⟨513413771939022886805819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1369103391837394364815517 513413771939022886805819)
        ·
          refine ⟨770120657908534330208729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513413771939022886805819 770120657908534330208729)
          ·
            refine ⟨577590493431400747656547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 770120657908534330208729 577590493431400747656547)
            ·
              refine ⟨866385740147101121484821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 577590493431400747656547 866385740147101121484821)
              ·
                refine ⟨40611831569395365069601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 866385740147101121484821 40611831569395365069601)
                ·
                  rfl

theorem cell20_266933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 6].length) (baseStart_266933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266933 prefixEnd_266933 := by exact prefixLift 266933
  have htrace : WordTrace (prefixWord ++ tailWord_266933) baseStart_266933 baseEnd_266933 := by
    simpa [prefixWord, tailWord_266933, baseEnd_266933] using wordTrace_append hprefix tailTrace_266933
  have hstable : (prefixWord ++ tailWord_266933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266933).length < 2 ^ (prefixWord ++ tailWord_266933).sum := by decide
  have hdescent : baseEnd_266933 < baseStart_266933 := by decide
  rcases family_descends (prefixWord ++ tailWord_266933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266943 : List Nat := [1, 1, 2, 2, 2, 6, 1, 3, 2]
def baseStart_266943 : Nat := 118140960795 + 266943 * 2 ^ 59
def prefixEnd_266943 : Nat := 4983230072969 + 3 ^ 40 * 266943 * 2
def baseEnd_266943 : Nat := 121840058980670504875429

theorem tailTrace_266943 : CollatzResearch.WordTrace tailWord_266943 prefixEnd_266943 121840058980670504875429 := by
  unfold tailWord_266943
  simp only [CollatzResearch.WordTrace]
  refine ⟨9736211071918576079885483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6490807381279050719923655 9736211071918576079885483)
  ·
    refine ⟨14604316607877864119828225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9736211071918576079885483 14604316607877864119828225)
    ·
      refine ⟨10953237455908398089871169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14604316607877864119828225 10953237455908398089871169)
      ·
        refine ⟨8214928091931298567403377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10953237455908398089871169 8214928091931298567403377)
        ·
          refine ⟨6161196068948473925552533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8214928091931298567403377 6161196068948473925552533)
          ·
            refine ⟨288806065731959715260275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6161196068948473925552533 288806065731959715260275)
            ·
              refine ⟨433209098597939572890413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288806065731959715260275 433209098597939572890413)
              ·
                refine ⟨162453411974227339833905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 433209098597939572890413 162453411974227339833905)
                ·
                  refine ⟨121840058980670504875429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162453411974227339833905 121840058980670504875429)
                  ·
                    rfl

theorem cell20_266943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 2].length) (baseStart_266943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266943 prefixEnd_266943 := by exact prefixLift 266943
  have htrace : WordTrace (prefixWord ++ tailWord_266943) baseStart_266943 baseEnd_266943 := by
    simpa [prefixWord, tailWord_266943, baseEnd_266943] using wordTrace_append hprefix tailTrace_266943
  have hstable : (prefixWord ++ tailWord_266943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266943).length < 2 ^ (prefixWord ++ tailWord_266943).sum := by decide
  have hdescent : baseEnd_266943 < baseStart_266943 := by decide
  rcases family_descends (prefixWord ++ tailWord_266943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266954 : List Nat := [3, 1, 2, 1, 4, 1, 8]
def baseStart_266954 : Nat := 118140960795 + 266954 * 2 ^ 59
def prefixEnd_266954 : Nat := 4983230072969 + 3 ^ 40 * 266954 * 2
def baseEnd_266954 : Nat := 13538342186711483945413

theorem tailTrace_266954 : CollatzResearch.WordTrace tailWord_266954 prefixEnd_266954 13538342186711483945413 := by
  unfold tailWord_266954
  simp only [CollatzResearch.WordTrace]
  refine ⟨2434153068719681239633979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6491074849919149972357277 2434153068719681239633979)
  ·
    refine ⟨3651229603079521859450969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2434153068719681239633979 3651229603079521859450969)
    ·
      refine ⟨2738422202309641394588227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3651229603079521859450969 2738422202309641394588227)
      ·
        refine ⟨4107633303464462091882341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2738422202309641394588227 4107633303464462091882341)
        ·
          refine ⟨770181244399586642227939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4107633303464462091882341 770181244399586642227939)
          ·
            refine ⟨1155271866599379963341909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770181244399586642227939 1155271866599379963341909)
            ·
              refine ⟨13538342186711483945413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1155271866599379963341909 13538342186711483945413)
              ·
                rfl

theorem cell20_266954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 8].length) (baseStart_266954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266954 prefixEnd_266954 := by exact prefixLift 266954
  have htrace : WordTrace (prefixWord ++ tailWord_266954) baseStart_266954 baseEnd_266954 := by
    simpa [prefixWord, tailWord_266954, baseEnd_266954] using wordTrace_append hprefix tailTrace_266954
  have hstable : (prefixWord ++ tailWord_266954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266954).length < 2 ^ (prefixWord ++ tailWord_266954).sum := by decide
  have hdescent : baseEnd_266954 < baseStart_266954 := by decide
  rcases family_descends (prefixWord ++ tailWord_266954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_266961 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 5]
def baseStart_266961 : Nat := 118140960795 + 266961 * 2 ^ 59
def prefixEnd_266961 : Nat := 4983230072969 + 3 ^ 40 * 266961 * 2
def baseEnd_266961 : Nat := 121848274671142442275355

theorem tailTrace_266961 : CollatzResearch.WordTrace tailWord_266961 prefixEnd_266961 121848274671142442275355 := by
  unfold tailWord_266961
  simp only [CollatzResearch.WordTrace]
  refine ⟨9736867585853365154040737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6491245057235576769360491 9736867585853365154040737)
  ·
    refine ⟨7302650689390023865530553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9736867585853365154040737 7302650689390023865530553)
    ·
      refine ⟨5476988017042517899147915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7302650689390023865530553 5476988017042517899147915)
      ·
        refine ⟨8215482025563776848721873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5476988017042517899147915 8215482025563776848721873)
        ·
          refine ⟨6161611519172832636541405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8215482025563776848721873 6161611519172832636541405)
          ·
            refine ⟨2310604319689812238703027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6161611519172832636541405 2310604319689812238703027)
            ·
              refine ⟨3465906479534718358054541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2310604319689812238703027 3465906479534718358054541)
              ·
                refine ⟨1299714929825519384270453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3465906479534718358054541 1299714929825519384270453)
                ·
                  refine ⟨121848274671142442275355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1299714929825519384270453 121848274671142442275355)
                  ·
                    rfl

theorem cell20_266961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_266961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_266961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_266961 prefixEnd_266961 := by exact prefixLift 266961
  have htrace : WordTrace (prefixWord ++ tailWord_266961) baseStart_266961 baseEnd_266961 := by
    simpa [prefixWord, tailWord_266961, baseEnd_266961] using wordTrace_append hprefix tailTrace_266961
  have hstable : (prefixWord ++ tailWord_266961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_266961).length < 2 ^ (prefixWord ++ tailWord_266961).sum := by decide
  have hdescent : baseEnd_266961 < baseStart_266961 := by decide
  rcases family_descends (prefixWord ++ tailWord_266961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267016 : List Nat := [2, 1, 3, 2, 2, 2, 1, 4, 3]
def baseStart_267016 : Nat := 118140960795 + 267016 * 2 ^ 59
def prefixEnd_267016 : Nat := 4983230072969 + 3 ^ 40 * 267016 * 2
def baseEnd_267016 : Nat := 121873378169806695441797

theorem tailTrace_267016 : CollatzResearch.WordTrace tailWord_267016 prefixEnd_267016 121873378169806695441797 := by
  unfold tailWord_267016
  simp only [CollatzResearch.WordTrace]
  refine ⟨4869436800327054773646451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6492582400436073031528601 4869436800327054773646451)
  ·
    refine ⟨7304155200490582160469677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4869436800327054773646451 7304155200490582160469677)
    ·
      refine ⟨2739058200183968310176129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7304155200490582160469677 2739058200183968310176129)
      ·
        refine ⟨2054293650137976232632097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2739058200183968310176129 2054293650137976232632097)
        ·
          refine ⟨1540720237603482174474073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2054293650137976232632097 1540720237603482174474073)
          ·
            refine ⟨1155540178202611630855555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1540720237603482174474073 1155540178202611630855555)
            ·
              refine ⟨1733310267303917446283333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1155540178202611630855555 1733310267303917446283333)
              ·
                refine ⟨324995675119484521178125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1733310267303917446283333 324995675119484521178125)
                ·
                  refine ⟨121873378169806695441797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 324995675119484521178125 121873378169806695441797)
                  ·
                    rfl

theorem cell20_267016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_267016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267016 prefixEnd_267016 := by exact prefixLift 267016
  have htrace : WordTrace (prefixWord ++ tailWord_267016) baseStart_267016 baseEnd_267016 := by
    simpa [prefixWord, tailWord_267016, baseEnd_267016] using wordTrace_append hprefix tailTrace_267016
  have hstable : (prefixWord ++ tailWord_267016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267016).length < 2 ^ (prefixWord ++ tailWord_267016).sum := by decide
  have hdescent : baseEnd_267016 < baseStart_267016 := by decide
  rcases family_descends (prefixWord ++ tailWord_267016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267053 : List Nat := [1, 5, 3, 2, 1, 1, 2, 3, 2]
def baseStart_267053 : Nat := 118140960795 + 267053 * 2 ^ 59
def prefixEnd_267053 : Nat := 4983230072969 + 3 ^ 40 * 267053 * 2
def baseEnd_267053 : Nat := 121890265977999011208313

theorem tailTrace_267053 : CollatzResearch.WordTrace tailWord_267053 prefixEnd_267053 121890265977999011208313 := by
  unfold tailWord_267053
  simp only [CollatzResearch.WordTrace]
  refine ⟨9740223101520064866389813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6493482067680043244259875 9740223101520064866389813)
  ·
    refine ⟨913145915767506081224045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9740223101520064866389813 913145915767506081224045)
    ·
      refine ⟨342429718412814780459017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 913145915767506081224045 342429718412814780459017)
      ·
        refine ⟨256822288809611085344263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 342429718412814780459017 256822288809611085344263)
        ·
          refine ⟨385233433214416628016395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256822288809611085344263 385233433214416628016395)
          ·
            refine ⟨577850149821624942024593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385233433214416628016395 577850149821624942024593)
            ·
              refine ⟨433387612366218706518445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 577850149821624942024593 433387612366218706518445)
              ·
                refine ⟨162520354637332014944417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 433387612366218706518445 162520354637332014944417)
                ·
                  refine ⟨121890265977999011208313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162520354637332014944417 121890265977999011208313)
                  ·
                    rfl

theorem cell20_267053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_267053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267053 prefixEnd_267053 := by exact prefixLift 267053
  have htrace : WordTrace (prefixWord ++ tailWord_267053) baseStart_267053 baseEnd_267053 := by
    simpa [prefixWord, tailWord_267053, baseEnd_267053] using wordTrace_append hprefix tailTrace_267053
  have hstable : (prefixWord ++ tailWord_267053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267053).length < 2 ^ (prefixWord ++ tailWord_267053).sum := by decide
  have hdescent : baseEnd_267053 < baseStart_267053 := by decide
  rcases family_descends (prefixWord ++ tailWord_267053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267071 : List Nat := [1, 1, 2, 2, 5, 3, 1, 2, 3]
def baseStart_267071 : Nat := 118140960795 + 267071 * 2 ^ 59
def prefixEnd_267071 : Nat := 4983230072969 + 3 ^ 40 * 267071 * 2
def baseEnd_267071 : Nat := 121898481668470948608239

theorem tailTrace_267071 : CollatzResearch.WordTrace tailWord_267071 prefixEnd_267071 121898481668470948608239 := by
  unfold tailWord_267071
  simp only [CollatzResearch.WordTrace]
  refine ⟨9740879615454853940545067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6493919743636569293696711 9740879615454853940545067)
  ·
    refine ⟨14611319423182280910817601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9740879615454853940545067 14611319423182280910817601)
    ·
      refine ⟨10958489567386710683113201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14611319423182280910817601 10958489567386710683113201)
      ·
        refine ⟨8218867175540033012334901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10958489567386710683113201 8218867175540033012334901)
        ·
          refine ⟨770518797706878094906397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8218867175540033012334901 770518797706878094906397)
          ·
            refine ⟨288944549140079285589899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 770518797706878094906397 288944549140079285589899)
            ·
              refine ⟨433416823710118928384849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 288944549140079285589899 433416823710118928384849)
              ·
                refine ⟨325062617782589196288637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433416823710118928384849 325062617782589196288637)
                ·
                  refine ⟨121898481668470948608239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325062617782589196288637 121898481668470948608239)
                  ·
                    rfl

theorem cell20_267071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 3].length) (baseStart_267071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267071 prefixEnd_267071 := by exact prefixLift 267071
  have htrace : WordTrace (prefixWord ++ tailWord_267071) baseStart_267071 baseEnd_267071 := by
    simpa [prefixWord, tailWord_267071, baseEnd_267071] using wordTrace_append hprefix tailTrace_267071
  have hstable : (prefixWord ++ tailWord_267071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267071).length < 2 ^ (prefixWord ++ tailWord_267071).sum := by decide
  have hdescent : baseEnd_267071 < baseStart_267071 := by decide
  rcases family_descends (prefixWord ++ tailWord_267071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267075 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 5]
def baseStart_267075 : Nat := 118140960795 + 267075 * 2 ^ 59
def prefixEnd_267075 : Nat := 4983230072969 + 3 ^ 40 * 267075 * 2
def baseEnd_267075 : Nat := 121900307377464712474889

theorem tailTrace_267075 : CollatzResearch.WordTrace tailWord_267075 prefixEnd_267075 121900307377464712474889 := by
  unfold tailWord_267075
  simp only [CollatzResearch.WordTrace]
  refine ⟨9741025507440362623690679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6494017004960241749127119 9741025507440362623690679)
  ·
    refine ⟨14611538261160543935536019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9741025507440362623690679 14611538261160543935536019)
    ·
      refine ⟨21917307391740815903304029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14611538261160543935536019 21917307391740815903304029)
      ·
        refine ⟨8218990271902805963739011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21917307391740815903304029 8218990271902805963739011)
        ·
          refine ⟨12328485407854208945608517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8218990271902805963739011 12328485407854208945608517)
          ·
            refine ⟨2311591013972664177301597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12328485407854208945608517 2311591013972664177301597)
            ·
              refine ⟨866846630239749066488099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2311591013972664177301597 866846630239749066488099)
              ·
                refine ⟨1300269945359623599732149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 866846630239749066488099 1300269945359623599732149)
                ·
                  refine ⟨121900307377464712474889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1300269945359623599732149 121900307377464712474889)
                  ·
                    rfl

theorem cell20_267075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 5].length) (baseStart_267075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267075 prefixEnd_267075 := by exact prefixLift 267075
  have htrace : WordTrace (prefixWord ++ tailWord_267075) baseStart_267075 baseEnd_267075 := by
    simpa [prefixWord, tailWord_267075, baseEnd_267075] using wordTrace_append hprefix tailTrace_267075
  have hstable : (prefixWord ++ tailWord_267075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267075).length < 2 ^ (prefixWord ++ tailWord_267075).sum := by decide
  have hdescent : baseEnd_267075 < baseStart_267075 := by decide
  rcases family_descends (prefixWord ++ tailWord_267075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267120 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 6]
def baseStart_267120 : Nat := 118140960795 + 267120 * 2 ^ 59
def prefixEnd_267120 : Nat := 4983230072969 + 3 ^ 40 * 267120 * 2
def baseEnd_267120 : Nat := 121920846603644555974705

theorem tailTrace_267120 : CollatzResearch.WordTrace tailWord_267120 prefixEnd_267120 121920846603644555974705 := by
  unfold tailWord_267120
  simp only [CollatzResearch.WordTrace]
  refine ⟨4871333396138667654539407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6495111194851556872719209 4871333396138667654539407)
  ·
    refine ⟨7307000094208001481809111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4871333396138667654539407 7307000094208001481809111)
    ·
      refine ⟨10960500141312002222713667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7307000094208001481809111 10960500141312002222713667)
      ·
        refine ⟨16440750211968003334070501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10960500141312002222713667 16440750211968003334070501)
        ·
          refine ⟨3082640664744000625138219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16440750211968003334070501 3082640664744000625138219)
          ·
            refine ⟨4623960997116000937707329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3082640664744000625138219 4623960997116000937707329)
            ·
              refine ⟨3467970747837000703280497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4623960997116000937707329 3467970747837000703280497)
              ·
                refine ⟨2600978060877750527460373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3467970747837000703280497 2600978060877750527460373)
                ·
                  refine ⟨121920846603644555974705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2600978060877750527460373 121920846603644555974705)
                  ·
                    rfl

theorem cell20_267120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_267120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267120 prefixEnd_267120 := by exact prefixLift 267120
  have htrace : WordTrace (prefixWord ++ tailWord_267120) baseStart_267120 baseEnd_267120 := by
    simpa [prefixWord, tailWord_267120, baseEnd_267120] using wordTrace_append hprefix tailTrace_267120
  have hstable : (prefixWord ++ tailWord_267120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267120).length < 2 ^ (prefixWord ++ tailWord_267120).sum := by decide
  have hdescent : baseEnd_267120 < baseStart_267120 := by decide
  rcases family_descends (prefixWord ++ tailWord_267120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267144 : List Nat := [2, 1, 3, 3, 2, 1, 1, 7]
def baseStart_267144 : Nat := 118140960795 + 267144 * 2 ^ 59
def prefixEnd_267144 : Nat := 4983230072969 + 3 ^ 40 * 267144 * 2
def baseEnd_267144 : Nat := 40643933619202379724869

theorem tailTrace_267144 : CollatzResearch.WordTrace tailWord_267144 prefixEnd_267144 40643933619202379724869 := by
  unfold tailWord_267144
  simp only [CollatzResearch.WordTrace]
  refine ⟨4871771072095193703976243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6495694762793591605301657 4871771072095193703976243)
  ·
    refine ⟨7307656608142790555964365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4871771072095193703976243 7307656608142790555964365)
    ·
      refine ⟨2740371228053546458486637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7307656608142790555964365 2740371228053546458486637)
      ·
        refine ⟨1027639210520079921932489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2740371228053546458486637 1027639210520079921932489)
        ·
          refine ⟨770729407890059941449367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1027639210520079921932489 770729407890059941449367)
          ·
            refine ⟨1156094111835089912174051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770729407890059941449367 1156094111835089912174051)
            ·
              refine ⟨1734141167752634868261077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1156094111835089912174051 1734141167752634868261077)
              ·
                refine ⟨40643933619202379724869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1734141167752634868261077 40643933619202379724869)
                ·
                  rfl

theorem cell20_267144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_267144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267144 prefixEnd_267144 := by exact prefixLift 267144
  have htrace : WordTrace (prefixWord ++ tailWord_267144) baseStart_267144 baseEnd_267144 := by
    simpa [prefixWord, tailWord_267144, baseEnd_267144] using wordTrace_append hprefix tailTrace_267144
  have hstable : (prefixWord ++ tailWord_267144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267144).length < 2 ^ (prefixWord ++ tailWord_267144).sum := by decide
  have hdescent : baseEnd_267144 < baseStart_267144 := by decide
  rcases family_descends (prefixWord ++ tailWord_267144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267185 : List Nat := [1, 2, 2, 4, 3, 1, 2, 2, 3]
def baseStart_267185 : Nat := 118140960795 + 267185 * 2 ^ 59
def prefixEnd_267185 : Nat := 4983230072969 + 3 ^ 40 * 267185 * 2
def baseEnd_267185 : Nat := 121950514374793218807773

theorem tailTrace_267185 : CollatzResearch.WordTrace tailWord_267185 prefixEnd_267185 121950514374793218807773 := by
  unfold tailWord_267185
  simp only [CollatzResearch.WordTrace]
  refine ⟨9745037537041851410195009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6496691691361234273463339 9745037537041851410195009)
  ·
    refine ⟨7308778152781388557646257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9745037537041851410195009 7308778152781388557646257)
    ·
      refine ⟨5481583614586041418234693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7308778152781388557646257 5481583614586041418234693)
      ·
        refine ⟨1027796927734882765919005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5481583614586041418234693 1027796927734882765919005)
        ·
          refine ⟨385423847900581037219627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1027796927734882765919005 385423847900581037219627)
          ·
            refine ⟨578135771850871555829441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385423847900581037219627 578135771850871555829441)
            ·
              refine ⟨433601828888153666872081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 578135771850871555829441 433601828888153666872081)
              ·
                refine ⟨325201371666115250154061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433601828888153666872081 325201371666115250154061)
                ·
                  refine ⟨121950514374793218807773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325201371666115250154061 121950514374793218807773)
                  ·
                    rfl

theorem cell20_267185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_267185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267185 prefixEnd_267185 := by exact prefixLift 267185
  have htrace : WordTrace (prefixWord ++ tailWord_267185) baseStart_267185 baseEnd_267185 := by
    simpa [prefixWord, tailWord_267185, baseEnd_267185] using wordTrace_append hprefix tailTrace_267185
  have hstable : (prefixWord ++ tailWord_267185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267185).length < 2 ^ (prefixWord ++ tailWord_267185).sum := by decide
  have hdescent : baseEnd_267185 < baseStart_267185 := by decide
  rcases family_descends (prefixWord ++ tailWord_267185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267188 : List Nat := [2, 5, 2, 1, 1, 2, 1, 4, 2]
def baseStart_267188 : Nat := 118140960795 + 267188 * 2 ^ 59
def prefixEnd_267188 : Nat := 4983230072969 + 3 ^ 40 * 267188 * 2
def baseEnd_267188 : Nat := 121951883656538541707761

theorem tailTrace_267188 : CollatzResearch.WordTrace tailWord_267188 prefixEnd_267188 121951883656538541707761 := by
  unfold tailWord_267188
  simp only [CollatzResearch.WordTrace]
  refine ⟨4872573478015491461277109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6496764637353988615036145 4872573478015491461277109)
  ·
    refine ⟨456803763563952324494729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4872573478015491461277109 456803763563952324494729)
    ·
      refine ⟨342602822672964243371047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 456803763563952324494729 342602822672964243371047)
      ·
        refine ⟨513904234009446365056571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342602822672964243371047 513904234009446365056571)
        ·
          refine ⟨770856351014169547584857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 513904234009446365056571 770856351014169547584857)
          ·
            refine ⟨578142263260627160688643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 770856351014169547584857 578142263260627160688643)
            ·
              refine ⟨867213394890940741032965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578142263260627160688643 867213394890940741032965)
              ·
                refine ⟨162602511542051388943681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 867213394890940741032965 162602511542051388943681)
                ·
                  refine ⟨121951883656538541707761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162602511542051388943681 121951883656538541707761)
                  ·
                    rfl

theorem cell20_267188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_267188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267188 prefixEnd_267188 := by exact prefixLift 267188
  have htrace : WordTrace (prefixWord ++ tailWord_267188) baseStart_267188 baseEnd_267188 := by
    simpa [prefixWord, tailWord_267188, baseEnd_267188] using wordTrace_append hprefix tailTrace_267188
  have hstable : (prefixWord ++ tailWord_267188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267188).length < 2 ^ (prefixWord ++ tailWord_267188).sum := by decide
  have hdescent : baseEnd_267188 < baseStart_267188 := by decide
  rcases family_descends (prefixWord ++ tailWord_267188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267192 : List Nat := [2, 1, 2, 1, 2, 5, 1, 4, 2]
def baseStart_267192 : Nat := 118140960795 + 267192 * 2 ^ 59
def prefixEnd_267192 : Nat := 4983230072969 + 3 ^ 40 * 267192 * 2
def baseEnd_267192 : Nat := 121953709365532305574411

theorem tailTrace_267192 : CollatzResearch.WordTrace tailWord_267192 prefixEnd_267192 121953709365532305574411 := by
  unfold tailWord_267192
  simp only [CollatzResearch.WordTrace]
  refine ⟨4872646424008245802849915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6496861898677661070466553 4872646424008245802849915)
  ·
    refine ⟨7308969636012368704274873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4872646424008245802849915 7308969636012368704274873)
    ·
      refine ⟨5481727227009276528206155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7308969636012368704274873 5481727227009276528206155)
      ·
        refine ⟨8222590840513914792309233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5481727227009276528206155 8222590840513914792309233)
        ·
          refine ⟨6166943130385436094231925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8222590840513914792309233 6166943130385436094231925)
          ·
            refine ⟨578150918473634633834243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6166943130385436094231925 578150918473634633834243)
            ·
              refine ⟨867226377710451950751365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578150918473634633834243 867226377710451950751365)
              ·
                refine ⟨162604945820709740765881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 867226377710451950751365 162604945820709740765881)
                ·
                  refine ⟨121953709365532305574411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162604945820709740765881 121953709365532305574411)
                  ·
                    rfl

theorem cell20_267192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 4, 2].length) (baseStart_267192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267192 prefixEnd_267192 := by exact prefixLift 267192
  have htrace : WordTrace (prefixWord ++ tailWord_267192) baseStart_267192 baseEnd_267192 := by
    simpa [prefixWord, tailWord_267192, baseEnd_267192] using wordTrace_append hprefix tailTrace_267192
  have hstable : (prefixWord ++ tailWord_267192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267192).length < 2 ^ (prefixWord ++ tailWord_267192).sum := by decide
  have hdescent : baseEnd_267192 < baseStart_267192 := by decide
  rcases family_descends (prefixWord ++ tailWord_267192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267237 : List Nat := [1, 3, 1, 6, 1, 1, 7]
def baseStart_267237 : Nat := 118140960795 + 267237 * 2 ^ 59
def prefixEnd_267237 : Nat := 4983230072969 + 3 ^ 40 * 267237 * 2
def baseEnd_267237 : Nat := 13552694287968016563803

theorem tailTrace_267237 : CollatzResearch.WordTrace tailWord_267237 prefixEnd_267237 13552694287968016563803 := by
  unfold tailWord_267237
  simp only [CollatzResearch.WordTrace]
  refine ⟨9746934132853464291087965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6497956088568976194058643 9746934132853464291087965)
  ·
    refine ⟨3655100299820049109157987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9746934132853464291087965 3655100299820049109157987)
    ·
      refine ⟨5482650449730073663736981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3655100299820049109157987 5482650449730073663736981)
      ·
        refine ⟨256999239831097202987671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5482650449730073663736981 256999239831097202987671)
        ·
          refine ⟨385498859746645804481507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 256999239831097202987671 385498859746645804481507)
          ·
            refine ⟨578248289619968706722261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 385498859746645804481507 578248289619968706722261)
            ·
              refine ⟨13552694287968016563803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 578248289619968706722261 13552694287968016563803)
              ·
                rfl

theorem cell20_267237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 7].length) (baseStart_267237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267237 prefixEnd_267237 := by exact prefixLift 267237
  have htrace : WordTrace (prefixWord ++ tailWord_267237) baseStart_267237 baseEnd_267237 := by
    simpa [prefixWord, tailWord_267237, baseEnd_267237] using wordTrace_append hprefix tailTrace_267237
  have hstable : (prefixWord ++ tailWord_267237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267237).length < 2 ^ (prefixWord ++ tailWord_267237).sum := by decide
  have hdescent : baseEnd_267237 < baseStart_267237 := by decide
  rcases family_descends (prefixWord ++ tailWord_267237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267275 : List Nat := [1, 1, 1, 1, 6, 4, 2, 4]
def baseStart_267275 : Nat := 118140960795 + 267275 * 2 ^ 59
def prefixEnd_267275 : Nat := 4983230072969 + 3 ^ 40 * 267275 * 2
def baseEnd_267275 : Nat := 40663864275717635269135

theorem tailTrace_267275 : CollatzResearch.WordTrace tailWord_267275 prefixEnd_267275 40663864275717635269135 := by
  unfold tailWord_267275
  simp only [CollatzResearch.WordTrace]
  refine ⟨9748320106715796780971279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6498880071143864520647519 9748320106715796780971279)
  ·
    refine ⟨14622480160073695171456919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9748320106715796780971279 14622480160073695171456919)
    ·
      refine ⟨21933720240110542757185379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14622480160073695171456919 21933720240110542757185379)
      ·
        refine ⟨32900580360165814135778069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21933720240110542757185379 32900580360165814135778069)
        ·
          refine ⟨1542214704382772537614597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32900580360165814135778069 1542214704382772537614597)
          ·
            refine ⟨289165257071769850802737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1542214704382772537614597 289165257071769850802737)
            ·
              refine ⟨216873942803827388102053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289165257071769850802737 216873942803827388102053)
              ·
                refine ⟨40663864275717635269135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 216873942803827388102053 40663864275717635269135)
                ·
                  rfl

theorem cell20_267275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 4].length) (baseStart_267275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267275 prefixEnd_267275 := by exact prefixLift 267275
  have htrace : WordTrace (prefixWord ++ tailWord_267275) baseStart_267275 baseEnd_267275 := by
    simpa [prefixWord, tailWord_267275, baseEnd_267275] using wordTrace_append hprefix tailTrace_267275
  have hstable : (prefixWord ++ tailWord_267275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267275).length < 2 ^ (prefixWord ++ tailWord_267275).sum := by decide
  have hdescent : baseEnd_267275 < baseStart_267275 := by decide
  rcases family_descends (prefixWord ++ tailWord_267275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267285 : List Nat := [1, 3, 2, 1, 4, 3, 1, 3, 2]
def baseStart_267285 : Nat := 118140960795 + 267285 * 2 ^ 59
def prefixEnd_267285 : Nat := 4983230072969 + 3 ^ 40 * 267285 * 2
def baseEnd_267285 : Nat := 121996157099637315474031

theorem tailTrace_267285 : CollatzResearch.WordTrace tailWord_267285 prefixEnd_267285 121996157099637315474031 := by
  unfold tailWord_267285
  simp only [CollatzResearch.WordTrace]
  refine ⟨9748684836679568488835309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6499123224453045659223539 9748684836679568488835309)
  ·
    refine ⟨3655756813754838183313241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9748684836679568488835309 3655756813754838183313241)
    ·
      refine ⟨2741817610316128637484931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3655756813754838183313241 2741817610316128637484931)
      ·
        refine ⟨4112726415474192956227397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2741817610316128637484931 4112726415474192956227397)
        ·
          refine ⟨771136202901411179292637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4112726415474192956227397 771136202901411179292637)
          ·
            refine ⟨289176076088029192234739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 771136202901411179292637 289176076088029192234739)
            ·
              refine ⟨433764114132043788352109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289176076088029192234739 433764114132043788352109)
              ·
                refine ⟨162661542799516420632041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 433764114132043788352109 162661542799516420632041)
                ·
                  refine ⟨121996157099637315474031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162661542799516420632041 121996157099637315474031)
                  ·
                    rfl

theorem cell20_267285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 3, 2].length) (baseStart_267285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267285 prefixEnd_267285 := by exact prefixLift 267285
  have htrace : WordTrace (prefixWord ++ tailWord_267285) baseStart_267285 baseEnd_267285 := by
    simpa [prefixWord, tailWord_267285, baseEnd_267285] using wordTrace_append hprefix tailTrace_267285
  have hstable : (prefixWord ++ tailWord_267285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267285).length < 2 ^ (prefixWord ++ tailWord_267285).sum := by decide
  have hdescent : baseEnd_267285 < baseStart_267285 := by decide
  rcases family_descends (prefixWord ++ tailWord_267285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267316 : List Nat := [2, 5, 1, 2, 1, 1, 4, 1, 3]
def baseStart_267316 : Nat := 118140960795 + 267316 * 2 ^ 59
def prefixEnd_267316 : Nat := 4983230072969 + 3 ^ 40 * 267316 * 2
def baseEnd_267316 : Nat := 122010306344338985440571

theorem tailTrace_267316 : CollatzResearch.WordTrace tailWord_267316 prefixEnd_267316 122010306344338985440571 := by
  unfold tailWord_267316
  simp only [CollatzResearch.WordTrace]
  refine ⟨4874907749783630391606901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6499876999711507188809201 4874907749783630391606901)
  ·
    refine ⟨457022601542215349213147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4874907749783630391606901 457022601542215349213147)
    ·
      refine ⟨685533902313323023819721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 457022601542215349213147 685533902313323023819721)
      ·
        refine ⟨514150426734992267864791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 685533902313323023819721 514150426734992267864791)
        ·
          refine ⟨771225640102488401797187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 514150426734992267864791 771225640102488401797187)
          ·
            refine ⟨1156838460153732602695781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 771225640102488401797187 1156838460153732602695781)
            ·
              refine ⟨216907211278824863005459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1156838460153732602695781 216907211278824863005459)
              ·
                refine ⟨325360816918237294508189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216907211278824863005459 325360816918237294508189)
                ·
                  refine ⟨122010306344338985440571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325360816918237294508189 122010306344338985440571)
                  ·
                    rfl

theorem cell20_267316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_267316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267316 prefixEnd_267316 := by exact prefixLift 267316
  have htrace : WordTrace (prefixWord ++ tailWord_267316) baseStart_267316 baseEnd_267316 := by
    simpa [prefixWord, tailWord_267316, baseEnd_267316] using wordTrace_append hprefix tailTrace_267316
  have hstable : (prefixWord ++ tailWord_267316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267316).length < 2 ^ (prefixWord ++ tailWord_267316).sum := by decide
  have hdescent : baseEnd_267316 < baseStart_267316 := by decide
  rcases family_descends (prefixWord ++ tailWord_267316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267320 : List Nat := [2, 1, 2, 1, 5, 2, 1, 3, 3]
def baseStart_267320 : Nat := 118140960795 + 267320 * 2 ^ 59
def prefixEnd_267320 : Nat := 4983230072969 + 3 ^ 40 * 267320 * 2
def baseEnd_267320 : Nat := 122012132053332749307221

theorem tailTrace_267320 : CollatzResearch.WordTrace tailWord_267320 prefixEnd_267320 122012132053332749307221 := by
  unfold tailWord_267320
  simp only [CollatzResearch.WordTrace]
  refine ⟨4874980695776384733179707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6499974261035179644239609 4874980695776384733179707)
  ·
    refine ⟨7312471043664577099769561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4874980695776384733179707 7312471043664577099769561)
    ·
      refine ⟨5484353282748432824827171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7312471043664577099769561 5484353282748432824827171)
      ·
        refine ⟨8226529924122649237240757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5484353282748432824827171 8226529924122649237240757)
        ·
          refine ⟨771237180386498365991321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8226529924122649237240757 771237180386498365991321)
          ·
            refine ⟨578427885289873774493491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 771237180386498365991321 578427885289873774493491)
            ·
              refine ⟨867641827934810661740237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 578427885289873774493491 867641827934810661740237)
              ·
                refine ⟨325365685475553998152589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 867641827934810661740237 325365685475553998152589)
                ·
                  refine ⟨122012132053332749307221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 325365685475553998152589 122012132053332749307221)
                  ·
                    rfl

theorem cell20_267320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_267320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267320 prefixEnd_267320 := by exact prefixLift 267320
  have htrace : WordTrace (prefixWord ++ tailWord_267320) baseStart_267320 baseEnd_267320 := by
    simpa [prefixWord, tailWord_267320, baseEnd_267320] using wordTrace_append hprefix tailTrace_267320
  have hstable : (prefixWord ++ tailWord_267320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267320).length < 2 ^ (prefixWord ++ tailWord_267320).sum := by decide
  have hdescent : baseEnd_267320 < baseStart_267320 := by decide
  rcases family_descends (prefixWord ++ tailWord_267320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267357 : List Nat := [1, 4, 4, 1, 2, 2, 2, 2, 2]
def baseStart_267357 : Nat := 118140960795 + 267357 * 2 ^ 59
def prefixEnd_267357 : Nat := 4983230072969 + 3 ^ 40 * 267357 * 2
def baseEnd_267357 : Nat := 122029019861525065073737

theorem tailTrace_267357 : CollatzResearch.WordTrace tailWord_267357 prefixEnd_267357 122029019861525065073737 := by
  unfold tailWord_267357
  simp only [CollatzResearch.WordTrace]
  refine ⟨9751310892418724785456325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6500873928279149856970883 9751310892418724785456325)
  ·
    refine ⟨1828370792328510897273061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9751310892418724785456325 1828370792328510897273061)
    ·
      refine ⟨342819523561595793238699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1828370792328510897273061 342819523561595793238699)
      ·
        refine ⟨514229285342393689858049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 342819523561595793238699 514229285342393689858049)
        ·
          refine ⟨385671964006795267393537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 514229285342393689858049 385671964006795267393537)
          ·
            refine ⟨289253973005096450545153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385671964006795267393537 289253973005096450545153)
            ·
              refine ⟨216940479753822337908865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 289253973005096450545153 216940479753822337908865)
              ·
                refine ⟨162705359815366753431649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 216940479753822337908865 162705359815366753431649)
                ·
                  refine ⟨122029019861525065073737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162705359815366753431649 122029019861525065073737)
                  ·
                    rfl

theorem cell20_267357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_267357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267357 prefixEnd_267357 := by exact prefixLift 267357
  have htrace : WordTrace (prefixWord ++ tailWord_267357) baseStart_267357 baseEnd_267357 := by
    simpa [prefixWord, tailWord_267357, baseEnd_267357] using wordTrace_append hprefix tailTrace_267357
  have hstable : (prefixWord ++ tailWord_267357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267357).length < 2 ^ (prefixWord ++ tailWord_267357).sum := by decide
  have hdescent : baseEnd_267357 < baseStart_267357 := by decide
  rcases family_descends (prefixWord ++ tailWord_267357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267368 : List Nat := [2, 1, 4, 4, 1, 2, 1, 5]
def baseStart_267368 : Nat := 118140960795 + 267368 * 2 ^ 59
def prefixEnd_267368 : Nat := 4983230072969 + 3 ^ 40 * 267368 * 2
def baseEnd_267368 : Nat := 40678013520419305235675

theorem tailTrace_267368 : CollatzResearch.WordTrace tailWord_267368 prefixEnd_267368 40678013520419305235675 := by
  unfold tailWord_267368
  simp only [CollatzResearch.WordTrace]
  refine ⟨4875856047689436832053379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6501141396919249109404505 4875856047689436832053379)
  ·
    refine ⟨7313784071534155248080069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4875856047689436832053379 7313784071534155248080069)
    ·
      refine ⟨1371334513412654109015013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7313784071534155248080069 1371334513412654109015013)
      ·
        refine ⟨257125221264872645440315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1371334513412654109015013 257125221264872645440315)
        ·
          refine ⟨385687831897308968160473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257125221264872645440315 385687831897308968160473)
          ·
            refine ⟨289265873922981726120355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385687831897308968160473 289265873922981726120355)
            ·
              refine ⟨433898810884472589180533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289265873922981726120355 433898810884472589180533)
              ·
                refine ⟨40678013520419305235675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 433898810884472589180533 40678013520419305235675)
                ·
                  rfl

theorem cell20_267368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 5].length) (baseStart_267368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267368 prefixEnd_267368 := by exact prefixLift 267368
  have htrace : WordTrace (prefixWord ++ tailWord_267368) baseStart_267368 baseEnd_267368 := by
    simpa [prefixWord, tailWord_267368, baseEnd_267368] using wordTrace_append hprefix tailTrace_267368
  have hstable : (prefixWord ++ tailWord_267368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267368).length < 2 ^ (prefixWord ++ tailWord_267368).sum := by decide
  have hdescent : baseEnd_267368 < baseStart_267368 := by decide
  rcases family_descends (prefixWord ++ tailWord_267368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267410 : List Nat := [3, 2, 3, 1, 1, 3, 7]
def baseStart_267410 : Nat := 118140960795 + 267410 * 2 ^ 59
def prefixEnd_267410 : Nat := 4983230072969 + 3 ^ 40 * 267410 * 2
def baseEnd_267410 : Nat := 13561467833965826256317

theorem tailTrace_267410 : CollatzResearch.WordTrace tailWord_267410 prefixEnd_267410 13561467833965826256317 := by
  unfold tailWord_267410
  simp only [CollatzResearch.WordTrace]
  refine ⟨2438310990306678709283921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6502162640817809891423789 2438310990306678709283921)
  ·
    refine ⟨1828733242730009031962941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2438310990306678709283921 1828733242730009031962941)
    ·
      refine ⟨685774966023753386986103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1828733242730009031962941 685774966023753386986103)
      ·
        refine ⟨1028662449035630080479155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 685774966023753386986103 1028662449035630080479155)
        ·
          refine ⟨1542993673553445120718733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1028662449035630080479155 1542993673553445120718733)
          ·
            refine ⟨578622627582541920269525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1542993673553445120718733 578622627582541920269525)
            ·
              refine ⟨13561467833965826256317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 578622627582541920269525 13561467833965826256317)
              ·
                rfl

theorem cell20_267410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 7].length) (baseStart_267410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267410 prefixEnd_267410 := by exact prefixLift 267410
  have htrace : WordTrace (prefixWord ++ tailWord_267410) baseStart_267410 baseEnd_267410 := by
    simpa [prefixWord, tailWord_267410, baseEnd_267410] using wordTrace_append hprefix tailTrace_267410
  have hstable : (prefixWord ++ tailWord_267410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267410).length < 2 ^ (prefixWord ++ tailWord_267410).sum := by decide
  have hdescent : baseEnd_267410 < baseStart_267410 := by decide
  rcases family_descends (prefixWord ++ tailWord_267410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_267420 : List Nat := [2, 2, 3, 2, 1, 2, 2, 4, 2]
def baseStart_267420 : Nat := 118140960795 + 267420 * 2 ^ 59
def prefixEnd_267420 : Nat := 4983230072969 + 3 ^ 40 * 267420 * 2
def baseEnd_267420 : Nat := 122057774778176845973479

theorem tailTrace_267420 : CollatzResearch.WordTrace tailWord_267420 prefixEnd_267420 122057774778176845973479 := by
  unfold tailWord_267420
  simp only [CollatzResearch.WordTrace]
  refine ⟨4876804345595243272499857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6502405794126991029999809 4876804345595243272499857)
  ·
    refine ⟨3657603259196432454374893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4876804345595243272499857 3657603259196432454374893)
    ·
      refine ⟨1371601222198662170390585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3657603259196432454374893 1371601222198662170390585)
      ·
        refine ⟨1028700916648996627792939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1371601222198662170390585 1028700916648996627792939)
        ·
          refine ⟨1543051374973494941689409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1028700916648996627792939 1543051374973494941689409)
          ·
            refine ⟨1157288531230121206267057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1543051374973494941689409 1157288531230121206267057)
            ·
              refine ⟨867966398422590904700293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1157288531230121206267057 867966398422590904700293)
              ·
                refine ⟨162743699704235794631305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 867966398422590904700293 162743699704235794631305)
                ·
                  refine ⟨122057774778176845973479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 162743699704235794631305 122057774778176845973479)
                  ·
                    rfl

theorem cell20_267420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_267420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_267420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_267420 prefixEnd_267420 := by exact prefixLift 267420
  have htrace : WordTrace (prefixWord ++ tailWord_267420) baseStart_267420 baseEnd_267420 := by
    simpa [prefixWord, tailWord_267420, baseEnd_267420] using wordTrace_append hprefix tailTrace_267420
  have hstable : (prefixWord ++ tailWord_267420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_267420).length < 2 ^ (prefixWord ++ tailWord_267420).sum := by decide
  have hdescent : baseEnd_267420 < baseStart_267420 := by decide
  rcases family_descends (prefixWord ++ tailWord_267420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
