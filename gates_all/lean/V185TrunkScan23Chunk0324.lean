import V185TrunkScan23Chunk0323

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1915962 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3]
def baseStart_1915962 : Nat := 118140960795 + 1915962 * 2 ^ 59
def prefixEnd_1915962 : Nat := 4983230072969 + 3 ^ 40 * 1915962 * 2
def baseEnd_1915962 : Nat := 983809421749738023563657

theorem tailTrace_1915962 : CollatzResearch.WordTrace tailWord_1915962 prefixEnd_1915962 983809421749738023563657 := by
  unfold tailWord_1915962
  simp only [CollatzResearch.WordTrace]
  refine ⟨17470218771201092275843535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46587250056536246068916093 17470218771201092275843535)
  ·
    refine ⟨26205328156801638413765303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17470218771201092275843535 26205328156801638413765303)
    ·
      refine ⟨39307992235202457620647955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26205328156801638413765303 39307992235202457620647955)
      ·
        refine ⟨58961988352803686430971933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39307992235202457620647955 58961988352803686430971933)
        ·
          refine ⟨22110745632301382411614475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58961988352803686430971933 22110745632301382411614475)
          ·
            refine ⟨33166118448452073617421713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22110745632301382411614475 33166118448452073617421713)
            ·
              refine ⟨24874588836339055213066285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33166118448452073617421713 24874588836339055213066285)
              ·
                refine ⟨9327970813627145704899857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24874588836339055213066285 9327970813627145704899857)
                ·
                  refine ⟨6995978110220359278674893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9327970813627145704899857 6995978110220359278674893)
                  ·
                    refine ⟨2623491791332634729503085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6995978110220359278674893 2623491791332634729503085)
                    ·
                      refine ⟨983809421749738023563657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2623491791332634729503085 983809421749738023563657)
                      ·
                        rfl

theorem cell23_1915962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_1915962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1915962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1915962 prefixEnd_1915962 := by exact prefixLift 1915962
  have htrace : WordTrace (prefixWord ++ tailWord_1915962) baseStart_1915962 baseEnd_1915962 := by
    simpa [prefixWord, tailWord_1915962, baseEnd_1915962] using wordTrace_append hprefix tailTrace_1915962
  have hstable : (prefixWord ++ tailWord_1915962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1915962).length < 2 ^ (prefixWord ++ tailWord_1915962).sum := by decide
  have hdescent : baseEnd_1915962 < baseStart_1915962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1915962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916029 : List Nat := [1, 4, 1, 1, 3, 1, 3, 2, 3, 4]
def baseStart_1916029 : Nat := 118140960795 + 1916029 * 2 ^ 59
def prefixEnd_1916029 : Nat := 4983230072969 + 3 ^ 40 * 1916029 * 2
def baseEnd_1916029 : Nat := 327947941651196420475283

theorem tailTrace_1916029 : CollatzResearch.WordTrace tailWord_1916029 prefixEnd_1916029 327947941651196420475283 := by
  unfold tailWord_1916029
  simp only [CollatzResearch.WordTrace]
  refine ⟨69883318775561639546063141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46588879183707759697375427 69883318775561639546063141)
  ·
    refine ⟨13103122270417807414886839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69883318775561639546063141 13103122270417807414886839)
    ·
      refine ⟨19654683405626711122330259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13103122270417807414886839 19654683405626711122330259)
      ·
        refine ⟨29482025108440066683495389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19654683405626711122330259 29482025108440066683495389)
        ·
          refine ⟨11055759415665025006310771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29482025108440066683495389 11055759415665025006310771)
          ·
            refine ⟨16583639123497537509466157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11055759415665025006310771 16583639123497537509466157)
            ·
              refine ⟨6218864671311576566049809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16583639123497537509466157 6218864671311576566049809)
              ·
                refine ⟨4664148503483682424537357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6218864671311576566049809 4664148503483682424537357)
                ·
                  refine ⟨1749055688806380909201509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4664148503483682424537357 1749055688806380909201509)
                  ·
                    refine ⟨327947941651196420475283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1749055688806380909201509 327947941651196420475283)
                    ·
                      rfl

theorem cell23_1916029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_1916029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916029 prefixEnd_1916029 := by exact prefixLift 1916029
  have htrace : WordTrace (prefixWord ++ tailWord_1916029) baseStart_1916029 baseEnd_1916029 := by
    simpa [prefixWord, tailWord_1916029, baseEnd_1916029] using wordTrace_append hprefix tailTrace_1916029
  have hstable : (prefixWord ++ tailWord_1916029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916029).length < 2 ^ (prefixWord ++ tailWord_1916029).sum := by decide
  have hdescent : baseEnd_1916029 < baseStart_1916029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916036 : List Nat := [2, 3, 2, 1, 2, 4, 1, 1, 2, 1, 4]
def baseStart_1916036 : Nat := 118140960795 + 1916036 * 2 ^ 59
def prefixEnd_1916036 : Nat := 4983230072969 + 3 ^ 40 * 1916036 * 2
def baseEnd_1916036 : Nat := 983847419318170734038317

theorem tailTrace_1916036 : CollatzResearch.WordTrace tailWord_1916036 prefixEnd_1916036 983847419318170734038317 := by
  unfold tailWord_1916036
  simp only [CollatzResearch.WordTrace]
  refine ⟨34941787043268139870783981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46589049391024186494378641 34941787043268139870783981)
  ·
    refine ⟨13103170141225552451543993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34941787043268139870783981 13103170141225552451543993)
    ·
      refine ⟨9827377605919164338657995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13103170141225552451543993 9827377605919164338657995)
      ·
        refine ⟨14741066408878746507986993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9827377605919164338657995 14741066408878746507986993)
        ·
          refine ⟨11055799806659059880990245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14741066408878746507986993 11055799806659059880990245)
          ·
            refine ⟨2072962463748573727685671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11055799806659059880990245 2072962463748573727685671)
            ·
              refine ⟨3109443695622860591528507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2072962463748573727685671 3109443695622860591528507)
              ·
                refine ⟨4664165543434290887292761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3109443695622860591528507 4664165543434290887292761)
                ·
                  refine ⟨3498124157575718165469571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4664165543434290887292761 3498124157575718165469571)
                  ·
                    refine ⟨5247186236363577248204357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3498124157575718165469571 5247186236363577248204357)
                    ·
                      refine ⟨983847419318170734038317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5247186236363577248204357 983847419318170734038317)
                      ·
                        rfl

theorem cell23_1916036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_1916036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916036 prefixEnd_1916036 := by exact prefixLift 1916036
  have htrace : WordTrace (prefixWord ++ tailWord_1916036) baseStart_1916036 baseEnd_1916036 := by
    simpa [prefixWord, tailWord_1916036, baseEnd_1916036] using wordTrace_append hprefix tailTrace_1916036
  have hstable : (prefixWord ++ tailWord_1916036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916036).length < 2 ^ (prefixWord ++ tailWord_1916036).sum := by decide
  have hdescent : baseEnd_1916036 < baseStart_1916036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916042 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 8]
def baseStart_1916042 : Nat := 118140960795 + 1916042 * 2 ^ 59
def prefixEnd_1916042 : Nat := 4983230072969 + 3 ^ 40 * 1916042 * 2
def baseEnd_1916042 : Nat := 109316722244677523395921

theorem tailTrace_1916042 : CollatzResearch.WordTrace tailWord_1916042 prefixEnd_1916042 109316722244677523395921 := by
  unfold tailWord_1916042
  simp only [CollatzResearch.WordTrace]
  refine ⟨17470948231128635691571595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46589195283009695177524253 17470948231128635691571595)
  ·
    refine ⟨26206422346692953537357393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17470948231128635691571595 26206422346692953537357393)
    ·
      refine ⟨19654816760019715153018045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26206422346692953537357393 19654816760019715153018045)
      ·
        refine ⟨7370556285007393182381767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19654816760019715153018045 7370556285007393182381767)
        ·
          refine ⟨11055834427511089773572651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7370556285007393182381767 11055834427511089773572651)
          ·
            refine ⟨16583751641266634660358977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11055834427511089773572651 16583751641266634660358977)
            ·
              refine ⟨12437813730949975995269233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16583751641266634660358977 12437813730949975995269233)
              ·
                refine ⟨9328360298212481996451925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12437813730949975995269233 9328360298212481996451925)
                ·
                  refine ⟨109316722244677523395921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9328360298212481996451925 109316722244677523395921)
                  ·
                    rfl

theorem cell23_1916042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 8].length) (baseStart_1916042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916042 prefixEnd_1916042 := by exact prefixLift 1916042
  have htrace : WordTrace (prefixWord ++ tailWord_1916042) baseStart_1916042 baseEnd_1916042 := by
    simpa [prefixWord, tailWord_1916042, baseEnd_1916042] using wordTrace_append hprefix tailTrace_1916042
  have hstable : (prefixWord ++ tailWord_1916042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916042).length < 2 ^ (prefixWord ++ tailWord_1916042).sum := by decide
  have hdescent : baseEnd_1916042 < baseStart_1916042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916079 : List Nat := [1, 1, 2, 1, 2, 3, 3, 2, 1, 5, 2]
def baseStart_1916079 : Nat := 118140960795 + 1916079 * 2 ^ 59
def prefixEnd_1916079 : Nat := 4983230072969 + 3 ^ 40 * 1916079 * 2
def baseEnd_1916079 : Nat := 983869498986314065800619

theorem tailTrace_1916079 : CollatzResearch.WordTrace tailWord_1916079 prefixEnd_1916079 983869498986314065800619 := by
  unfold tailWord_1916079
  simp only [CollatzResearch.WordTrace]
  refine ⟨69885142425380498085383291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46590094950253665390255527 69885142425380498085383291)
  ·
    refine ⟨104827713638070747128074937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69885142425380498085383291 104827713638070747128074937)
    ·
      refine ⟨78620785228553060346056203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104827713638070747128074937 78620785228553060346056203)
      ·
        refine ⟨117931177842829590519084305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78620785228553060346056203 117931177842829590519084305)
        ·
          refine ⟨88448383382122192889313229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117931177842829590519084305 88448383382122192889313229)
          ·
            refine ⟨33168143768295822333492461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88448383382122192889313229 33168143768295822333492461)
            ·
              refine ⟨12438053913110933375059673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33168143768295822333492461 12438053913110933375059673)
              ·
                refine ⟨9328540434833200031294755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12438053913110933375059673 9328540434833200031294755)
                ·
                  refine ⟨13992810652249800046942133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9328540434833200031294755 13992810652249800046942133)
                  ·
                    refine ⟨1311825998648418754400825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13992810652249800046942133 1311825998648418754400825)
                    ·
                      refine ⟨983869498986314065800619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1311825998648418754400825 983869498986314065800619)
                      ·
                        rfl

theorem cell23_1916079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 5, 2].length) (baseStart_1916079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916079 prefixEnd_1916079 := by exact prefixLift 1916079
  have htrace : WordTrace (prefixWord ++ tailWord_1916079) baseStart_1916079 baseEnd_1916079 := by
    simpa [prefixWord, tailWord_1916079, baseEnd_1916079] using wordTrace_append hprefix tailTrace_1916079
  have hstable : (prefixWord ++ tailWord_1916079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916079).length < 2 ^ (prefixWord ++ tailWord_1916079).sum := by decide
  have hdescent : baseEnd_1916079 < baseStart_1916079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916089 : List Nat := [1, 2, 1, 4, 1, 3, 1, 4, 1, 5]
def baseStart_1916089 : Nat := 118140960795 + 1916089 * 2 ^ 59
def prefixEnd_1916089 : Nat := 4983230072969 + 3 ^ 40 * 1916089 * 2
def baseEnd_1916089 : Nat := 327958211264286342225191

theorem tailTrace_1916089 : CollatzResearch.WordTrace tailWord_1916089 prefixEnd_1916089 327958211264286342225191 := by
  unfold tailWord_1916089
  simp only [CollatzResearch.WordTrace]
  refine ⟨69885507155344269793247321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46590338103562846528831547 69885507155344269793247321)
  ·
    refine ⟨52414130366508202344935491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69885507155344269793247321 52414130366508202344935491)
    ·
      refine ⟨78621195549762303517403237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52414130366508202344935491 78621195549762303517403237)
      ·
        refine ⟨14741474165580431909513107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78621195549762303517403237 14741474165580431909513107)
        ·
          refine ⟨22112211248370647864269661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14741474165580431909513107 22112211248370647864269661)
          ·
            refine ⟨8292079218138992949101123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22112211248370647864269661 8292079218138992949101123)
            ·
              refine ⟨12438118827208489423651685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8292079218138992949101123 12438118827208489423651685)
              ·
                refine ⟨2332147280101591766934691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12438118827208489423651685 2332147280101591766934691)
                ·
                  refine ⟨3498220920152387650402037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332147280101591766934691 3498220920152387650402037)
                  ·
                    refine ⟨327958211264286342225191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3498220920152387650402037 327958211264286342225191)
                    ·
                      rfl

theorem cell23_1916089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 5].length) (baseStart_1916089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916089 prefixEnd_1916089 := by exact prefixLift 1916089
  have htrace : WordTrace (prefixWord ++ tailWord_1916089) baseStart_1916089 baseEnd_1916089 := by
    simpa [prefixWord, tailWord_1916089, baseEnd_1916089] using wordTrace_append hprefix tailTrace_1916089
  have hstable : (prefixWord ++ tailWord_1916089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916089).length < 2 ^ (prefixWord ++ tailWord_1916089).sum := by decide
  have hdescent : baseEnd_1916089 < baseStart_1916089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916119 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 4, 4]
def baseStart_1916119 : Nat := 118140960795 + 1916119 * 2 ^ 59
def prefixEnd_1916119 : Nat := 4983230072969 + 3 ^ 40 * 1916119 * 2
def baseEnd_1916119 : Nat := 327963346070831303100145

theorem tailTrace_1916119 : CollatzResearch.WordTrace tailWord_1916119 prefixEnd_1916119 327963346070831303100145 := by
  unfold tailWord_1916119
  simp only [CollatzResearch.WordTrace]
  refine ⟨69886601345235584916839411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46591067563490389944559607 69886601345235584916839411)
  ·
    refine ⟨104829902017853377375259117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69886601345235584916839411 104829902017853377375259117)
    ·
      refine ⟨39311213256695016515722169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104829902017853377375259117 39311213256695016515722169)
      ·
        refine ⟨29483409942521262386791627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39311213256695016515722169 29483409942521262386791627)
        ·
          refine ⟨44225114913781893580187441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29483409942521262386791627 44225114913781893580187441)
          ·
            refine ⟨33168836185336420185140581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44225114913781893580187441 33168836185336420185140581)
            ·
              refine ⟨6219156784750578784713859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33168836185336420185140581 6219156784750578784713859)
              ·
                refine ⟨9328735177125868177070789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6219156784750578784713859 9328735177125868177070789)
                ·
                  refine ⟨1749137845711100283200773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9328735177125868177070789 1749137845711100283200773)
                  ·
                    refine ⟨327963346070831303100145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1749137845711100283200773 327963346070831303100145)
                    ·
                      rfl

theorem cell23_1916119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 4].length) (baseStart_1916119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916119 prefixEnd_1916119 := by exact prefixLift 1916119
  have htrace : WordTrace (prefixWord ++ tailWord_1916119) baseStart_1916119 baseEnd_1916119 := by
    simpa [prefixWord, tailWord_1916119, baseEnd_1916119] using wordTrace_append hprefix tailTrace_1916119
  have hstable : (prefixWord ++ tailWord_1916119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916119).length < 2 ^ (prefixWord ++ tailWord_1916119).sum := by decide
  have hdescent : baseEnd_1916119 < baseStart_1916119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916120 : List Nat := [2, 1, 2, 2, 6, 1, 1, 1, 3, 1, 3]
def baseStart_1916120 : Nat := 118140960795 + 1916120 * 2 ^ 59
def prefixEnd_1916120 : Nat := 4983230072969 + 3 ^ 40 * 1916120 * 2
def baseEnd_1916120 : Nat := 983890551693148405387931

theorem tailTrace_1916120 : CollatzResearch.WordTrace tailWord_1916120 prefixEnd_1916120 983890551693148405387931 := by
  unfold tailWord_1916120
  simp only [CollatzResearch.WordTrace]
  refine ⟨34943318909115981043812907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46591091878821308058417209 34943318909115981043812907)
  ·
    refine ⟨52414978363673971565719361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34943318909115981043812907 52414978363673971565719361)
    ·
      refine ⟨39311233772755478674289521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52414978363673971565719361 39311233772755478674289521)
      ·
        refine ⟨29483425329566609005717141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39311233772755478674289521 29483425329566609005717141)
        ·
          refine ⟨1382035562323434797142991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 29483425329566609005717141 1382035562323434797142991)
          ·
            refine ⟨2073053343485152195714487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382035562323434797142991 2073053343485152195714487)
            ·
              refine ⟨3109580015227728293571731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2073053343485152195714487 3109580015227728293571731)
              ·
                refine ⟨4664370022841592440357597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3109580015227728293571731 4664370022841592440357597)
                ·
                  refine ⟨1749138758565597165134099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4664370022841592440357597 1749138758565597165134099)
                  ·
                    refine ⟨2623708137848395747701149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1749138758565597165134099 2623708137848395747701149)
                    ·
                      refine ⟨983890551693148405387931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2623708137848395747701149 983890551693148405387931)
                      ·
                        rfl

theorem cell23_1916120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_1916120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916120 prefixEnd_1916120 := by exact prefixLift 1916120
  have htrace : WordTrace (prefixWord ++ tailWord_1916120) baseStart_1916120 baseEnd_1916120 := by
    simpa [prefixWord, tailWord_1916120, baseEnd_1916120] using wordTrace_append hprefix tailTrace_1916120
  have hstable : (prefixWord ++ tailWord_1916120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916120).length < 2 ^ (prefixWord ++ tailWord_1916120).sum := by decide
  have hdescent : baseEnd_1916120 < baseStart_1916120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916129 : List Nat := [1, 2, 3, 1, 3, 2, 2, 2, 1, 1, 5]
def baseStart_1916129 : Nat := 118140960795 + 1916129 * 2 ^ 59
def prefixEnd_1916129 : Nat := 4983230072969 + 3 ^ 40 * 1916129 * 2
def baseEnd_1916129 : Nat := 983895173019038870175389

theorem tailTrace_1916129 : CollatzResearch.WordTrace tailWord_1916129 prefixEnd_1916129 983895173019038870175389 := by
  unfold tailWord_1916129
  simp only [CollatzResearch.WordTrace]
  refine ⟨69886966075199356624703441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46591310716799571083135627 69886966075199356624703441)
  ·
    refine ⟨52415224556399517468527581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69886966075199356624703441 52415224556399517468527581)
    ·
      refine ⟨19655709208649819050697843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52415224556399517468527581 19655709208649819050697843)
      ·
        refine ⟨29483563812974728576046765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19655709208649819050697843 29483563812974728576046765)
        ·
          refine ⟨11056336429865523216017537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29483563812974728576046765 11056336429865523216017537)
          ·
            refine ⟨8292252322399142412013153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11056336429865523216017537 8292252322399142412013153)
            ·
              refine ⟨6219189241799356809009865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8292252322399142412013153 6219189241799356809009865)
              ·
                refine ⟨4664391931349517606757399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6219189241799356809009865 4664391931349517606757399)
                ·
                  refine ⟨6996587897024276410136099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4664391931349517606757399 6996587897024276410136099)
                  ·
                    refine ⟨10494881845536414615204149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6996587897024276410136099 10494881845536414615204149)
                    ·
                      refine ⟨983895173019038870175389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10494881845536414615204149 983895173019038870175389)
                      ·
                        rfl

theorem cell23_1916129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_1916129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916129 prefixEnd_1916129 := by exact prefixLift 1916129
  have htrace : WordTrace (prefixWord ++ tailWord_1916129) baseStart_1916129 baseEnd_1916129 := by
    simpa [prefixWord, tailWord_1916129, baseEnd_1916129] using wordTrace_append hprefix tailTrace_1916129
  have hstable : (prefixWord ++ tailWord_1916129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916129).length < 2 ^ (prefixWord ++ tailWord_1916129).sum := by decide
  have hdescent : baseEnd_1916129 < baseStart_1916129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916132 : List Nat := [2, 3, 1, 1, 1, 2, 3, 10]
def baseStart_1916132 : Nat := 118140960795 + 1916132 * 2 ^ 59
def prefixEnd_1916132 : Nat := 4983230072969 + 3 ^ 40 * 1916132 * 2
def baseEnd_1916132 : Nat := 36440619017074161423625

theorem tailTrace_1916132 : CollatzResearch.WordTrace tailWord_1916132 prefixEnd_1916132 36440619017074161423625 := by
  unfold tailWord_1916132
  simp only [CollatzResearch.WordTrace]
  refine ⟨34943537747094244068531325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46591383662792325424708433 34943537747094244068531325)
  ·
    refine ⟨13103826655160341525699247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34943537747094244068531325 13103826655160341525699247)
    ·
      refine ⟨19655739982740512288548871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13103826655160341525699247 19655739982740512288548871)
      ·
        refine ⟨29483609974110768432823307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19655739982740512288548871 29483609974110768432823307)
        ·
          refine ⟨44225414961166152649234961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29483609974110768432823307 44225414961166152649234961)
          ·
            refine ⟨33169061220874614486926221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44225414961166152649234961 33169061220874614486926221)
            ·
              refine ⟨12438397957827980432597333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33169061220874614486926221 12438397957827980432597333)
              ·
                refine ⟨36440619017074161423625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12438397957827980432597333 36440619017074161423625)
                ·
                  rfl

theorem cell23_1916132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 10].length) (baseStart_1916132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916132 prefixEnd_1916132 := by exact prefixLift 1916132
  have htrace : WordTrace (prefixWord ++ tailWord_1916132) baseStart_1916132 baseEnd_1916132 := by
    simpa [prefixWord, tailWord_1916132, baseEnd_1916132] using wordTrace_append hprefix tailTrace_1916132
  have hstable : (prefixWord ++ tailWord_1916132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916132).length < 2 ^ (prefixWord ++ tailWord_1916132).sum := by decide
  have hdescent : baseEnd_1916132 < baseStart_1916132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916136 : List Nat := [2, 1, 4, 1, 2, 1, 3, 3, 2, 4]
def baseStart_1916136 : Nat := 118140960795 + 1916136 * 2 ^ 59
def prefixEnd_1916136 : Nat := 4983230072969 + 3 ^ 40 * 1916136 * 2
def baseEnd_1916136 : Nat := 327966255794540114262619

theorem tailTrace_1916136 : CollatzResearch.WordTrace tailWord_1916136 prefixEnd_1916136 327966255794540114262619 := by
  unfold tailWord_1916136
  simp only [CollatzResearch.WordTrace]
  refine ⟨34943610693086998410104131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46591480924115997880138841 34943610693086998410104131)
  ·
    refine ⟨52415416039630497615156197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34943610693086998410104131 52415416039630497615156197)
    ·
      refine ⟨9827890507430718302841787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52415416039630497615156197 9827890507430718302841787)
      ·
        refine ⟨14741835761146077454262681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9827890507430718302841787 14741835761146077454262681)
        ·
          refine ⟨11056376820859558090697011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14741835761146077454262681 11056376820859558090697011)
          ·
            refine ⟨16584565231289337136045517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11056376820859558090697011 16584565231289337136045517)
            ·
              refine ⟨6219211961733501426017069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16584565231289337136045517 6219211961733501426017069)
              ·
                refine ⟨2332204485650063034756401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6219211961733501426017069 2332204485650063034756401)
                ·
                  refine ⟨1749153364237547276067301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2332204485650063034756401 1749153364237547276067301)
                  ·
                    refine ⟨327966255794540114262619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1749153364237547276067301 327966255794540114262619)
                    ·
                      rfl

theorem cell23_1916136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_1916136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916136 prefixEnd_1916136 := by exact prefixLift 1916136
  have htrace : WordTrace (prefixWord ++ tailWord_1916136) baseStart_1916136 baseEnd_1916136 := by
    simpa [prefixWord, tailWord_1916136, baseEnd_1916136] using wordTrace_append hprefix tailTrace_1916136
  have hstable : (prefixWord ++ tailWord_1916136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916136).length < 2 ^ (prefixWord ++ tailWord_1916136).sum := by decide
  have hdescent : baseEnd_1916136 < baseStart_1916136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916143 : List Nat := [1, 1, 2, 1, 7, 2, 1, 2, 1, 1, 4]
def baseStart_1916143 : Nat := 118140960795 + 1916143 * 2 ^ 59
def prefixEnd_1916143 : Nat := 4983230072969 + 3 ^ 40 * 1916143 * 2
def baseEnd_1916143 : Nat := 983902361748201815400325

theorem tailTrace_1916143 : CollatzResearch.WordTrace tailWord_1916143 prefixEnd_1916143 983902361748201815400325 := by
  unfold tailWord_1916143
  simp only [CollatzResearch.WordTrace]
  refine ⟨69887476697148637015713083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46591651131432424677142055 69887476697148637015713083)
  ·
    refine ⟨104831215045722955523569625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69887476697148637015713083 104831215045722955523569625)
    ·
      refine ⟨78623411284292216642677219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104831215045722955523569625 78623411284292216642677219)
      ·
        refine ⟨117935116926438324964015829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78623411284292216642677219 117935116926438324964015829)
        ·
          refine ⟨2764104302963398241344121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 117935116926438324964015829 2764104302963398241344121)
          ·
            refine ⟨2073078227222548681008091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2764104302963398241344121 2073078227222548681008091)
            ·
              refine ⟨3109617340833823021512137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2073078227222548681008091 3109617340833823021512137)
              ·
                refine ⟨2332213005625367266134103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3109617340833823021512137 2332213005625367266134103)
                ·
                  refine ⟨3498319508438050899201155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332213005625367266134103 3498319508438050899201155)
                  ·
                    refine ⟨5247479262657076348801733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3498319508438050899201155 5247479262657076348801733)
                    ·
                      refine ⟨983902361748201815400325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5247479262657076348801733 983902361748201815400325)
                      ·
                        rfl

theorem cell23_1916143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 2, 1, 1, 4].length) (baseStart_1916143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916143 prefixEnd_1916143 := by exact prefixLift 1916143
  have htrace : WordTrace (prefixWord ++ tailWord_1916143) baseStart_1916143 baseEnd_1916143 := by
    simpa [prefixWord, tailWord_1916143, baseEnd_1916143] using wordTrace_append hprefix tailTrace_1916143
  have hstable : (prefixWord ++ tailWord_1916143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916143).length < 2 ^ (prefixWord ++ tailWord_1916143).sum := by decide
  have hdescent : baseEnd_1916143 < baseStart_1916143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916156 : List Nat := [2, 2, 2, 1, 5, 1, 1, 2, 1, 2, 4]
def baseStart_1916156 : Nat := 118140960795 + 1916156 * 2 ^ 59
def prefixEnd_1916156 : Nat := 4983230072969 + 3 ^ 40 * 1916156 * 2
def baseEnd_1916156 : Nat := 983909036996710264537765

theorem tailTrace_1916156 : CollatzResearch.WordTrace tailWord_1916156 prefixEnd_1916156 983909036996710264537765 := by
  unfold tailWord_1916156
  simp only [CollatzResearch.WordTrace]
  refine ⟨34943975423050770117968161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46591967230734360157290881 34943975423050770117968161)
  ·
    refine ⟨26207981567288077588476121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34943975423050770117968161 26207981567288077588476121)
    ·
      refine ⟨19655986175466058191357091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26207981567288077588476121 19655986175466058191357091)
      ·
        refine ⟨29483979263199087287035637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19655986175466058191357091 29483979263199087287035637)
        ·
          refine ⟨2764123055924914433159591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 29483979263199087287035637 2764123055924914433159591)
          ·
            refine ⟨4146184583887371649739387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2764123055924914433159591 4146184583887371649739387)
            ·
              refine ⟨6219276875831057474609081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4146184583887371649739387 6219276875831057474609081)
              ·
                refine ⟨4664457656873293105956811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6219276875831057474609081 4664457656873293105956811)
                ·
                  refine ⟨6996686485309939658935217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4664457656873293105956811 6996686485309939658935217)
                  ·
                    refine ⟨5247514863982454744201413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6996686485309939658935217 5247514863982454744201413)
                    ·
                      refine ⟨983909036996710264537765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5247514863982454744201413 983909036996710264537765)
                      ·
                        rfl

theorem cell23_1916156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_1916156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916156 prefixEnd_1916156 := by exact prefixLift 1916156
  have htrace : WordTrace (prefixWord ++ tailWord_1916156) baseStart_1916156 baseEnd_1916156 := by
    simpa [prefixWord, tailWord_1916156, baseEnd_1916156] using wordTrace_append hprefix tailTrace_1916156
  have hstable : (prefixWord ++ tailWord_1916156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916156).length < 2 ^ (prefixWord ++ tailWord_1916156).sum := by decide
  have hdescent : baseEnd_1916156 < baseStart_1916156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916159 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 3]
def baseStart_1916159 : Nat := 118140960795 + 1916159 * 2 ^ 59
def prefixEnd_1916159 : Nat := 4983230072969 + 3 ^ 40 * 1916159 * 2
def baseEnd_1916159 : Nat := 983910577438673752800251

theorem tailTrace_1916159 : CollatzResearch.WordTrace tailWord_1916159 prefixEnd_1916159 983910577438673752800251 := by
  unfold tailWord_1916159
  simp only [CollatzResearch.WordTrace]
  refine ⟨69888060265090671748295531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46592040176727114498863687 69888060265090671748295531)
  ·
    refine ⟨104832090397636007622443297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69888060265090671748295531 104832090397636007622443297)
    ·
      refine ⟨78624067798227005716832473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104832090397636007622443297 78624067798227005716832473)
      ·
        refine ⟨58968050848670254287624355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78624067798227005716832473 58968050848670254287624355)
        ·
          refine ⟨88452076273005381431436533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58968050848670254287624355 88452076273005381431436533)
          ·
            refine ⟨8292382150594254509197175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88452076273005381431436533 8292382150594254509197175)
            ·
              refine ⟨12438573225891381763795763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8292382150594254509197175 12438573225891381763795763)
              ·
                refine ⟨18657859838837072645693645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12438573225891381763795763 18657859838837072645693645)
                ·
                  refine ⟨6996697439563902242135117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18657859838837072645693645 6996697439563902242135117)
                  ·
                    refine ⟨2623761539836463340800669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6996697439563902242135117 2623761539836463340800669)
                    ·
                      refine ⟨983910577438673752800251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2623761539836463340800669 983910577438673752800251)
                      ·
                        rfl

theorem cell23_1916159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 3].length) (baseStart_1916159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916159 prefixEnd_1916159 := by exact prefixLift 1916159
  have htrace : WordTrace (prefixWord ++ tailWord_1916159) baseStart_1916159 baseEnd_1916159 := by
    simpa [prefixWord, tailWord_1916159, baseEnd_1916159] using wordTrace_append hprefix tailTrace_1916159
  have hstable : (prefixWord ++ tailWord_1916159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916159).length < 2 ^ (prefixWord ++ tailWord_1916159).sum := by decide
  have hdescent : baseEnd_1916159 < baseStart_1916159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916163 : List Nat := [1, 1, 1, 3, 2, 5, 3, 1, 1, 2, 3]
def baseStart_1916163 : Nat := 118140960795 + 1916163 * 2 ^ 59
def prefixEnd_1916163 : Nat := 4983230072969 + 3 ^ 40 * 1916163 * 2
def baseEnd_1916163 : Nat := 983912631361291737150233

theorem tailTrace_1916163 : CollatzResearch.WordTrace tailWord_1916163 prefixEnd_1916163 983912631361291737150233 := by
  unfold tailWord_1916163
  simp only [CollatzResearch.WordTrace]
  refine ⟨69888206157076180431441143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46592137438050786954294095 69888206157076180431441143)
  ·
    refine ⟨104832309235614270647161715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69888206157076180431441143 104832309235614270647161715)
    ·
      refine ⟨157248463853421405970742573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104832309235614270647161715 157248463853421405970742573)
      ·
        refine ⟨58968173945033027239028465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157248463853421405970742573 58968173945033027239028465)
        ·
          refine ⟨44226130458774770429271349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58968173945033027239028465 44226130458774770429271349)
          ·
            refine ⟨4146199730510134727744189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44226130458774770429271349 4146199730510134727744189)
            ·
              refine ⟨1554824898941300522904071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4146199730510134727744189 1554824898941300522904071)
              ·
                refine ⟨2332237348411950784356107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1554824898941300522904071 2332237348411950784356107)
                ·
                  refine ⟨3498356022617926176534161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332237348411950784356107 3498356022617926176534161)
                  ·
                    refine ⟨2623767016963444632400621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3498356022617926176534161 2623767016963444632400621)
                    ·
                      refine ⟨983912631361291737150233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2623767016963444632400621 983912631361291737150233)
                      ·
                        rfl

theorem cell23_1916163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 1, 2, 3].length) (baseStart_1916163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916163 prefixEnd_1916163 := by exact prefixLift 1916163
  have htrace : WordTrace (prefixWord ++ tailWord_1916163) baseStart_1916163 baseEnd_1916163 := by
    simpa [prefixWord, tailWord_1916163, baseEnd_1916163] using wordTrace_append hprefix tailTrace_1916163
  have hstable : (prefixWord ++ tailWord_1916163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916163).length < 2 ^ (prefixWord ++ tailWord_1916163).sum := by decide
  have hdescent : baseEnd_1916163 < baseStart_1916163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916190 : List Nat := [4, 3, 2, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_1916190 : Nat := 118140960795 + 1916190 * 2 ^ 59
def prefixEnd_1916190 : Nat := 4983230072969 + 3 ^ 40 * 1916190 * 2
def baseEnd_1916190 : Nat := 983926495338963131512609

theorem tailTrace_1916190 : CollatzResearch.WordTrace tailWord_1916190 prefixEnd_1916190 983926495338963131512609 := by
  unfold tailWord_1916190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8736148865997295505334253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46592793951985576028449349 8736148865997295505334253)
  ·
    refine ⟨3276055824748985814500345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8736148865997295505334253 3276055824748985814500345)
    ·
      refine ⟨2457041868561739360875259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3276055824748985814500345 2457041868561739360875259)
      ·
        refine ⟨3685562802842609041312889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2457041868561739360875259 3685562802842609041312889)
        ·
          refine ⟨2764172102131956780984667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3685562802842609041312889 2764172102131956780984667)
          ·
            refine ⟨4146258153197935171477001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2764172102131956780984667 4146258153197935171477001)
            ·
              refine ⟨3109693614898451378607751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4146258153197935171477001 3109693614898451378607751)
              ·
                refine ⟨4664540422347677067911627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3109693614898451378607751 4664540422347677067911627)
                ·
                  refine ⟨6996810633521515601867441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4664540422347677067911627 6996810633521515601867441)
                  ·
                    refine ⟨5247607975141136701400581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6996810633521515601867441 5247607975141136701400581)
                    ·
                      refine ⟨983926495338963131512609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5247607975141136701400581 983926495338963131512609)
                      ·
                        rfl

theorem cell23_1916190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_1916190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916190 prefixEnd_1916190 := by exact prefixLift 1916190
  have htrace : WordTrace (prefixWord ++ tailWord_1916190) baseStart_1916190 baseEnd_1916190 := by
    simpa [prefixWord, tailWord_1916190, baseEnd_1916190] using wordTrace_append hprefix tailTrace_1916190
  have hstable : (prefixWord ++ tailWord_1916190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916190).length < 2 ^ (prefixWord ++ tailWord_1916190).sum := by decide
  have hdescent : baseEnd_1916190 < baseStart_1916190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916214 : List Nat := [5, 1, 2, 3, 1, 2, 2, 1, 1, 2, 3]
def baseStart_1916214 : Nat := 118140960795 + 1916214 * 2 ^ 59
def prefixEnd_1916214 : Nat := 4983230072969 + 3 ^ 40 * 1916214 * 2
def baseEnd_1916214 : Nat := 983938818874671037612499

theorem tailTrace_1916214 : CollatzResearch.WordTrace tailWord_1916214 prefixEnd_1916214 983938818874671037612499 := by
  unfold tailWord_1916214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4368129142493213508846731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46593377519927610761031797 4368129142493213508846731)
  ·
    refine ⟨6552193713739820263270097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4368129142493213508846731 6552193713739820263270097)
    ·
      refine ⟨4914145285304865197452573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6552193713739820263270097 4914145285304865197452573)
      ·
        refine ⟨1842804481989324449044715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4914145285304865197452573 1842804481989324449044715)
        ·
          refine ⟨2764206722983986673567073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1842804481989324449044715 2764206722983986673567073)
          ·
            refine ⟨2073155042237990005175305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2764206722983986673567073 2073155042237990005175305)
            ·
              refine ⟨1554866281678492503881479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2073155042237990005175305 1554866281678492503881479)
              ·
                refine ⟨2332299422517738755822219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1554866281678492503881479 2332299422517738755822219)
                ·
                  refine ⟨3498449133776608133733329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332299422517738755822219 3498449133776608133733329)
                  ·
                    refine ⟨2623836850332456100299997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3498449133776608133733329 2623836850332456100299997)
                    ·
                      refine ⟨983938818874671037612499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2623836850332456100299997 983938818874671037612499)
                      ·
                        rfl

theorem cell23_1916214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_1916214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916214 prefixEnd_1916214 := by exact prefixLift 1916214
  have htrace : WordTrace (prefixWord ++ tailWord_1916214) baseStart_1916214 baseEnd_1916214 := by
    simpa [prefixWord, tailWord_1916214, baseEnd_1916214] using wordTrace_append hprefix tailTrace_1916214
  have hstable : (prefixWord ++ tailWord_1916214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916214).length < 2 ^ (prefixWord ++ tailWord_1916214).sum := by decide
  have hdescent : baseEnd_1916214 < baseStart_1916214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916220 : List Nat := [2, 2, 2, 2, 1, 3, 4, 1, 1, 3, 2]
def baseStart_1916220 : Nat := 118140960795 + 1916220 * 2 ^ 59
def prefixEnd_1916220 : Nat := 4983230072969 + 3 ^ 40 * 1916220 * 2
def baseEnd_1916220 : Nat := 983941899758598014137471

theorem tailTrace_1916220 : CollatzResearch.WordTrace tailWord_1916220 prefixEnd_1916220 983941899758598014137471 := by
  unfold tailWord_1916220
  simp only [CollatzResearch.WordTrace]
  refine ⟨34945142558934839583133057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46593523411913119444177409 34945142558934839583133057)
  ·
    refine ⟨26208856919201129687349793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34945142558934839583133057 26208856919201129687349793)
    ·
      refine ⟨19656642689400847265512345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26208856919201129687349793 19656642689400847265512345)
      ·
        refine ⟨14742482017050635449134259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19656642689400847265512345 14742482017050635449134259)
        ·
          refine ⟨22113723025575953173701389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14742482017050635449134259 22113723025575953173701389)
          ·
            refine ⟨8292646134590982440138021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22113723025575953173701389 8292646134590982440138021)
            ·
              refine ⟨1554871150235809207525879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8292646134590982440138021 1554871150235809207525879)
              ·
                refine ⟨2332306725353713811288819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1554871150235809207525879 2332306725353713811288819)
                ·
                  refine ⟨3498460088030570716933229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332306725353713811288819 3498460088030570716933229)
                  ·
                    refine ⟨1311922533011464018849961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3498460088030570716933229 1311922533011464018849961)
                    ·
                      refine ⟨983941899758598014137471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1311922533011464018849961 983941899758598014137471)
                      ·
                        rfl

theorem cell23_1916220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_1916220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916220 prefixEnd_1916220 := by exact prefixLift 1916220
  have htrace : WordTrace (prefixWord ++ tailWord_1916220) baseStart_1916220 baseEnd_1916220 := by
    simpa [prefixWord, tailWord_1916220, baseEnd_1916220] using wordTrace_append hprefix tailTrace_1916220
  have hstable : (prefixWord ++ tailWord_1916220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916220).length < 2 ^ (prefixWord ++ tailWord_1916220).sum := by decide
  have hdescent : baseEnd_1916220 < baseStart_1916220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916279 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 5]
def baseStart_1916279 : Nat := 118140960795 + 1916279 * 2 ^ 59
def prefixEnd_1916279 : Nat := 4983230072969 + 3 ^ 40 * 1916279 * 2
def baseEnd_1916279 : Nat := 983972195117213283299699

theorem tailTrace_1916279 : CollatzResearch.WordTrace tailWord_1916279 prefixEnd_1916279 983972195117213283299699 := by
  unfold tailWord_1916279
  simp only [CollatzResearch.WordTrace]
  refine ⟨69892437024655932242663891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46594958016437288161775927 69892437024655932242663891)
  ·
    refine ⟨104838655536983898363995837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69892437024655932242663891 104838655536983898363995837)
    ·
      refine ⟨39314495826368961886498439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104838655536983898363995837 39314495826368961886498439)
      ·
        refine ⟨58971743739553442829747659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39314495826368961886498439 58971743739553442829747659)
        ·
          refine ⟨88457615609330164244621489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58971743739553442829747659 88457615609330164244621489)
          ·
            refine ⟨66343211706997623183466117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88457615609330164244621489 66343211706997623183466117)
            ·
              refine ⟨12439352195062054346899897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66343211706997623183466117 12439352195062054346899897)
              ·
                refine ⟨9329514146296540760174923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12439352195062054346899897 9329514146296540760174923)
                ·
                  refine ⟨13994271219444811140262385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9329514146296540760174923 13994271219444811140262385)
                  ·
                    refine ⟨10495703414583608355196789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13994271219444811140262385 10495703414583608355196789)
                    ·
                      refine ⟨983972195117213283299699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10495703414583608355196789 983972195117213283299699)
                      ·
                        rfl

theorem cell23_1916279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_1916279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916279 prefixEnd_1916279 := by exact prefixLift 1916279
  have htrace : WordTrace (prefixWord ++ tailWord_1916279) baseStart_1916279 baseEnd_1916279 := by
    simpa [prefixWord, tailWord_1916279, baseEnd_1916279] using wordTrace_append hprefix tailTrace_1916279
  have hstable : (prefixWord ++ tailWord_1916279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916279).length < 2 ^ (prefixWord ++ tailWord_1916279).sum := by decide
  have hdescent : baseEnd_1916279 < baseStart_1916279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916290 : List Nat := [3, 4, 2, 1, 1, 3, 1, 1, 7]
def baseStart_1916290 : Nat := 118140960795 + 1916290 * 2 ^ 59
def prefixEnd_1916290 : Nat := 4983230072969 + 3 ^ 40 * 1916290 * 2
def baseEnd_1916290 : Nat := 109330871489379193362461

theorem tailTrace_1916290 : CollatzResearch.WordTrace tailWord_1916290 prefixEnd_1916290 109330871489379193362461 := by
  unfold tailWord_1916290
  simp only [CollatzResearch.WordTrace]
  refine ⟨17473209556904020280328581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46595225485077387414209549 17473209556904020280328581)
  ·
    refine ⟨3276226791919503802561609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17473209556904020280328581 3276226791919503802561609)
    ·
      refine ⟨2457170093939627851921207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3276226791919503802561609 2457170093939627851921207)
      ·
        refine ⟨3685755140909441777881811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2457170093939627851921207 3685755140909441777881811)
        ·
          refine ⟨5528632711364162666822717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3685755140909441777881811 5528632711364162666822717)
          ·
            refine ⟨2073237266761561000058519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5528632711364162666822717 2073237266761561000058519)
            ·
              refine ⟨3109855900142341500087779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2073237266761561000058519 3109855900142341500087779)
              ·
                refine ⟨4664783850213512250131669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3109855900142341500087779 4664783850213512250131669)
                ·
                  refine ⟨109330871489379193362461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4664783850213512250131669 109330871489379193362461)
                  ·
                    rfl

theorem cell23_1916290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_1916290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916290 prefixEnd_1916290 := by exact prefixLift 1916290
  have htrace : WordTrace (prefixWord ++ tailWord_1916290) baseStart_1916290 baseEnd_1916290 := by
    simpa [prefixWord, tailWord_1916290, baseEnd_1916290] using wordTrace_append hprefix tailTrace_1916290
  have hstable : (prefixWord ++ tailWord_1916290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916290).length < 2 ^ (prefixWord ++ tailWord_1916290).sum := by decide
  have hdescent : baseEnd_1916290 < baseStart_1916290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916296 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 1, 2, 5]
def baseStart_1916296 : Nat := 118140960795 + 1916296 * 2 ^ 59
def prefixEnd_1916296 : Nat := 4983230072969 + 3 ^ 40 * 1916296 * 2
def baseEnd_1916296 : Nat := 983980924288339716787121

theorem tailTrace_1916296 : CollatzResearch.WordTrace tailWord_1916296 prefixEnd_1916296 983980924288339716787121 := by
  unfold tailWord_1916296
  simp only [CollatzResearch.WordTrace]
  refine ⟨34946528532797172073016371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46595371377062896097355161 34946528532797172073016371)
  ·
    refine ⟨52419792799195758109524557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34946528532797172073016371 52419792799195758109524557)
    ·
      refine ⟨19657422299698409291071709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52419792799195758109524557 19657422299698409291071709)
      ·
        refine ⟨7371533362386903484151891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19657422299698409291071709 7371533362386903484151891)
        ·
          refine ⟨11057300043580355226227837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7371533362386903484151891 11057300043580355226227837)
          ·
            refine ⟨4146487516342633209835439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11057300043580355226227837 4146487516342633209835439)
            ·
              refine ⟨6219731274513949814753159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4146487516342633209835439 6219731274513949814753159)
              ·
                refine ⟨9329596911770924722129739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6219731274513949814753159 9329596911770924722129739)
                ·
                  refine ⟨13994395367656387083194609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9329596911770924722129739 13994395367656387083194609)
                  ·
                    refine ⟨10495796525742290312395957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13994395367656387083194609 10495796525742290312395957)
                    ·
                      refine ⟨983980924288339716787121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10495796525742290312395957 983980924288339716787121)
                      ·
                        rfl

theorem cell23_1916296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_1916296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916296 prefixEnd_1916296 := by exact prefixLift 1916296
  have htrace : WordTrace (prefixWord ++ tailWord_1916296) baseStart_1916296 baseEnd_1916296 := by
    simpa [prefixWord, tailWord_1916296, baseEnd_1916296] using wordTrace_append hprefix tailTrace_1916296
  have hstable : (prefixWord ++ tailWord_1916296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916296).length < 2 ^ (prefixWord ++ tailWord_1916296).sum := by decide
  have hdescent : baseEnd_1916296 < baseStart_1916296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916376 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 3, 5]
def baseStart_1916376 : Nat := 118140960795 + 1916376 * 2 ^ 59
def prefixEnd_1916376 : Nat := 4983230072969 + 3 ^ 40 * 1916376 * 2
def baseEnd_1916376 : Nat := 328007334246899801262251

theorem tailTrace_1916376 : CollatzResearch.WordTrace tailWord_1916376 prefixEnd_1916376 328007334246899801262251 := by
  unfold tailWord_1916376
  simp only [CollatzResearch.WordTrace]
  refine ⟨34947987452652258904472491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46597316603536345205963321 34947987452652258904472491)
  ·
    refine ⟨52421981178978388356708737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34947987452652258904472491 52421981178978388356708737)
    ·
      refine ⟨39316485884233791267531553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52421981178978388356708737 39316485884233791267531553)
      ·
        refine ⟨29487364413175343450648665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39316485884233791267531553 29487364413175343450648665)
        ·
          refine ⟨22115523309881507587986499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29487364413175343450648665 22115523309881507587986499)
          ·
            refine ⟨33173284964822261381979749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22115523309881507587986499 33173284964822261381979749)
            ·
              refine ⟨6219990930904174009121203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33173284964822261381979749 6219990930904174009121203)
              ·
                refine ⟨9329986396356261013681805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6219990930904174009121203 9329986396356261013681805)
                ·
                  refine ⟨3498744898633597880130677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9329986396356261013681805 3498744898633597880130677)
                  ·
                    refine ⟨328007334246899801262251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3498744898633597880130677 328007334246899801262251)
                    ·
                      rfl

theorem cell23_1916376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_1916376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916376 prefixEnd_1916376 := by exact prefixLift 1916376
  have htrace : WordTrace (prefixWord ++ tailWord_1916376) baseStart_1916376 baseEnd_1916376 := by
    simpa [prefixWord, tailWord_1916376, baseEnd_1916376] using wordTrace_append hprefix tailTrace_1916376
  have hstable : (prefixWord ++ tailWord_1916376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916376).length < 2 ^ (prefixWord ++ tailWord_1916376).sum := by decide
  have hdescent : baseEnd_1916376 < baseStart_1916376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916383 : List Nat := [1, 1, 2, 3, 3, 1, 3, 1, 1, 5, 2]
def baseStart_1916383 : Nat := 118140960795 + 1916383 * 2 ^ 59
def prefixEnd_1916383 : Nat := 4983230072969 + 3 ^ 40 * 1916383 * 2
def baseEnd_1916383 : Nat := 984025597105280876399221

theorem tailTrace_1916383 : CollatzResearch.WordTrace tailWord_1916383 prefixEnd_1916383 984025597105280876399221 := by
  unfold tailWord_1916383
  simp only [CollatzResearch.WordTrace]
  refine ⟨69896230216279158004449803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46597486810852772002966535 69896230216279158004449803)
  ·
    refine ⟨104844345324418737006674705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69896230216279158004449803 104844345324418737006674705)
    ·
      refine ⟨78633258993314052755006029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104844345324418737006674705 78633258993314052755006029)
      ·
        refine ⟨29487472122492769783127261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78633258993314052755006029 29487472122492769783127261)
        ·
          refine ⟨11057802045934788668672723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29487472122492769783127261 11057802045934788668672723)
          ·
            refine ⟨16586703068902183003009085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11057802045934788668672723 16586703068902183003009085)
            ·
              refine ⟨6220013650838318626128407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16586703068902183003009085 6220013650838318626128407)
              ·
                refine ⟨9330020476257477939192611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6220013650838318626128407 9330020476257477939192611)
                ·
                  refine ⟨13995030714386216908788917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9330020476257477939192611 13995030714386216908788917)
                  ·
                    refine ⟨1312034129473707835198961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13995030714386216908788917 1312034129473707835198961)
                    ·
                      refine ⟨984025597105280876399221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1312034129473707835198961 984025597105280876399221)
                      ·
                        rfl

theorem cell23_1916383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 5, 2].length) (baseStart_1916383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916383 prefixEnd_1916383 := by exact prefixLift 1916383
  have htrace : WordTrace (prefixWord ++ tailWord_1916383) baseStart_1916383 baseEnd_1916383 := by
    simpa [prefixWord, tailWord_1916383, baseEnd_1916383] using wordTrace_append hprefix tailTrace_1916383
  have hstable : (prefixWord ++ tailWord_1916383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916383).length < 2 ^ (prefixWord ++ tailWord_1916383).sum := by decide
  have hdescent : baseEnd_1916383 < baseStart_1916383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916396 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 4]
def baseStart_1916396 : Nat := 118140960795 + 1916396 * 2 ^ 59
def prefixEnd_1916396 : Nat := 4983230072969 + 3 ^ 40 * 1916396 * 2
def baseEnd_1916396 : Nat := 984032272353789325536661

theorem tailTrace_1916396 : CollatzResearch.WordTrace tailWord_1916396 prefixEnd_1916396 984032272353789325536661 := by
  unfold tailWord_1916396
  simp only [CollatzResearch.WordTrace]
  refine ⟨34948352182616030612336521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46597802910154707483115361 34948352182616030612336521)
  ·
    refine ⟨26211264136962022959252391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34948352182616030612336521 26211264136962022959252391)
    ·
      refine ⟨39316896205443034438878587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26211264136962022959252391 39316896205443034438878587)
      ·
        refine ⟨58975344308164551658317881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39316896205443034438878587 58975344308164551658317881)
        ·
          refine ⟨44231508231123413743738411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58975344308164551658317881 44231508231123413743738411)
          ·
            refine ⟨66347262346685120615607617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44231508231123413743738411 66347262346685120615607617)
            ·
              refine ⟨49760446760013840461705713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66347262346685120615607617 49760446760013840461705713)
              ·
                refine ⟨37320335070010380346279285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49760446760013840461705713 37320335070010380346279285)
                ·
                  refine ⟨3498781412813473157463683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37320335070010380346279285 3498781412813473157463683)
                  ·
                    refine ⟨5248172119220209736195525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3498781412813473157463683 5248172119220209736195525)
                    ·
                      refine ⟨984032272353789325536661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5248172119220209736195525 984032272353789325536661)
                      ·
                        rfl

theorem cell23_1916396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_1916396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916396 prefixEnd_1916396 := by exact prefixLift 1916396
  have htrace : WordTrace (prefixWord ++ tailWord_1916396) baseStart_1916396 baseEnd_1916396 := by
    simpa [prefixWord, tailWord_1916396, baseEnd_1916396] using wordTrace_append hprefix tailTrace_1916396
  have hstable : (prefixWord ++ tailWord_1916396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916396).length < 2 ^ (prefixWord ++ tailWord_1916396).sum := by decide
  have hdescent : baseEnd_1916396 < baseStart_1916396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916397 : List Nat := [1, 5, 1, 3, 3, 1, 1, 2, 6]
def baseStart_1916397 : Nat := 118140960795 + 1916397 * 2 ^ 59
def prefixEnd_1916397 : Nat := 4983230072969 + 3 ^ 40 * 1916397 * 2
def baseEnd_1916397 : Nat := 109336976203827091291573

theorem tailTrace_1916397 : CollatzResearch.WordTrace tailWord_1916397 prefixEnd_1916397 109336976203827091291573 := by
  unfold tailWord_1916397
  simp only [CollatzResearch.WordTrace]
  refine ⟨69896740838228438395459445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46597827225485625596972963 69896740838228438395459445)
  ·
    refine ⟨6552819453583916099574323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69896740838228438395459445 6552819453583916099574323)
    ·
      refine ⟨9829229180375874149361485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6552819453583916099574323 9829229180375874149361485)
      ·
        refine ⟨3685960942640952806010557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9829229180375874149361485 3685960942640952806010557)
        ·
          refine ⟨1382235353490357302253959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3685960942640952806010557 1382235353490357302253959)
          ·
            refine ⟨2073353030235535953380939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382235353490357302253959 2073353030235535953380939)
            ·
              refine ⟨3110029545353303930071409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2073353030235535953380939 3110029545353303930071409)
              ·
                refine ⟨2332522159014977947553557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3110029545353303930071409 2332522159014977947553557)
                ·
                  refine ⟨109336976203827091291573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2332522159014977947553557 109336976203827091291573)
                  ·
                    rfl

theorem cell23_1916397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_1916397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916397 prefixEnd_1916397 := by exact prefixLift 1916397
  have htrace : WordTrace (prefixWord ++ tailWord_1916397) baseStart_1916397 baseEnd_1916397 := by
    simpa [prefixWord, tailWord_1916397, baseEnd_1916397] using wordTrace_append hprefix tailTrace_1916397
  have hstable : (prefixWord ++ tailWord_1916397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916397).length < 2 ^ (prefixWord ++ tailWord_1916397).sum := by decide
  have hdescent : baseEnd_1916397 < baseStart_1916397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916423 : List Nat := [1, 1, 4, 3, 2, 1, 3, 1, 1, 6]
def baseStart_1916423 : Nat := 118140960795 + 1916423 * 2 ^ 59
def prefixEnd_1916423 : Nat := 4983230072969 + 3 ^ 40 * 1916423 * 2
def baseEnd_1916423 : Nat := 328015378777153573299679

theorem tailTrace_1916423 : CollatzResearch.WordTrace tailWord_1916423 prefixEnd_1916423 328015378777153573299679 := by
  unfold tailWord_1916423
  simp only [CollatzResearch.WordTrace]
  refine ⟨69897689136134244835905923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46598459424089496557270615 69897689136134244835905923)
  ·
    refine ⟨104846533704201367253858885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69897689136134244835905923 104846533704201367253858885)
    ·
      refine ⟨19658725069537756360098541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104846533704201367253858885 19658725069537756360098541)
      ·
        refine ⟨7372021901076658635036953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19658725069537756360098541 7372021901076658635036953)
        ·
          refine ⟨5529016425807493976277715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7372021901076658635036953 5529016425807493976277715)
          ·
            refine ⟨8293524638711240964416573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5529016425807493976277715 8293524638711240964416573)
            ·
              refine ⟨3110071739516715361656215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8293524638711240964416573 3110071739516715361656215)
              ·
                refine ⟨4665107609275073042484323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3110071739516715361656215 4665107609275073042484323)
                ·
                  refine ⟨6997661413912609563726485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4665107609275073042484323 6997661413912609563726485)
                  ·
                    refine ⟨328015378777153573299679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6997661413912609563726485 328015378777153573299679)
                    ·
                      rfl

theorem cell23_1916423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_1916423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916423 prefixEnd_1916423 := by exact prefixLift 1916423
  have htrace : WordTrace (prefixWord ++ tailWord_1916423) baseStart_1916423 baseEnd_1916423 := by
    simpa [prefixWord, tailWord_1916423, baseEnd_1916423] using wordTrace_append hprefix tailTrace_1916423
  have hstable : (prefixWord ++ tailWord_1916423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916423).length < 2 ^ (prefixWord ++ tailWord_1916423).sum := by decide
  have hdescent : baseEnd_1916423 < baseStart_1916423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916450 : List Nat := [3, 3, 1, 1, 1, 1, 4, 3, 1, 2, 3]
def baseStart_1916450 : Nat := 118140960795 + 1916450 * 2 ^ 59
def prefixEnd_1916450 : Nat := 4983230072969 + 3 ^ 40 * 1916450 * 2
def baseEnd_1916450 : Nat := 984060000309132114261413

theorem tailTrace_1916450 : CollatzResearch.WordTrace tailWord_1916450 prefixEnd_1916450 984060000309132114261413 := by
  unfold tailWord_1916450
  simp only [CollatzResearch.WordTrace]
  refine ⟨17474668476759107111784701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46599115938024285631425869 17474668476759107111784701)
  ·
    refine ⟨6553000678784665166919263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17474668476759107111784701 6553000678784665166919263)
    ·
      refine ⟨9829501018176997750378895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6553000678784665166919263 9829501018176997750378895)
      ·
        refine ⟨14744251527265496625568343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9829501018176997750378895 14744251527265496625568343)
        ·
          refine ⟨22116377290898244938352515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14744251527265496625568343 22116377290898244938352515)
          ·
            refine ⟨33174565936347367407528773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22116377290898244938352515 33174565936347367407528773)
            ·
              refine ⟨6220231113065131388911645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33174565936347367407528773 6220231113065131388911645)
              ·
                refine ⟨2332586667399424270841867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6220231113065131388911645 2332586667399424270841867)
                ·
                  refine ⟨3498880001099136406262801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332586667399424270841867 3498880001099136406262801)
                  ·
                    refine ⟨2624160000824352304697101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3498880001099136406262801 2624160000824352304697101)
                    ·
                      refine ⟨984060000309132114261413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2624160000824352304697101 984060000309132114261413)
                      ·
                        rfl

theorem cell23_1916450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_1916450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916450 prefixEnd_1916450 := by exact prefixLift 1916450
  have htrace : WordTrace (prefixWord ++ tailWord_1916450) baseStart_1916450 baseEnd_1916450 := by
    simpa [prefixWord, tailWord_1916450, baseEnd_1916450] using wordTrace_append hprefix tailTrace_1916450
  have hstable : (prefixWord ++ tailWord_1916450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916450).length < 2 ^ (prefixWord ++ tailWord_1916450).sum := by decide
  have hdescent : baseEnd_1916450 < baseStart_1916450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916466 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 2, 7]
def baseStart_1916466 : Nat := 118140960795 + 1916466 * 2 ^ 59
def prefixEnd_1916466 : Nat := 4983230072969 + 3 ^ 40 * 1916466 * 2
def baseEnd_1916466 : Nat := 328022738666534683887113

theorem tailTrace_1916466 : CollatzResearch.WordTrace tailWord_1916466 prefixEnd_1916466 328022738666534683887113 := by
  unfold tailWord_1916466
  simp only [CollatzResearch.WordTrace]
  refine ⟨17474814368744615794930313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46599504983318975453147501 17474814368744615794930313)
  ·
    refine ⟨13106110776558461846197735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17474814368744615794930313 13106110776558461846197735)
    ·
      refine ⟨19659166164837692769296603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13106110776558461846197735 19659166164837692769296603)
      ·
        refine ⟨29488749247256539153944905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19659166164837692769296603 29488749247256539153944905)
        ·
          refine ⟨22116561935442404365458679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29488749247256539153944905 22116561935442404365458679)
          ·
            refine ⟨33174842903163606548188019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22116561935442404365458679 33174842903163606548188019)
            ·
              refine ⟨49762264354745409822282029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33174842903163606548188019 49762264354745409822282029)
              ·
                refine ⟨18660849133029528683355761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49762264354745409822282029 18660849133029528683355761)
                ·
                  refine ⟨13995636849772146512516821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18660849133029528683355761 13995636849772146512516821)
                  ·
                    refine ⟨328022738666534683887113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13995636849772146512516821 328022738666534683887113)
                    ·
                      rfl

theorem cell23_1916466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_1916466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916466 prefixEnd_1916466 := by exact prefixLift 1916466
  have htrace : WordTrace (prefixWord ++ tailWord_1916466) baseStart_1916466 baseEnd_1916466 := by
    simpa [prefixWord, tailWord_1916466, baseEnd_1916466] using wordTrace_append hprefix tailTrace_1916466
  have hstable : (prefixWord ++ tailWord_1916466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916466).length < 2 ^ (prefixWord ++ tailWord_1916466).sum := by decide
  have hdescent : baseEnd_1916466 < baseStart_1916466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916470 : List Nat := [5, 1, 2, 1, 3, 1, 2, 8]
def baseStart_1916470 : Nat := 118140960795 + 1916470 * 2 ^ 59
def prefixEnd_1916470 : Nat := 4983230072969 + 3 ^ 40 * 1916470 * 2
def baseEnd_1916470 : Nat := 36447047034156371704123

theorem tailTrace_1916470 : CollatzResearch.WordTrace tailWord_1916470 prefixEnd_1916470 36447047034156371704123 := by
  unfold tailWord_1916470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4368712710435248241429179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46599602244642647908577909 4368712710435248241429179)
  ·
    refine ⟨6553069065652872362143769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4368712710435248241429179 6553069065652872362143769)
    ·
      refine ⟨4914801799239654271607827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6553069065652872362143769 4914801799239654271607827)
      ·
        refine ⟨7372202698859481407411741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4914801799239654271607827 7372202698859481407411741)
        ·
          refine ⟨2764576012072305527779403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7372202698859481407411741 2764576012072305527779403)
          ·
            refine ⟨4146864018108458291669105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2764576012072305527779403 4146864018108458291669105)
            ·
              refine ⟨3110148013581343718751829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4146864018108458291669105 3110148013581343718751829)
              ·
                refine ⟨36447047034156371704123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3110148013581343718751829 36447047034156371704123)
                ·
                  rfl

theorem cell23_1916470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_1916470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916470 prefixEnd_1916470 := by exact prefixLift 1916470
  have htrace : WordTrace (prefixWord ++ tailWord_1916470) baseStart_1916470 baseEnd_1916470 := by
    simpa [prefixWord, tailWord_1916470, baseEnd_1916470] using wordTrace_append hprefix tailTrace_1916470
  have hstable : (prefixWord ++ tailWord_1916470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916470).length < 2 ^ (prefixWord ++ tailWord_1916470).sum := by decide
  have hdescent : baseEnd_1916470 < baseStart_1916470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916490 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 3, 3, 2]
def baseStart_1916490 : Nat := 118140960795 + 1916490 * 2 ^ 59
def prefixEnd_1916490 : Nat := 4983230072969 + 3 ^ 40 * 1916490 * 2
def baseEnd_1916490 : Nat := 984080539535311957761229

theorem tailTrace_1916490 : CollatzResearch.WordTrace tailWord_1916490 prefixEnd_1916490 984080539535311957761229 := by
  unfold tailWord_1916490
  simp only [CollatzResearch.WordTrace]
  refine ⟨17475033206722878819648731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46600088551261010185729949 17475033206722878819648731)
  ·
    refine ⟨26212549810084318229473097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17475033206722878819648731 26212549810084318229473097)
    ·
      refine ⟨19659412357563238672104823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26212549810084318229473097 19659412357563238672104823)
      ·
        refine ⟨29489118536344858008157235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19659412357563238672104823 29489118536344858008157235)
        ·
          refine ⟨44233677804517287012235853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29489118536344858008157235 44233677804517287012235853)
          ·
            refine ⟨16587629176693982629588445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44233677804517287012235853 16587629176693982629588445)
            ·
              refine ⟨6220360941260243486095667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16587629176693982629588445 6220360941260243486095667)
              ·
                refine ⟨9330541411890365229143501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6220360941260243486095667 9330541411890365229143501)
                ·
                  refine ⟨3498953029458886960928813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9330541411890365229143501 3498953029458886960928813)
                  ·
                    refine ⟨1312107386047082610348305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3498953029458886960928813 1312107386047082610348305)
                    ·
                      refine ⟨984080539535311957761229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1312107386047082610348305 984080539535311957761229)
                      ·
                        rfl

theorem cell23_1916490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 3, 3, 2].length) (baseStart_1916490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916490 prefixEnd_1916490 := by exact prefixLift 1916490
  have htrace : WordTrace (prefixWord ++ tailWord_1916490) baseStart_1916490 baseEnd_1916490 := by
    simpa [prefixWord, tailWord_1916490, baseEnd_1916490] using wordTrace_append hprefix tailTrace_1916490
  have hstable : (prefixWord ++ tailWord_1916490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916490).length < 2 ^ (prefixWord ++ tailWord_1916490).sum := by decide
  have hdescent : baseEnd_1916490 < baseStart_1916490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916537 : List Nat := [1, 2, 1, 3, 3, 1, 1, 5, 2, 2, 2]
def baseStart_1916537 : Nat := 118140960795 + 1916537 * 2 ^ 59
def prefixEnd_1916537 : Nat := 4983230072969 + 3 ^ 40 * 1916537 * 2
def baseEnd_1916537 : Nat := 984104673126073273873513

theorem tailTrace_1916537 : CollatzResearch.WordTrace tailWord_1916537 prefixEnd_1916537 984104673126073273873513 := by
  unfold tailWord_1916537
  simp only [CollatzResearch.WordTrace]
  refine ⟨69901847057721242305555865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46601231371814161537037243 69901847057721242305555865)
  ·
    refine ⟨52426385293290931729166899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69901847057721242305555865 52426385293290931729166899)
    ·
      refine ⟨78639577939936397593750349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52426385293290931729166899 78639577939936397593750349)
      ·
        refine ⟨29489841727476149097656381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78639577939936397593750349 29489841727476149097656381)
        ·
          refine ⟨11058690647803555911621143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29489841727476149097656381 11058690647803555911621143)
          ·
            refine ⟨16588035971705333867431715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11058690647803555911621143 16588035971705333867431715)
            ·
              refine ⟨24882053957558000801147573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16588035971705333867431715 24882053957558000801147573)
              ·
                refine ⟨2332692558521062575107585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24882053957558000801147573 2332692558521062575107585)
                ·
                  refine ⟨1749519418890796931330689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2332692558521062575107585 1749519418890796931330689)
                  ·
                    refine ⟨1312139564168097698498017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1749519418890796931330689 1312139564168097698498017)
                    ·
                      refine ⟨984104673126073273873513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1312139564168097698498017 984104673126073273873513)
                      ·
                        rfl

theorem cell23_1916537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_1916537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916537 prefixEnd_1916537 := by exact prefixLift 1916537
  have htrace : WordTrace (prefixWord ++ tailWord_1916537) baseStart_1916537 baseEnd_1916537 := by
    simpa [prefixWord, tailWord_1916537, baseEnd_1916537] using wordTrace_append hprefix tailTrace_1916537
  have hstable : (prefixWord ++ tailWord_1916537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916537).length < 2 ^ (prefixWord ++ tailWord_1916537).sum := by decide
  have hdescent : baseEnd_1916537 < baseStart_1916537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916573 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 4, 5]
def baseStart_1916573 : Nat := 118140960795 + 1916573 * 2 ^ 59
def prefixEnd_1916573 : Nat := 4983230072969 + 3 ^ 40 * 1916573 * 2
def baseEnd_1916573 : Nat := 328041052809878377674449

theorem tailTrace_1916573 : CollatzResearch.WordTrace tailWord_1916573 prefixEnd_1916573 328041052809878377674449 := by
  unfold tailWord_1916573
  simp only [CollatzResearch.WordTrace]
  refine ⟨69903160085590820453866373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46602106723727213635910915 69903160085590820453866373)
  ·
    refine ⟨13106842516048278835099945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69903160085590820453866373 13106842516048278835099945)
    ·
      refine ⟨9830131887036209126324959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13106842516048278835099945 9830131887036209126324959)
      ·
        refine ⟨14745197830554313689487439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9830131887036209126324959 14745197830554313689487439)
        ·
          refine ⟨22117796745831470534231159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14745197830554313689487439 22117796745831470534231159)
          ·
            refine ⟨33176695118747205801346739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22117796745831470534231159 33176695118747205801346739)
            ·
              refine ⟨49765042678120808702020109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33176695118747205801346739 49765042678120808702020109)
              ·
                refine ⟨18661891004295303263257541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49765042678120808702020109 18661891004295303263257541)
                ·
                  refine ⟨3499104563305369361860789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18661891004295303263257541 3499104563305369361860789)
                  ·
                    refine ⟨328041052809878377674449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3499104563305369361860789 328041052809878377674449)
                    ·
                      rfl

theorem cell23_1916573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_1916573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916573 prefixEnd_1916573 := by exact prefixLift 1916573
  have htrace : WordTrace (prefixWord ++ tailWord_1916573) baseStart_1916573 baseEnd_1916573 := by
    simpa [prefixWord, tailWord_1916573, baseEnd_1916573] using wordTrace_append hprefix tailTrace_1916573
  have hstable : (prefixWord ++ tailWord_1916573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916573).length < 2 ^ (prefixWord ++ tailWord_1916573).sum := by decide
  have hdescent : baseEnd_1916573 < baseStart_1916573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916633 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 8]
def baseStart_1916633 : Nat := 118140960795 + 1916633 * 2 ^ 59
def prefixEnd_1916633 : Nat := 4983230072969 + 3 ^ 40 * 1916633 * 2
def baseEnd_1916633 : Nat := 109350440807656099808119

theorem tailTrace_1916633 : CollatzResearch.WordTrace tailWord_1916633 prefixEnd_1916633 109350440807656099808119 := by
  unfold tailWord_1916633
  simp only [CollatzResearch.WordTrace]
  refine ⟨69905348465373450701050553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46603565643582300467367035 69905348465373450701050553)
  ·
    refine ⟨52429011349030088025787915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69905348465373450701050553 52429011349030088025787915)
    ·
      refine ⟨78643517023545132038681873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52429011349030088025787915 78643517023545132038681873)
      ·
        refine ⟨58982637767658849029011405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78643517023545132038681873 58982637767658849029011405)
        ·
          refine ⟨22118489162872068385879277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58982637767658849029011405 22118489162872068385879277)
          ·
            refine ⟨8294433436077025644704729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22118489162872068385879277 8294433436077025644704729)
            ·
              refine ⟨6220825077057769233528547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8294433436077025644704729 6220825077057769233528547)
              ·
                refine ⟨9331237615586653850292821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6220825077057769233528547 9331237615586653850292821)
                ·
                  refine ⟨109350440807656099808119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9331237615586653850292821 109350440807656099808119)
                  ·
                    rfl

theorem cell23_1916633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 8].length) (baseStart_1916633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916633 prefixEnd_1916633 := by exact prefixLift 1916633
  have htrace : WordTrace (prefixWord ++ tailWord_1916633) baseStart_1916633 baseEnd_1916633 := by
    simpa [prefixWord, tailWord_1916633, baseEnd_1916633] using wordTrace_append hprefix tailTrace_1916633
  have hstable : (prefixWord ++ tailWord_1916633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916633).length < 2 ^ (prefixWord ++ tailWord_1916633).sum := by decide
  have hdescent : baseEnd_1916633 < baseStart_1916633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916700 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_1916700 : Nat := 118140960795 + 1916700 * 2 ^ 59
def prefixEnd_1916700 : Nat := 4983230072969 + 3 ^ 40 * 1916700 * 2
def baseEnd_1916700 : Nat := 984188370472756136135263

theorem tailTrace_1916700 : CollatzResearch.WordTrace tailWord_1916700 prefixEnd_1916700 984188370472756136135263 := by
  unfold tailWord_1916700
  simp only [CollatzResearch.WordTrace]
  refine ⟨34953896078065360571869777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46605194770753814095826369 34953896078065360571869777)
  ·
    refine ⟨26215422058549020428902333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34953896078065360571869777 26215422058549020428902333)
    ·
      refine ⟨9830783271955882660838375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26215422058549020428902333 9830783271955882660838375)
      ·
        refine ⟨14746174907933823991257563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9830783271955882660838375 14746174907933823991257563)
        ·
          refine ⟨22119262361900735986886345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14746174907933823991257563 22119262361900735986886345)
          ·
            refine ⟨16589446771425551990164759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22119262361900735986886345 16589446771425551990164759)
            ·
              refine ⟨24884170157138327985247139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16589446771425551990164759 24884170157138327985247139)
              ·
                refine ⟨37326255235707491977870709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24884170157138327985247139 37326255235707491977870709)
                ·
                  refine ⟨3499336428347577372925379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37326255235707491977870709 3499336428347577372925379)
                  ·
                    refine ⟨5249004642521366059388069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3499336428347577372925379 5249004642521366059388069)
                    ·
                      refine ⟨984188370472756136135263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5249004642521366059388069 984188370472756136135263)
                      ·
                        rfl

theorem cell23_1916700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_1916700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916700 prefixEnd_1916700 := by exact prefixLift 1916700
  have htrace : WordTrace (prefixWord ++ tailWord_1916700) baseStart_1916700 baseEnd_1916700 := by
    simpa [prefixWord, tailWord_1916700, baseEnd_1916700] using wordTrace_append hprefix tailTrace_1916700
  have hstable : (prefixWord ++ tailWord_1916700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916700).length < 2 ^ (prefixWord ++ tailWord_1916700).sum := by decide
  have hdescent : baseEnd_1916700 < baseStart_1916700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916734 : List Nat := [4, 2, 1, 2, 2, 2, 1, 3, 1, 1, 4]
def baseStart_1916734 : Nat := 118140960795 + 1916734 * 2 ^ 59
def prefixEnd_1916734 : Nat := 4983230072969 + 3 ^ 40 * 1916734 * 2
def baseEnd_1916734 : Nat := 984205828815009003110107

theorem tailTrace_1916734 : CollatzResearch.WordTrace tailWord_1916734 prefixEnd_1916734 984205828815009003110107 := by
  unfold tailWord_1916734
  simp only [CollatzResearch.WordTrace]
  refine ⟨8738629029750943118809657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46606021492005029966984837 8738629029750943118809657)
  ·
    refine ⟨6553971772313207339107243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8738629029750943118809657 6553971772313207339107243)
    ·
      refine ⟨9830957658469811008660865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6553971772313207339107243 9830957658469811008660865)
      ·
        refine ⟨7373218243852358256495649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9830957658469811008660865 7373218243852358256495649)
        ·
          refine ⟨5529913682889268692371737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7373218243852358256495649 5529913682889268692371737)
          ·
            refine ⟨4147435262166951519278803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5529913682889268692371737 4147435262166951519278803)
            ·
              refine ⟨6221152893250427278918205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4147435262166951519278803 6221152893250427278918205)
              ·
                refine ⟨2332932334968910229594327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6221152893250427278918205 2332932334968910229594327)
                ·
                  refine ⟨3499398502453365344391491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2332932334968910229594327 3499398502453365344391491)
                  ·
                    refine ⟨5249097753680048016587237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3499398502453365344391491 5249097753680048016587237)
                    ·
                      refine ⟨984205828815009003110107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5249097753680048016587237 984205828815009003110107)
                      ·
                        rfl

theorem cell23_1916734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_1916734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916734 prefixEnd_1916734 := by exact prefixLift 1916734
  have htrace : WordTrace (prefixWord ++ tailWord_1916734) baseStart_1916734 baseEnd_1916734 := by
    simpa [prefixWord, tailWord_1916734, baseEnd_1916734] using wordTrace_append hprefix tailTrace_1916734
  have hstable : (prefixWord ++ tailWord_1916734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916734).length < 2 ^ (prefixWord ++ tailWord_1916734).sum := by decide
  have hdescent : baseEnd_1916734 < baseStart_1916734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916744 : List Nat := [2, 1, 3, 1, 1, 6, 1, 2, 2, 4]
def baseStart_1916744 : Nat := 118140960795 + 1916744 * 2 ^ 59
def prefixEnd_1916744 : Nat := 4983230072969 + 3 ^ 40 * 1916744 * 2
def baseEnd_1916744 : Nat := 328070321207184654661687

theorem tailTrace_1916744 : CollatzResearch.WordTrace tailWord_1916744 prefixEnd_1916744 328070321207184654661687 := by
  unfold tailWord_1916744
  simp only [CollatzResearch.WordTrace]
  refine ⟨34954698483985658329170643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46606264645314211105560857 34954698483985658329170643)
  ·
    refine ⟨52432047725978487493755965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34954698483985658329170643 52432047725978487493755965)
    ·
      refine ⟨19662017897241932810158487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52432047725978487493755965 19662017897241932810158487)
      ·
        refine ⟨29493026845862899215237731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19662017897241932810158487 29493026845862899215237731)
        ·
          refine ⟨44239540268794348822856597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29493026845862899215237731 44239540268794348822856597)
          ·
            refine ⟨2073728450099735101071403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 44239540268794348822856597 2073728450099735101071403)
            ·
              refine ⟨3110592675149602651607105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2073728450099735101071403 3110592675149602651607105)
              ·
                refine ⟨2332944506362201988705329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3110592675149602651607105 2332944506362201988705329)
                ·
                  refine ⟨1749708379771651491528997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2332944506362201988705329 1749708379771651491528997)
                  ·
                    refine ⟨328070321207184654661687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1749708379771651491528997 328070321207184654661687)
                    ·
                      rfl

theorem cell23_1916744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_1916744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916744 prefixEnd_1916744 := by exact prefixLift 1916744
  have htrace : WordTrace (prefixWord ++ tailWord_1916744) baseStart_1916744 baseEnd_1916744 := by
    simpa [prefixWord, tailWord_1916744, baseEnd_1916744] using wordTrace_append hprefix tailTrace_1916744
  have hstable : (prefixWord ++ tailWord_1916744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916744).length < 2 ^ (prefixWord ++ tailWord_1916744).sum := by decide
  have hdescent : baseEnd_1916744 < baseStart_1916744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916750 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3]
def baseStart_1916750 : Nat := 118140960795 + 1916750 * 2 ^ 59
def prefixEnd_1916750 : Nat := 4983230072969 + 3 ^ 40 * 1916750 * 2
def baseEnd_1916750 : Nat := 984214044505480940510033

theorem tailTrace_1916750 : CollatzResearch.WordTrace tailWord_1916750 prefixEnd_1916750 984214044505480940510033 := by
  unfold tailWord_1916750
  simp only [CollatzResearch.WordTrace]
  refine ⟨8738701975743697460382463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46606410537299719788706469 8738701975743697460382463)
  ·
    refine ⟨13108052963615546190573695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8738701975743697460382463 13108052963615546190573695)
    ·
      refine ⟨19662079445423319285860543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13108052963615546190573695 19662079445423319285860543)
      ·
        refine ⟨29493119168134978928790815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19662079445423319285860543 29493119168134978928790815)
        ·
          refine ⟨44239678752202468393186223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29493119168134978928790815 44239678752202468393186223)
          ·
            refine ⟨66359518128303702589779335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44239678752202468393186223 66359518128303702589779335)
            ·
              refine ⟨99539277192455553884669003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66359518128303702589779335 99539277192455553884669003)
              ·
                refine ⟨149308915788683330827003505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99539277192455553884669003 149308915788683330827003505)
                ·
                  refine ⟨111981686841512498120252629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149308915788683330827003505 111981686841512498120252629)
                  ·
                    refine ⟨2624570785347949174693421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 111981686841512498120252629 2624570785347949174693421)
                    ·
                      refine ⟨984214044505480940510033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2624570785347949174693421 984214044505480940510033)
                      ·
                        rfl

theorem cell23_1916750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_1916750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916750 prefixEnd_1916750 := by exact prefixLift 1916750
  have htrace : WordTrace (prefixWord ++ tailWord_1916750) baseStart_1916750 baseEnd_1916750 := by
    simpa [prefixWord, tailWord_1916750, baseEnd_1916750] using wordTrace_append hprefix tailTrace_1916750
  have hstable : (prefixWord ++ tailWord_1916750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916750).length < 2 ^ (prefixWord ++ tailWord_1916750).sum := by decide
  have hdescent : baseEnd_1916750 < baseStart_1916750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916763 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 7]
def baseStart_1916763 : Nat := 118140960795 + 1916763 * 2 ^ 59
def prefixEnd_1916763 : Nat := 4983230072969 + 3 ^ 40 * 1916763 * 2
def baseEnd_1916763 : Nat := 984220719753989389647473

theorem tailTrace_1916763 : CollatzResearch.WordTrace tailWord_1916763 prefixEnd_1916763 984220719753989389647473 := by
  unfold tailWord_1916763
  simp only [CollatzResearch.WordTrace]
  refine ⟨69910089954902482903282943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46606726636601655268855295 69910089954902482903282943)
  ·
    refine ⟨104865134932353724354924415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69910089954902482903282943 104865134932353724354924415)
    ·
      refine ⟨157297702398530586532386623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104865134932353724354924415 157297702398530586532386623)
      ·
        refine ⟨235946553597795879798579935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157297702398530586532386623 235946553597795879798579935)
        ·
          refine ⟨353919830396693819697869903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235946553597795879798579935 353919830396693819697869903)
          ·
            refine ⟨530879745595040729546804855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 353919830396693819697869903 530879745595040729546804855)
            ·
              refine ⟨796319618392561094320207283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 530879745595040729546804855 796319618392561094320207283)
              ·
                refine ⟨1194479427588841641480310925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 796319618392561094320207283 1194479427588841641480310925)
                ·
                  refine ⟨447929785345815615555116597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1194479427588841641480310925 447929785345815615555116597)
                  ·
                    refine ⟨41993417376170213958292181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 447929785345815615555116597 41993417376170213958292181)
                    ·
                      refine ⟨984220719753989389647473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41993417376170213958292181 984220719753989389647473)
                      ·
                        rfl

theorem cell23_1916763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 7].length) (baseStart_1916763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916763 prefixEnd_1916763 := by exact prefixLift 1916763
  have htrace : WordTrace (prefixWord ++ tailWord_1916763) baseStart_1916763 baseEnd_1916763 := by
    simpa [prefixWord, tailWord_1916763, baseEnd_1916763] using wordTrace_append hprefix tailTrace_1916763
  have hstable : (prefixWord ++ tailWord_1916763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916763).length < 2 ^ (prefixWord ++ tailWord_1916763).sum := by decide
  have hdescent : baseEnd_1916763 < baseStart_1916763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916767 : List Nat := [1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 3]
def baseStart_1916767 : Nat := 118140960795 + 1916767 * 2 ^ 59
def prefixEnd_1916767 : Nat := 4983230072969 + 3 ^ 40 * 1916767 * 2
def baseEnd_1916767 : Nat := 984222773676607373997455

theorem tailTrace_1916767 : CollatzResearch.WordTrace tailWord_1916767 prefixEnd_1916767 984222773676607373997455 := by
  unfold tailWord_1916767
  simp only [CollatzResearch.WordTrace]
  refine ⟨69910235846887991586428555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46606823897925327724285703 69910235846887991586428555)
  ·
    refine ⟨104865353770331987379642833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69910235846887991586428555 104865353770331987379642833)
    ·
      refine ⟨78649015327748990534732125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104865353770331987379642833 78649015327748990534732125)
      ·
        refine ⟨29493380747905871450524547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78649015327748990534732125 29493380747905871450524547)
        ·
          refine ⟨44240071121858807175786821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29493380747905871450524547 44240071121858807175786821)
          ·
            refine ⟨8295013335348526345460029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44240071121858807175786821 8295013335348526345460029)
            ·
              refine ⟨3110630000755697379547511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8295013335348526345460029 3110630000755697379547511)
              ·
                refine ⟨4665945001133546069321267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3110630000755697379547511 4665945001133546069321267)
                ·
                  refine ⟨6998917501700319103981901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4665945001133546069321267 6998917501700319103981901)
                  ·
                    refine ⟨2624594063137619663993213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6998917501700319103981901 2624594063137619663993213)
                    ·
                      refine ⟨984222773676607373997455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2624594063137619663993213 984222773676607373997455)
                      ·
                        rfl

theorem cell23_1916767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 3].length) (baseStart_1916767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916767 prefixEnd_1916767 := by exact prefixLift 1916767
  have htrace : WordTrace (prefixWord ++ tailWord_1916767) baseStart_1916767 baseEnd_1916767 := by
    simpa [prefixWord, tailWord_1916767, baseEnd_1916767] using wordTrace_append hprefix tailTrace_1916767
  have hstable : (prefixWord ++ tailWord_1916767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916767).length < 2 ^ (prefixWord ++ tailWord_1916767).sum := by decide
  have hdescent : baseEnd_1916767 < baseStart_1916767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916777 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 3, 3, 2]
def baseStart_1916777 : Nat := 118140960795 + 1916777 * 2 ^ 59
def prefixEnd_1916777 : Nat := 4983230072969 + 3 ^ 40 * 1916777 * 2
def baseEnd_1916777 : Nat := 984227908483152334872409

theorem tailTrace_1916777 : CollatzResearch.WordTrace tailWord_1916777 prefixEnd_1916777 984227908483152334872409 := by
  unfold tailWord_1916777
  simp only [CollatzResearch.WordTrace]
  refine ⟨69910600576851763294292585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46607067051234508862861723 69910600576851763294292585)
  ·
    refine ⟨52432950432638822470719439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69910600576851763294292585 52432950432638822470719439)
    ·
      refine ⟨78649425648958233706079159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52432950432638822470719439 78649425648958233706079159)
      ·
        refine ⟨117974138473437350559118739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78649425648958233706079159 117974138473437350559118739)
        ·
          refine ⟨176961207710156025838678109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117974138473437350559118739 176961207710156025838678109)
          ·
            refine ⟨66360452891308509689504291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 176961207710156025838678109 66360452891308509689504291)
            ·
              refine ⟨99540679336962764534256437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66360452891308509689504291 99540679336962764534256437)
              ·
                refine ⟨9331938687840259175086541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99540679336962764534256437 9331938687840259175086541)
                ·
                  refine ⟨3499477007940097190657453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9331938687840259175086541 3499477007940097190657453)
                  ·
                    refine ⟨1312303877977536446496545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3499477007940097190657453 1312303877977536446496545)
                    ·
                      refine ⟨984227908483152334872409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1312303877977536446496545 984227908483152334872409)
                      ·
                        rfl

theorem cell23_1916777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 3, 3, 2].length) (baseStart_1916777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916777 prefixEnd_1916777 := by exact prefixLift 1916777
  have htrace : WordTrace (prefixWord ++ tailWord_1916777) baseStart_1916777 baseEnd_1916777 := by
    simpa [prefixWord, tailWord_1916777, baseEnd_1916777] using wordTrace_append hprefix tailTrace_1916777
  have hstable : (prefixWord ++ tailWord_1916777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916777).length < 2 ^ (prefixWord ++ tailWord_1916777).sum := by decide
  have hdescent : baseEnd_1916777 < baseStart_1916777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916780 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 5]
def baseStart_1916780 : Nat := 118140960795 + 1916780 * 2 ^ 59
def prefixEnd_1916780 : Nat := 4983230072969 + 3 ^ 40 * 1916780 * 2
def baseEnd_1916780 : Nat := 984229448925115823134895

theorem tailTrace_1916780 : CollatzResearch.WordTrace tailWord_1916780 prefixEnd_1916780 984229448925115823134895 := by
  unfold tailWord_1916780
  simp only [CollatzResearch.WordTrace]
  refine ⟨34955354997920447403325897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46607139997227263204434529 34955354997920447403325897)
  ·
    refine ⟨26216516248440335552494423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34955354997920447403325897 26216516248440335552494423)
    ·
      refine ⟨39324774372660503328741635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26216516248440335552494423 39324774372660503328741635)
      ·
        refine ⟨58987161558990754993112453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39324774372660503328741635 58987161558990754993112453)
        ·
          refine ⟨11060092792310766561208585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58987161558990754993112453 11060092792310766561208585)
          ·
            refine ⟨8295069594233074920906439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11060092792310766561208585 8295069594233074920906439)
            ·
              refine ⟨12442604391349612381359659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8295069594233074920906439 12442604391349612381359659)
              ·
                refine ⟨18663906587024418572039489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12442604391349612381359659 18663906587024418572039489)
                ·
                  refine ⟨13997929940268313929029617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18663906587024418572039489 13997929940268313929029617)
                  ·
                    refine ⟨10498447455201235446772213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13997929940268313929029617 10498447455201235446772213)
                    ·
                      refine ⟨984229448925115823134895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10498447455201235446772213 984229448925115823134895)
                      ·
                        rfl

theorem cell23_1916780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_1916780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916780 prefixEnd_1916780 := by exact prefixLift 1916780
  have htrace : WordTrace (prefixWord ++ tailWord_1916780) baseStart_1916780 baseEnd_1916780 := by
    simpa [prefixWord, tailWord_1916780, baseEnd_1916780] using wordTrace_append hprefix tailTrace_1916780
  have hstable : (prefixWord ++ tailWord_1916780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916780).length < 2 ^ (prefixWord ++ tailWord_1916780).sum := by decide
  have hdescent : baseEnd_1916780 < baseStart_1916780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916794 : List Nat := [3, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2]
def baseStart_1916794 : Nat := 118140960795 + 1916794 * 2 ^ 59
def prefixEnd_1916794 : Nat := 4983230072969 + 3 ^ 40 * 1916794 * 2
def baseEnd_1916794 : Nat := 984236637654278768359831

theorem tailTrace_1916794 : CollatzResearch.WordTrace tailWord_1916794 prefixEnd_1916794 984236637654278768359831 := by
  unfold tailWord_1916794
  simp only [CollatzResearch.WordTrace]
  refine ⟨17477805154447543799415359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46607480411860116798440957 17477805154447543799415359)
  ·
    refine ⟨26216707731671315699123039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17477805154447543799415359 26216707731671315699123039)
    ·
      refine ⟨39325061597506973548684559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26216707731671315699123039 39325061597506973548684559)
      ·
        refine ⟨58987592396260460323026839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39325061597506973548684559 58987592396260460323026839)
        ·
          refine ⟨88481388594390690484540259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58987592396260460323026839 88481388594390690484540259)
          ·
            refine ⟨132722082891586035726810389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88481388594390690484540259 132722082891586035726810389)
            ·
              refine ⟨6221347635543095424694237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132722082891586035726810389 6221347635543095424694237)
              ·
                refine ⟨2333005363328660784260339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6221347635543095424694237 2333005363328660784260339)
                ·
                  refine ⟨3499508044992991176390509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2333005363328660784260339 3499508044992991176390509)
                  ·
                    refine ⟨1312315516872371691146441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3499508044992991176390509 1312315516872371691146441)
                    ·
                      refine ⟨984236637654278768359831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1312315516872371691146441 984236637654278768359831)
                      ·
                        rfl

theorem cell23_1916794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 1, 3, 2].length) (baseStart_1916794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916794 prefixEnd_1916794 := by exact prefixLift 1916794
  have htrace : WordTrace (prefixWord ++ tailWord_1916794) baseStart_1916794 baseEnd_1916794 := by
    simpa [prefixWord, tailWord_1916794, baseEnd_1916794] using wordTrace_append hprefix tailTrace_1916794
  have hstable : (prefixWord ++ tailWord_1916794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916794).length < 2 ^ (prefixWord ++ tailWord_1916794).sum := by decide
  have hdescent : baseEnd_1916794 < baseStart_1916794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916818 : List Nat := [3, 2, 3, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_1916818 : Nat := 118140960795 + 1916818 * 2 ^ 59
def prefixEnd_1916818 : Nat := 4983230072969 + 3 ^ 40 * 1916818 * 2
def baseEnd_1916818 : Nat := 984248961189986674459721

theorem tailTrace_1916818 : CollatzResearch.WordTrace tailWord_1916818 prefixEnd_1916818 984248961189986674459721 := by
  unfold tailWord_1916818
  simp only [CollatzResearch.WordTrace]
  refine ⟨17478023992425806824133777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46608063979802151531023405 17478023992425806824133777)
  ·
    refine ⟨13108517994319355118100333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17478023992425806824133777 13108517994319355118100333)
    ·
      refine ⟨4915694247869758169287625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13108517994319355118100333 4915694247869758169287625)
      ·
        refine ⟨3686770685902318626965719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4915694247869758169287625 3686770685902318626965719)
        ·
          refine ⟨5530156028853477940448579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3686770685902318626965719 5530156028853477940448579)
          ·
            refine ⟨8295234043280216910672869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5530156028853477940448579 8295234043280216910672869)
            ·
              refine ⟨1555356383115040670751163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8295234043280216910672869 1555356383115040670751163)
              ·
                refine ⟨2333034574672561006126745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1555356383115040670751163 2333034574672561006126745)
                ·
                  refine ⟨1749775931004420754595059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2333034574672561006126745 1749775931004420754595059)
                  ·
                    refine ⟨2624663896506631131892589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1749775931004420754595059 2624663896506631131892589)
                    ·
                      refine ⟨984248961189986674459721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2624663896506631131892589 984248961189986674459721)
                      ·
                        rfl

theorem cell23_1916818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_1916818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916818 prefixEnd_1916818 := by exact prefixLift 1916818
  have htrace : WordTrace (prefixWord ++ tailWord_1916818) baseStart_1916818 baseEnd_1916818 := by
    simpa [prefixWord, tailWord_1916818, baseEnd_1916818] using wordTrace_append hprefix tailTrace_1916818
  have hstable : (prefixWord ++ tailWord_1916818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916818).length < 2 ^ (prefixWord ++ tailWord_1916818).sum := by decide
  have hdescent : baseEnd_1916818 < baseStart_1916818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916822 : List Nat := [5, 3, 1, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_1916822 : Nat := 118140960795 + 1916822 * 2 ^ 59
def prefixEnd_1916822 : Nat := 4983230072969 + 3 ^ 40 * 1916822 * 2
def baseEnd_1916822 : Nat := 984251015112604658809703

theorem tailTrace_1916822 : CollatzResearch.WordTrace tailWord_1916822 prefixEnd_1916822 984251015112604658809703 := by
  unfold tailWord_1916822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4369515116355545998730045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46608161241125823986453813 4369515116355545998730045)
  ·
    refine ⟨1638568168633329749523767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4369515116355545998730045 1638568168633329749523767)
    ·
      refine ⟨2457852252949994624285651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1638568168633329749523767 2457852252949994624285651)
      ·
        refine ⟨3686778379424991936428477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2457852252949994624285651 3686778379424991936428477)
        ·
          refine ⟨1382541892284371976160679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3686778379424991936428477 1382541892284371976160679)
          ·
            refine ⟨2073812838426557964241019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382541892284371976160679 2073812838426557964241019)
            ·
              refine ⟨3110719257639836946361529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2073812838426557964241019 3110719257639836946361529)
              ·
                refine ⟨2333039443229877709771147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3110719257639836946361529 2333039443229877709771147)
                ·
                  refine ⟨3499559164844816564656721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2333039443229877709771147 3499559164844816564656721)
                  ·
                    refine ⟨2624669373633612423492541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3499559164844816564656721 2624669373633612423492541)
                    ·
                      refine ⟨984251015112604658809703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2624669373633612423492541 984251015112604658809703)
                      ·
                        rfl

theorem cell23_1916822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_1916822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916822 prefixEnd_1916822 := by exact prefixLift 1916822
  have htrace : WordTrace (prefixWord ++ tailWord_1916822) baseStart_1916822 baseEnd_1916822 := by
    simpa [prefixWord, tailWord_1916822, baseEnd_1916822] using wordTrace_append hprefix tailTrace_1916822
  have hstable : (prefixWord ++ tailWord_1916822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916822).length < 2 ^ (prefixWord ++ tailWord_1916822).sum := by decide
  have hdescent : baseEnd_1916822 < baseStart_1916822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916828 : List Nat := [2, 2, 3, 3, 1, 3, 1, 2, 1, 3, 2]
def baseStart_1916828 : Nat := 118140960795 + 1916828 * 2 ^ 59
def prefixEnd_1916828 : Nat := 4983230072969 + 3 ^ 40 * 1916828 * 2
def baseEnd_1916828 : Nat := 984254095996531635334675

theorem tailTrace_1916828 : CollatzResearch.WordTrace tailWord_1916828 prefixEnd_1916828 984254095996531635334675 := by
  unfold tailWord_1916828
  simp only [CollatzResearch.WordTrace]
  refine ⟨34956230349833499502199569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46608307133111332669599425 34956230349833499502199569)
  ·
    refine ⟨26217172762375124626649677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34956230349833499502199569 26217172762375124626649677)
    ·
      refine ⟨9831439785890671734993629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26217172762375124626649677 9831439785890671734993629)
      ·
        refine ⟨3686789919709001900622611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9831439785890671734993629 3686789919709001900622611)
        ·
          refine ⟨5530184879563502850933917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3686789919709001900622611 5530184879563502850933917)
          ·
            refine ⟨2073819329836313569100219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5530184879563502850933917 2073819329836313569100219)
            ·
              refine ⟨3110728994754470353650329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2073819329836313569100219 3110728994754470353650329)
              ·
                refine ⟨2333046746065852765237747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3110728994754470353650329 2333046746065852765237747)
                ·
                  refine ⟨3499570119098779147856621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2333046746065852765237747 3499570119098779147856621)
                  ·
                    refine ⟨1312338794662042180446233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3499570119098779147856621 1312338794662042180446233)
                    ·
                      refine ⟨984254095996531635334675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1312338794662042180446233 984254095996531635334675)
                      ·
                        rfl

theorem cell23_1916828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_1916828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916828 prefixEnd_1916828 := by exact prefixLift 1916828
  have htrace : WordTrace (prefixWord ++ tailWord_1916828) baseStart_1916828 baseEnd_1916828 := by
    simpa [prefixWord, tailWord_1916828, baseEnd_1916828] using wordTrace_append hprefix tailTrace_1916828
  have hstable : (prefixWord ++ tailWord_1916828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916828).length < 2 ^ (prefixWord ++ tailWord_1916828).sum := by decide
  have hdescent : baseEnd_1916828 < baseStart_1916828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916847 : List Nat := [1, 1, 2, 1, 2, 2, 4, 5, 5]
def baseStart_1916847 : Nat := 118140960795 + 1916847 * 2 ^ 59
def prefixEnd_1916847 : Nat := 4983230072969 + 3 ^ 40 * 1916847 * 2
def baseEnd_1916847 : Nat := 109362650236551895666343

theorem tailTrace_1916847 : CollatzResearch.WordTrace tailWord_1916847 prefixEnd_1916847 109362650236551895666343 := by
  unfold tailWord_1916847
  simp only [CollatzResearch.WordTrace]
  refine ⟨69913153686598165249340795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46608769124398776832893863 69913153686598165249340795)
  ·
    refine ⟨104869730529897247874011193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69913153686598165249340795 104869730529897247874011193)
    ·
      refine ⟨78652297897422935905508395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104869730529897247874011193 78652297897422935905508395)
      ·
        refine ⟨117978446846134403858262593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78652297897422935905508395 117978446846134403858262593)
        ·
          refine ⟨88483835134600802893696945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 117978446846134403858262593 88483835134600802893696945)
          ·
            refine ⟨66362876350950602170272709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88483835134600802893696945 66362876350950602170272709)
            ·
              refine ⟨12443039315803237906926133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66362876350950602170272709 12443039315803237906926133)
              ·
                refine ⟨1166534935856553553774325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12443039315803237906926133 1166534935856553553774325)
                ·
                  refine ⟨109362650236551895666343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1166534935856553553774325 109362650236551895666343)
                  ·
                    rfl

theorem cell23_1916847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 5].length) (baseStart_1916847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916847 prefixEnd_1916847 := by exact prefixLift 1916847
  have htrace : WordTrace (prefixWord ++ tailWord_1916847) baseStart_1916847 baseEnd_1916847 := by
    simpa [prefixWord, tailWord_1916847, baseEnd_1916847] using wordTrace_append hprefix tailTrace_1916847
  have hstable : (prefixWord ++ tailWord_1916847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916847).length < 2 ^ (prefixWord ++ tailWord_1916847).sum := by decide
  have hdescent : baseEnd_1916847 < baseStart_1916847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916857 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 2, 3, 3]
def baseStart_1916857 : Nat := 118140960795 + 1916857 * 2 ^ 59
def prefixEnd_1916857 : Nat := 4983230072969 + 3 ^ 40 * 1916857 * 2
def baseEnd_1916857 : Nat := 984268986935512021872041

theorem tailTrace_1916857 : CollatzResearch.WordTrace tailWord_1916857 prefixEnd_1916857 984268986935512021872041 := by
  unfold tailWord_1916857
  simp only [CollatzResearch.WordTrace]
  refine ⟨69913518416561936957204825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46609012277707957971469883 69913518416561936957204825)
  ·
    refine ⟨52435138812421452717903619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69913518416561936957204825 52435138812421452717903619)
    ·
      refine ⟨78652708218632179076855429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52435138812421452717903619 78652708218632179076855429)
      ·
        refine ⟨14747382790993533576910393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78652708218632179076855429 14747382790993533576910393)
        ·
          refine ⟨11060537093245150182682795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14747382790993533576910393 11060537093245150182682795)
          ·
            refine ⟨16590805639867725274024193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11060537093245150182682795 16590805639867725274024193)
            ·
              refine ⟨12443104229900793955518145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16590805639867725274024193 12443104229900793955518145)
              ·
                refine ⟨9332328172425595466638609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12443104229900793955518145 9332328172425595466638609)
                ·
                  refine ⟨6999246129319196599978957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9332328172425595466638609 6999246129319196599978957)
                  ·
                    refine ⟨2624717298494698724992109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6999246129319196599978957 2624717298494698724992109)
                    ·
                      refine ⟨984268986935512021872041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2624717298494698724992109 984268986935512021872041)
                      ·
                        rfl

theorem cell23_1916857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_1916857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916857 prefixEnd_1916857 := by exact prefixLift 1916857
  have htrace : WordTrace (prefixWord ++ tailWord_1916857) baseStart_1916857 baseEnd_1916857 := by
    simpa [prefixWord, tailWord_1916857, baseEnd_1916857] using wordTrace_append hprefix tailTrace_1916857
  have hstable : (prefixWord ++ tailWord_1916857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916857).length < 2 ^ (prefixWord ++ tailWord_1916857).sum := by decide
  have hdescent : baseEnd_1916857 < baseStart_1916857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916884 : List Nat := [2, 4, 1, 2, 1, 1, 1, 2, 2, 5, 2]
def baseStart_1916884 : Nat := 118140960795 + 1916884 * 2 ^ 59
def prefixEnd_1916884 : Nat := 4983230072969 + 3 ^ 40 * 1916884 * 2
def baseEnd_1916884 : Nat := 984282850913183416234417

theorem tailTrace_1916884 : CollatzResearch.WordTrace tailWord_1916884 prefixEnd_1916884 984282850913183416234417 := by
  unfold tailWord_1916884
  simp only [CollatzResearch.WordTrace]
  refine ⟨34957251593732060284218853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46609668791642747045625137 34957251593732060284218853)
  ·
    refine ⟨6554484673824761303291035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34957251593732060284218853 6554484673824761303291035)
    ·
      refine ⟨9831727010737141954936553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6554484673824761303291035 9831727010737141954936553)
      ·
        refine ⟨7373795258052856466202415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9831727010737141954936553 7373795258052856466202415)
        ·
          refine ⟨11060692887079284699303623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7373795258052856466202415 11060692887079284699303623)
          ·
            refine ⟨16591039330618927048955435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11060692887079284699303623 16591039330618927048955435)
            ·
              refine ⟨24886558995928390573433153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16591039330618927048955435 24886558995928390573433153)
              ·
                refine ⟨18664919246946292930074865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24886558995928390573433153 18664919246946292930074865)
                ·
                  refine ⟨13998689435209719697556149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18664919246946292930074865 13998689435209719697556149)
                  ·
                    refine ⟨1312377134550911221645889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13998689435209719697556149 1312377134550911221645889)
                    ·
                      refine ⟨984282850913183416234417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1312377134550911221645889 984282850913183416234417)
                      ·
                        rfl

theorem cell23_1916884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_1916884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916884 prefixEnd_1916884 := by exact prefixLift 1916884
  have htrace : WordTrace (prefixWord ++ tailWord_1916884) baseStart_1916884 baseEnd_1916884 := by
    simpa [prefixWord, tailWord_1916884, baseEnd_1916884] using wordTrace_append hprefix tailTrace_1916884
  have hstable : (prefixWord ++ tailWord_1916884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916884).length < 2 ^ (prefixWord ++ tailWord_1916884).sum := by decide
  have hdescent : baseEnd_1916884 < baseStart_1916884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916898 : List Nat := [3, 3, 3, 1, 2, 1, 2, 3, 5]
def baseStart_1916898 : Nat := 118140960795 + 1916898 * 2 ^ 59
def prefixEnd_1916898 : Nat := 4983230072969 + 3 ^ 40 * 1916898 * 2
def baseEnd_1916898 : Nat := 109365559960260706828817

theorem tailTrace_1916898 : CollatzResearch.WordTrace tailWord_1916898 prefixEnd_1916898 109365559960260706828817 := by
  unfold tailWord_1916898
  simp only [CollatzResearch.WordTrace]
  refine ⟨17478753452353350239861837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46610009206275600639631565 17478753452353350239861837)
  ·
    refine ⟨6554532544632506339948189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17478753452353350239861837 6554532544632506339948189)
    ·
      refine ⟨2457949704237189877480571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6554532544632506339948189 2457949704237189877480571)
      ·
        refine ⟨3686924556355784816220857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2457949704237189877480571 3686924556355784816220857)
        ·
          refine ⟨2765193417266838612165643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3686924556355784816220857 2765193417266838612165643)
          ·
            refine ⟨4147790125900257918248465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2765193417266838612165643 4147790125900257918248465)
            ·
              refine ⟨3110842594425193438686349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4147790125900257918248465 3110842594425193438686349)
              ·
                refine ⟨1166565972909447539507381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3110842594425193438686349 1166565972909447539507381)
                ·
                  refine ⟨109365559960260706828817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1166565972909447539507381 109365559960260706828817)
                  ·
                    rfl

theorem cell23_1916898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_1916898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916898 prefixEnd_1916898 := by exact prefixLift 1916898
  have htrace : WordTrace (prefixWord ++ tailWord_1916898) baseStart_1916898 baseEnd_1916898 := by
    simpa [prefixWord, tailWord_1916898, baseEnd_1916898] using wordTrace_append hprefix tailTrace_1916898
  have hstable : (prefixWord ++ tailWord_1916898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916898).length < 2 ^ (prefixWord ++ tailWord_1916898).sum := by decide
  have hdescent : baseEnd_1916898 < baseStart_1916898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916924 : List Nat := [2, 2, 2, 1, 2, 2, 4, 1, 3, 4]
def baseStart_1916924 : Nat := 118140960795 + 1916924 * 2 ^ 59
def prefixEnd_1916924 : Nat := 4983230072969 + 3 ^ 40 * 1916924 * 2
def baseEnd_1916924 : Nat := 328101130046454419911411

theorem tailTrace_1916924 : CollatzResearch.WordTrace tailWord_1916924 prefixEnd_1916924 328101130046454419911411 := by
  unfold tailWord_1916924
  simp only [CollatzResearch.WordTrace]
  refine ⟨34957981053659603699946913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46610641404879471599929217 34957981053659603699946913)
  ·
    refine ⟨26218485790244702774960185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34957981053659603699946913 26218485790244702774960185)
    ·
      refine ⟨19663864342683527081220139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26218485790244702774960185 19663864342683527081220139)
      ·
        refine ⟨29495796514025290621830209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19663864342683527081220139 29495796514025290621830209)
        ·
          refine ⟨22121847385518967966372657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29495796514025290621830209 22121847385518967966372657)
          ·
            refine ⟨16591385539139225974779493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22121847385518967966372657 16591385539139225974779493)
            ·
              refine ⟨3110884788588604870271155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16591385539139225974779493 3110884788588604870271155)
              ·
                refine ⟨4666327182882907305406733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3110884788588604870271155 4666327182882907305406733)
                ·
                  refine ⟨1749872693581090239527525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4666327182882907305406733 1749872693581090239527525)
                  ·
                    refine ⟨328101130046454419911411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1749872693581090239527525 328101130046454419911411)
                    ·
                      rfl

theorem cell23_1916924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_1916924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916924 prefixEnd_1916924 := by exact prefixLift 1916924
  have htrace : WordTrace (prefixWord ++ tailWord_1916924) baseStart_1916924 baseEnd_1916924 := by
    simpa [prefixWord, tailWord_1916924, baseEnd_1916924] using wordTrace_append hprefix tailTrace_1916924
  have hstable : (prefixWord ++ tailWord_1916924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916924).length < 2 ^ (prefixWord ++ tailWord_1916924).sum := by decide
  have hdescent : baseEnd_1916924 < baseStart_1916924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916968 : List Nat := [2, 1, 5, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_1916968 : Nat := 118140960795 + 1916968 * 2 ^ 59
def prefixEnd_1916968 : Nat := 4983230072969 + 3 ^ 40 * 1916968 * 2
def baseEnd_1916968 : Nat := 984325983288161087584031

theorem tailTrace_1916968 : CollatzResearch.WordTrace tailWord_1916968 prefixEnd_1916968 984325983288161087584031 := by
  unfold tailWord_1916968
  simp only [CollatzResearch.WordTrace]
  refine ⟨34958783459579901457247779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46611711279439868609663705 34958783459579901457247779)
  ·
    refine ⟨52438175189369852185871669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34958783459579901457247779 52438175189369852185871669)
    ·
      refine ⟨4916078924003423642425469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52438175189369852185871669 4916078924003423642425469)
      ·
        refine ⟨1843529596501283865909551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4916078924003423642425469 1843529596501283865909551)
        ·
          refine ⟨2765294394751925798864327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1843529596501283865909551 2765294394751925798864327)
          ·
            refine ⟨4147941592127888698296491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2765294394751925798864327 4147941592127888698296491)
            ·
              refine ⟨6221912388191833047444737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4147941592127888698296491 6221912388191833047444737)
              ·
                refine ⟨4666434291143874785583553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6221912388191833047444737 4666434291143874785583553)
                ·
                  refine ⟨3499825718357906089187665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4666434291143874785583553 3499825718357906089187665)
                  ·
                    refine ⟨2624869288768429566890749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3499825718357906089187665 2624869288768429566890749)
                    ·
                      refine ⟨984325983288161087584031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2624869288768429566890749 984325983288161087584031)
                      ·
                        rfl

theorem cell23_1916968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_1916968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916968 prefixEnd_1916968 := by exact prefixLift 1916968
  have htrace : WordTrace (prefixWord ++ tailWord_1916968) baseStart_1916968 baseEnd_1916968 := by
    simpa [prefixWord, tailWord_1916968, baseEnd_1916968] using wordTrace_append hprefix tailTrace_1916968
  have hstable : (prefixWord ++ tailWord_1916968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916968).length < 2 ^ (prefixWord ++ tailWord_1916968).sum := by decide
  have hdescent : baseEnd_1916968 < baseStart_1916968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916981 : List Nat := [1, 3, 3, 1, 1, 1, 5, 1, 3, 1, 3]
def baseStart_1916981 : Nat := 118140960795 + 1916981 * 2 ^ 59
def prefixEnd_1916981 : Nat := 4983230072969 + 3 ^ 40 * 1916981 * 2
def baseEnd_1916981 : Nat := 984332658536669536721471

theorem tailTrace_1916981 : CollatzResearch.WordTrace tailWord_1916981 prefixEnd_1916981 984332658536669536721471 := by
  unfold tailWord_1916981
  simp only [CollatzResearch.WordTrace]
  refine ⟨69918041068112706134718797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46612027378741804089812531 69918041068112706134718797)
  ·
    refine ⟨26219265400542264800519549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69918041068112706134718797 26219265400542264800519549)
    ·
      refine ⟨9832224525203349300194831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26219265400542264800519549 9832224525203349300194831)
      ·
        refine ⟨14748336787805023950292247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9832224525203349300194831 14748336787805023950292247)
        ·
          refine ⟨22122505181707535925438371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14748336787805023950292247 22122505181707535925438371)
          ·
            refine ⟨33183757772561303888157557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22122505181707535925438371 33183757772561303888157557)
            ·
              refine ⟨3110977291177622239514771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33183757772561303888157557 3110977291177622239514771)
              ·
                refine ⟨4666465936766433359272157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3110977291177622239514771 4666465936766433359272157)
                ·
                  refine ⟨1749924726287412509727059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4666465936766433359272157 1749924726287412509727059)
                  ·
                    refine ⟨2624887089431118764590589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1749924726287412509727059 2624887089431118764590589)
                    ·
                      refine ⟨984332658536669536721471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2624887089431118764590589 984332658536669536721471)
                      ·
                        rfl

theorem cell23_1916981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_1916981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916981 prefixEnd_1916981 := by exact prefixLift 1916981
  have htrace : WordTrace (prefixWord ++ tailWord_1916981) baseStart_1916981 baseEnd_1916981 := by
    simpa [prefixWord, tailWord_1916981, baseEnd_1916981] using wordTrace_append hprefix tailTrace_1916981
  have hstable : (prefixWord ++ tailWord_1916981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916981).length < 2 ^ (prefixWord ++ tailWord_1916981).sum := by decide
  have hdescent : baseEnd_1916981 < baseStart_1916981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916987 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 4]
def baseStart_1916987 : Nat := 118140960795 + 1916987 * 2 ^ 59
def prefixEnd_1916987 : Nat := 4983230072969 + 3 ^ 40 * 1916987 * 2
def baseEnd_1916987 : Nat := 984335739420596513246443

theorem tailTrace_1916987 : CollatzResearch.WordTrace tailWord_1916987 prefixEnd_1916987 984335739420596513246443 := by
  unfold tailWord_1916987
  simp only [CollatzResearch.WordTrace]
  refine ⟨69918259906090969159437215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46612173270727312772958143 69918259906090969159437215)
  ·
    refine ⟨104877389859136453739155823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69918259906090969159437215 104877389859136453739155823)
    ·
      refine ⟨157316084788704680608733735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104877389859136453739155823 157316084788704680608733735)
      ·
        refine ⟨235974127183057020913100603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157316084788704680608733735 235974127183057020913100603)
        ·
          refine ⟨353961190774585531369650905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 235974127183057020913100603 353961190774585531369650905)
          ·
            refine ⟨265470893080939148527238179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 353961190774585531369650905 265470893080939148527238179)
            ·
              refine ⟨398206339621408722790857269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265470893080939148527238179 398206339621408722790857269)
              ·
                refine ⟨37331844339507067761642869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 398206339621408722790857269 37331844339507067761642869)
                ·
                  refine ⟨3499860406828787602654019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37331844339507067761642869 3499860406828787602654019)
                  ·
                    refine ⟨5249790610243181403981029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3499860406828787602654019 5249790610243181403981029)
                    ·
                      refine ⟨984335739420596513246443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5249790610243181403981029 984335739420596513246443)
                      ·
                        rfl

theorem cell23_1916987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 4].length) (baseStart_1916987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916987 prefixEnd_1916987 := by exact prefixLift 1916987
  have htrace : WordTrace (prefixWord ++ tailWord_1916987) baseStart_1916987 baseEnd_1916987 := by
    simpa [prefixWord, tailWord_1916987, baseEnd_1916987] using wordTrace_append hprefix tailTrace_1916987
  have hstable : (prefixWord ++ tailWord_1916987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916987).length < 2 ^ (prefixWord ++ tailWord_1916987).sum := by decide
  have hdescent : baseEnd_1916987 < baseStart_1916987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916997 : List Nat := [1, 3, 1, 1, 1, 3, 1, 5, 1, 6]
def baseStart_1916997 : Nat := 118140960795 + 1916997 * 2 ^ 59
def prefixEnd_1916997 : Nat := 4983230072969 + 3 ^ 40 * 1916997 * 2
def baseEnd_1916997 : Nat := 328113624742380491373799

theorem tailTrace_1916997 : CollatzResearch.WordTrace tailWord_1916997 prefixEnd_1916997 328113624742380491373799 := by
  unfold tailWord_1916997
  simp only [CollatzResearch.WordTrace]
  refine ⟨69918624636054740867301245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46612416424036493911534163 69918624636054740867301245)
  ·
    refine ⟨26219484238520527825237967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69918624636054740867301245 26219484238520527825237967)
    ·
      refine ⟨39329226357780791737856951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26219484238520527825237967 39329226357780791737856951)
      ·
        refine ⟨58993839536671187606785427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39329226357780791737856951 58993839536671187606785427)
        ·
          refine ⟨88490759305006781410178141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58993839536671187606785427 88490759305006781410178141)
          ·
            refine ⟨33184034739377543028816803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88490759305006781410178141 33184034739377543028816803)
            ·
              refine ⟨49776052109066314543225205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33184034739377543028816803 49776052109066314543225205)
              ·
                refine ⟨4666504885224966988427363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49776052109066314543225205 4666504885224966988427363)
                ·
                  refine ⟨6999757327837450482641045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4666504885224966988427363 6999757327837450482641045)
                  ·
                    refine ⟨328113624742380491373799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6999757327837450482641045 328113624742380491373799)
                    ·
                      rfl

theorem cell23_1916997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_1916997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916997 prefixEnd_1916997 := by exact prefixLift 1916997
  have htrace : WordTrace (prefixWord ++ tailWord_1916997) baseStart_1916997 baseEnd_1916997 := by
    simpa [prefixWord, tailWord_1916997, baseEnd_1916997] using wordTrace_append hprefix tailTrace_1916997
  have hstable : (prefixWord ++ tailWord_1916997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916997).length < 2 ^ (prefixWord ++ tailWord_1916997).sum := by decide
  have hdescent : baseEnd_1916997 < baseStart_1916997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1916998 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_1916998 : Nat := 118140960795 + 1916998 * 2 ^ 59
def prefixEnd_1916998 : Nat := 4983230072969 + 3 ^ 40 * 1916998 * 2
def baseEnd_1916998 : Nat := 984341387707795970208893

theorem tailTrace_1916998 : CollatzResearch.WordTrace tailWord_1916998 prefixEnd_1916998 984341387707795970208893 := by
  unfold tailWord_1916998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2184958159657847438690239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 46612440739367412025391765 2184958159657847438690239)
  ·
    refine ⟨3277437239486771158035359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2184958159657847438690239 3277437239486771158035359)
    ·
      refine ⟨4916155859230156737053039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3277437239486771158035359 4916155859230156737053039)
      ·
        refine ⟨7374233788845235105579559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4916155859230156737053039 7374233788845235105579559)
        ·
          refine ⟨11061350683267852658369339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7374233788845235105579559 11061350683267852658369339)
          ·
            refine ⟨16592026024901778987554009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11061350683267852658369339 16592026024901778987554009)
            ·
              refine ⟨12444019518676334240665507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16592026024901778987554009 12444019518676334240665507)
              ·
                refine ⟨18666029278014501360998261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12444019518676334240665507 18666029278014501360998261)
                ·
                  refine ⟨1749940244813859502593587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18666029278014501360998261 1749940244813859502593587)
                  ·
                    refine ⟨2624910367220789253890381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1749940244813859502593587 2624910367220789253890381)
                    ·
                      refine ⟨984341387707795970208893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2624910367220789253890381 984341387707795970208893)
                      ·
                        rfl

theorem cell23_1916998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_1916998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1916998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1916998 prefixEnd_1916998 := by exact prefixLift 1916998
  have htrace : WordTrace (prefixWord ++ tailWord_1916998) baseStart_1916998 baseEnd_1916998 := by
    simpa [prefixWord, tailWord_1916998, baseEnd_1916998] using wordTrace_append hprefix tailTrace_1916998
  have hstable : (prefixWord ++ tailWord_1916998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1916998).length < 2 ^ (prefixWord ++ tailWord_1916998).sum := by decide
  have hdescent : baseEnd_1916998 < baseStart_1916998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1916998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917004 : List Nat := [2, 2, 1, 3, 1, 1, 2, 1, 2, 6, 2]
def baseStart_1917004 : Nat := 118140960795 + 1917004 * 2 ^ 59
def prefixEnd_1917004 : Nat := 4983230072969 + 3 ^ 40 * 1917004 * 2
def baseEnd_1917004 : Nat := 984344468591722946733865

theorem tailTrace_1917004 : CollatzResearch.WordTrace tailWord_1917004 prefixEnd_1917004 984344468591722946733865 := by
  unfold tailWord_1917004
  simp only [CollatzResearch.WordTrace]
  refine ⟨34959439973514690531403033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46612586631352920708537377 34959439973514690531403033)
  ·
    refine ⟨26219579980136017898552275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34959439973514690531403033 26219579980136017898552275)
    ·
      refine ⟨39329369970204026847828413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26219579980136017898552275 39329369970204026847828413)
      ·
        refine ⟨14748513738826510067935655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39329369970204026847828413 14748513738826510067935655)
        ·
          refine ⟨22122770608239765101903483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14748513738826510067935655 22122770608239765101903483)
          ·
            refine ⟨33184155912359647652855225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22122770608239765101903483 33184155912359647652855225)
            ·
              refine ⟨24888116934269735739641419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33184155912359647652855225 24888116934269735739641419)
              ·
                refine ⟨37332175401404603609462129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24888116934269735739641419 37332175401404603609462129)
                ·
                  refine ⟨27999131551053452707096597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37332175401404603609462129 27999131551053452707096597)
                  ·
                    refine ⟨1312459291455630595645153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27999131551053452707096597 1312459291455630595645153)
                    ·
                      refine ⟨984344468591722946733865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1312459291455630595645153 984344468591722946733865)
                      ·
                        rfl

theorem cell23_1917004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_1917004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917004 prefixEnd_1917004 := by exact prefixLift 1917004
  have htrace : WordTrace (prefixWord ++ tailWord_1917004) baseStart_1917004 baseEnd_1917004 := by
    simpa [prefixWord, tailWord_1917004, baseEnd_1917004] using wordTrace_append hprefix tailTrace_1917004
  have hstable : (prefixWord ++ tailWord_1917004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917004).length < 2 ^ (prefixWord ++ tailWord_1917004).sum := by decide
  have hdescent : baseEnd_1917004 < baseStart_1917004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917007 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 3]
def baseStart_1917007 : Nat := 118140960795 + 1917007 * 2 ^ 59
def prefixEnd_1917007 : Nat := 4983230072969 + 3 ^ 40 * 1917007 * 2
def baseEnd_1917007 : Nat := 984346009033686434996351

theorem tailTrace_1917007 : CollatzResearch.WordTrace tailWord_1917007 prefixEnd_1917007 984346009033686434996351 := by
  unfold tailWord_1917007
  simp only [CollatzResearch.WordTrace]
  refine ⟨69918989366018512575165275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46612659577345675050110183 69918989366018512575165275)
  ·
    refine ⟨104878484049027768862747913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69918989366018512575165275 104878484049027768862747913)
    ·
      refine ⟨78658863036770826647060935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104878484049027768862747913 78658863036770826647060935)
      ·
        refine ⟨117988294555156239970591403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78658863036770826647060935 117988294555156239970591403)
        ·
          refine ⟨176982441832734359955887105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 117988294555156239970591403 176982441832734359955887105)
          ·
            refine ⟨132736831374550769966915329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 176982441832734359955887105 132736831374550769966915329)
            ·
              refine ⟨99552623530913077475186497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132736831374550769966915329 99552623530913077475186497)
              ·
                refine ⟨74664467648184808106389873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99552623530913077475186497 74664467648184808106389873)
                ·
                  refine ⟨55998350736138606079792405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74664467648184808106389873 55998350736138606079792405)
                  ·
                    refine ⟨2624922690756497159990269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 55998350736138606079792405 2624922690756497159990269)
                    ·
                      refine ⟨984346009033686434996351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2624922690756497159990269 984346009033686434996351)
                      ·
                        rfl

theorem cell23_1917007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 3].length) (baseStart_1917007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917007 prefixEnd_1917007 := by exact prefixLift 1917007
  have htrace : WordTrace (prefixWord ++ tailWord_1917007) baseStart_1917007 baseEnd_1917007 := by
    simpa [prefixWord, tailWord_1917007, baseEnd_1917007] using wordTrace_append hprefix tailTrace_1917007
  have hstable : (prefixWord ++ tailWord_1917007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917007).length < 2 ^ (prefixWord ++ tailWord_1917007).sum := by decide
  have hdescent : baseEnd_1917007 < baseStart_1917007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917024 : List Nat := [2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 5]
def baseStart_1917024 : Nat := 118140960795 + 1917024 * 2 ^ 59
def prefixEnd_1917024 : Nat := 4983230072969 + 3 ^ 40 * 1917024 * 2
def baseEnd_1917024 : Nat := 984354738204812868483773

theorem tailTrace_1917024 : CollatzResearch.WordTrace tailWord_1917024 prefixEnd_1917024 984354738204812868483773 := by
  unfold tailWord_1917024
  simp only [CollatzResearch.WordTrace]
  refine ⟨34959804703478462239267063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46613072937971282985689417 34959804703478462239267063)
  ·
    refine ⟨52439707055217693358900595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34959804703478462239267063 52439707055217693358900595)
    ·
      refine ⟨78659560582826540038350893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52439707055217693358900595 78659560582826540038350893)
      ·
        refine ⟨29497335218559952514381585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78659560582826540038350893 29497335218559952514381585)
        ·
          refine ⟨22123001413919964385786189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29497335218559952514381585 22123001413919964385786189)
          ·
            refine ⟨8296125530219986644669821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22123001413919964385786189 8296125530219986644669821)
            ·
              refine ⟨3111047073832494991751183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8296125530219986644669821 3111047073832494991751183)
              ·
                refine ⟨4666570610748742487626775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3111047073832494991751183 4666570610748742487626775)
                ·
                  refine ⟨6999855916123113731440163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4666570610748742487626775 6999855916123113731440163)
                  ·
                    refine ⟨10499783874184670597160245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6999855916123113731440163 10499783874184670597160245)
                    ·
                      refine ⟨984354738204812868483773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10499783874184670597160245 984354738204812868483773)
                      ·
                        rfl

theorem cell23_1917024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_1917024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917024 prefixEnd_1917024 := by exact prefixLift 1917024
  have htrace : WordTrace (prefixWord ++ tailWord_1917024) baseStart_1917024 baseEnd_1917024 := by
    simpa [prefixWord, tailWord_1917024, baseEnd_1917024] using wordTrace_append hprefix tailTrace_1917024
  have hstable : (prefixWord ++ tailWord_1917024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917024).length < 2 ^ (prefixWord ++ tailWord_1917024).sum := by decide
  have hdescent : baseEnd_1917024 < baseStart_1917024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917031 : List Nat := [1, 1, 5, 1, 1, 2, 4, 2, 2, 4]
def baseStart_1917031 : Nat := 118140960795 + 1917031 * 2 ^ 59
def prefixEnd_1917031 : Nat := 4983230072969 + 3 ^ 40 * 1917031 * 2
def baseEnd_1917031 : Nat := 328119444189798113698747

theorem tailTrace_1917031 : CollatzResearch.WordTrace tailWord_1917031 prefixEnd_1917031 328119444189798113698747 := by
  unfold tailWord_1917031
  simp only [CollatzResearch.WordTrace]
  refine ⟨69919864717931564674038947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46613243145287709782692631 69919864717931564674038947)
  ·
    refine ⟨104879797076897347011058421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69919864717931564674038947 104879797076897347011058421)
    ·
      refine ⟨9832480975959126282286727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104879797076897347011058421 9832480975959126282286727)
      ·
        refine ⟨14748721463938689423430091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9832480975959126282286727 14748721463938689423430091)
        ·
          refine ⟨22123082195908034135145137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14748721463938689423430091 22123082195908034135145137)
          ·
            refine ⟨16592311646931025601358853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22123082195908034135145137 16592311646931025601358853)
            ·
              refine ⟨3111058433799567300254785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16592311646931025601358853 3111058433799567300254785)
              ·
                refine ⟨2333293825349675475191089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3111058433799567300254785 2333293825349675475191089)
                ·
                  refine ⟨1749970369012256606393317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2333293825349675475191089 1749970369012256606393317)
                  ·
                    refine ⟨328119444189798113698747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1749970369012256606393317 328119444189798113698747)
                    ·
                      rfl

theorem cell23_1917031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_1917031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917031 prefixEnd_1917031 := by exact prefixLift 1917031
  have htrace : WordTrace (prefixWord ++ tailWord_1917031) baseStart_1917031 baseEnd_1917031 := by
    simpa [prefixWord, tailWord_1917031, baseEnd_1917031] using wordTrace_append hprefix tailTrace_1917031
  have hstable : (prefixWord ++ tailWord_1917031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917031).length < 2 ^ (prefixWord ++ tailWord_1917031).sum := by decide
  have hdescent : baseEnd_1917031 < baseStart_1917031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917038 : List Nat := [4, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2]
def baseStart_1917038 : Nat := 118140960795 + 1917038 * 2 ^ 59
def prefixEnd_1917038 : Nat := 4983230072969 + 3 ^ 40 * 1917038 * 2
def baseEnd_1917038 : Nat := 984361926933975813708709

theorem tailTrace_1917038 : CollatzResearch.WordTrace tailWord_1917038 prefixEnd_1917038 984361926933975813708709 := by
  unfold tailWord_1917038
  simp only [CollatzResearch.WordTrace]
  refine ⟨8740015003613275608692971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46613413352604136579695845 8740015003613275608692971)
  ·
    refine ⟨13110022505419913413039457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8740015003613275608692971 13110022505419913413039457)
    ·
      refine ⟨9832516879064935059779593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13110022505419913413039457 9832516879064935059779593)
      ·
        refine ⟨7374387659298701294834695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9832516879064935059779593 7374387659298701294834695)
        ·
          refine ⟨11061581488948051942252043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7374387659298701294834695 11061581488948051942252043)
          ·
            refine ⟨16592372233422077913378065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11061581488948051942252043 16592372233422077913378065)
            ·
              refine ⟨12444279175066558435033549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16592372233422077913378065 12444279175066558435033549)
              ·
                refine ⟨4666604690649959413137581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12444279175066558435033549 4666604690649959413137581)
                ·
                  refine ⟨1749976758993734779926593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4666604690649959413137581 1749976758993734779926593)
                  ·
                    refine ⟨1312482569245301084944945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1749976758993734779926593 1312482569245301084944945)
                    ·
                      refine ⟨984361926933975813708709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1312482569245301084944945 984361926933975813708709)
                      ·
                        rfl

theorem cell23_1917038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_1917038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917038 prefixEnd_1917038 := by exact prefixLift 1917038
  have htrace : WordTrace (prefixWord ++ tailWord_1917038) baseStart_1917038 baseEnd_1917038 := by
    simpa [prefixWord, tailWord_1917038, baseEnd_1917038] using wordTrace_append hprefix tailTrace_1917038
  have hstable : (prefixWord ++ tailWord_1917038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917038).length < 2 ^ (prefixWord ++ tailWord_1917038).sum := by decide
  have hdescent : baseEnd_1917038 < baseStart_1917038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917088 : List Nat := [2, 1, 1, 4, 2, 2, 3, 2, 2, 1, 3]
def baseStart_1917088 : Nat := 118140960795 + 1917088 * 2 ^ 59
def prefixEnd_1917088 : Nat := 4983230072969 + 3 ^ 40 * 1917088 * 2
def baseEnd_1917088 : Nat := 984387600966700618083479

theorem tailTrace_1917088 : CollatzResearch.WordTrace tailWord_1917088 prefixEnd_1917088 984387600966700618083479 := by
  unfold tailWord_1917088
  simp only [CollatzResearch.WordTrace]
  refine ⟨34960971839362531704431959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46614629119150042272575945 34960971839362531704431959)
  ·
    refine ⟨52441457759043797556647939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34960971839362531704431959 52441457759043797556647939)
    ·
      refine ⟨78662186638565696334971909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52441457759043797556647939 78662186638565696334971909)
      ·
        refine ⟨14749159994731068062807233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78662186638565696334971909 14749159994731068062807233)
        ·
          refine ⟨11061869996048301047105425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14749159994731068062807233 11061869996048301047105425)
          ·
            refine ⟨8296402497036225785329069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11061869996048301047105425 8296402497036225785329069)
            ·
              refine ⟨3111150936388584669498401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8296402497036225785329069 3111150936388584669498401)
              ·
                refine ⟨2333363202291438502123801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3111150936388584669498401 2333363202291438502123801)
                ·
                  refine ⟨1750022401718578876592851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2333363202291438502123801 1750022401718578876592851)
                  ·
                    refine ⟨2625033602577868314889277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1750022401718578876592851 2625033602577868314889277)
                    ·
                      refine ⟨984387600966700618083479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2625033602577868314889277 984387600966700618083479)
                      ·
                        rfl

theorem cell23_1917088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_1917088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917088 prefixEnd_1917088 := by exact prefixLift 1917088
  have htrace : WordTrace (prefixWord ++ tailWord_1917088) baseStart_1917088 baseEnd_1917088 := by
    simpa [prefixWord, tailWord_1917088, baseEnd_1917088] using wordTrace_append hprefix tailTrace_1917088
  have hstable : (prefixWord ++ tailWord_1917088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917088).length < 2 ^ (prefixWord ++ tailWord_1917088).sum := by decide
  have hdescent : baseEnd_1917088 < baseStart_1917088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917102 : List Nat := [4, 1, 4, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_1917102 : Nat := 118140960795 + 1917102 * 2 ^ 59
def prefixEnd_1917102 : Nat := 4983230072969 + 3 ^ 40 * 1917102 * 2
def baseEnd_1917102 : Nat := 984394789695863563308415

theorem tailTrace_1917102 : CollatzResearch.WordTrace tailWord_1917102 prefixEnd_1917102 984394789695863563308415 := by
  unfold tailWord_1917102
  simp only [CollatzResearch.WordTrace]
  refine ⟨8740306787584292974984195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46614969533782895866582373 8740306787584292974984195)
  ·
    refine ⟨13110460181376439462476293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8740306787584292974984195 13110460181376439462476293)
    ·
      refine ⟨2458211284008082399214305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13110460181376439462476293 2458211284008082399214305)
      ·
        refine ⟨1843658463006061799410729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2458211284008082399214305 1843658463006061799410729)
        ·
          refine ⟨1382743847254546349558047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1843658463006061799410729 1382743847254546349558047)
          ·
            refine ⟨2074115770881819524337071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382743847254546349558047 2074115770881819524337071)
            ·
              refine ⟨3111173656322729286505607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2074115770881819524337071 3111173656322729286505607)
              ·
                refine ⟨4666760484484093929758411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3111173656322729286505607 4666760484484093929758411)
                ·
                  refine ⟨7000140726726140894637617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4666760484484093929758411 7000140726726140894637617)
                  ·
                    refine ⟨5250105545044605670978213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7000140726726140894637617 5250105545044605670978213)
                    ·
                      refine ⟨984394789695863563308415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5250105545044605670978213 984394789695863563308415)
                      ·
                        rfl

theorem cell23_1917102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_1917102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917102 prefixEnd_1917102 := by exact prefixLift 1917102
  have htrace : WordTrace (prefixWord ++ tailWord_1917102) baseStart_1917102 baseEnd_1917102 := by
    simpa [prefixWord, tailWord_1917102, baseEnd_1917102] using wordTrace_append hprefix tailTrace_1917102
  have hstable : (prefixWord ++ tailWord_1917102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917102).length < 2 ^ (prefixWord ++ tailWord_1917102).sum := by decide
  have hdescent : baseEnd_1917102 < baseStart_1917102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917105 : List Nat := [1, 2, 2, 5, 3, 1, 1, 1, 1, 3, 3]
def baseStart_1917105 : Nat := 118140960795 + 1917105 * 2 ^ 59
def prefixEnd_1917105 : Nat := 4983230072969 + 3 ^ 40 * 1917105 * 2
def baseEnd_1917105 : Nat := 984396330137827051570901

theorem tailTrace_1917105 : CollatzResearch.WordTrace tailWord_1917105 prefixEnd_1917105 984396330137827051570901 := by
  unfold tailWord_1917105
  simp only [CollatzResearch.WordTrace]
  refine ⟨69922563719663475312232769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46615042479775650208155179 69922563719663475312232769)
  ·
    refine ⟨52441922789747606484174577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69922563719663475312232769 52441922789747606484174577)
    ·
      refine ⟨39331442092310704863130933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52441922789747606484174577 39331442092310704863130933)
      ·
        refine ⟨3687322696154128580918525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39331442092310704863130933 3687322696154128580918525)
        ·
          refine ⟨1382746011057798217844447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3687322696154128580918525 1382746011057798217844447)
          ·
            refine ⟨2074119016586697326766671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382746011057798217844447 2074119016586697326766671)
            ·
              refine ⟨3111178524880045990150007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2074119016586697326766671 3111178524880045990150007)
              ·
                refine ⟨4666767787320068985225011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3111178524880045990150007 4666767787320068985225011)
                ·
                  refine ⟨7000151680980103477837517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4666767787320068985225011 7000151680980103477837517)
                  ·
                    refine ⟨2625056880367538804189069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7000151680980103477837517 2625056880367538804189069)
                    ·
                      refine ⟨984396330137827051570901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2625056880367538804189069 984396330137827051570901)
                      ·
                        rfl

theorem cell23_1917105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_1917105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917105 prefixEnd_1917105 := by exact prefixLift 1917105
  have htrace : WordTrace (prefixWord ++ tailWord_1917105) baseStart_1917105 baseEnd_1917105 := by
    simpa [prefixWord, tailWord_1917105, baseEnd_1917105] using wordTrace_append hprefix tailTrace_1917105
  have hstable : (prefixWord ++ tailWord_1917105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917105).length < 2 ^ (prefixWord ++ tailWord_1917105).sum := by decide
  have hdescent : baseEnd_1917105 < baseStart_1917105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917114 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3]
def baseStart_1917114 : Nat := 118140960795 + 1917114 * 2 ^ 59
def prefixEnd_1917114 : Nat := 4983230072969 + 3 ^ 40 * 1917114 * 2
def baseEnd_1917114 : Nat := 984400951463717516358359

theorem tailTrace_1917114 : CollatzResearch.WordTrace tailWord_1917114 prefixEnd_1917114 984400951463717516358359 := by
  unfold tailWord_1917114
  simp only [CollatzResearch.WordTrace]
  refine ⟨17480722994157717462327599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46615261317753913232873597 17480722994157717462327599)
  ·
    refine ⟨26221084491236576193491399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17480722994157717462327599 26221084491236576193491399)
    ·
      refine ⟨39331626736854864290237099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26221084491236576193491399 39331626736854864290237099)
      ·
        refine ⟨58997440105282296435355649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39331626736854864290237099 58997440105282296435355649)
        ·
          refine ⟨44248080078961722326516737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58997440105282296435355649 44248080078961722326516737)
          ·
            refine ⟨33186060059221291744887553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44248080078961722326516737 33186060059221291744887553)
            ·
              refine ⟨24889545044415968808665665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33186060059221291744887553 24889545044415968808665665)
              ·
                refine ⟨18667158783311976606499249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24889545044415968808665665 18667158783311976606499249)
                ·
                  refine ⟨14000369087483982454874437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18667158783311976606499249 14000369087483982454874437)
                  ·
                    refine ⟨2625069203903246710288957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14000369087483982454874437 2625069203903246710288957)
                    ·
                      refine ⟨984400951463717516358359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2625069203903246710288957 984400951463717516358359)
                      ·
                        rfl

theorem cell23_1917114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 2, 4, 3].length) (baseStart_1917114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917114 prefixEnd_1917114 := by exact prefixLift 1917114
  have htrace : WordTrace (prefixWord ++ tailWord_1917114) baseStart_1917114 baseEnd_1917114 := by
    simpa [prefixWord, tailWord_1917114, baseEnd_1917114] using wordTrace_append hprefix tailTrace_1917114
  have hstable : (prefixWord ++ tailWord_1917114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917114).length < 2 ^ (prefixWord ++ tailWord_1917114).sum := by decide
  have hdescent : baseEnd_1917114 < baseStart_1917114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917164 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 4, 5]
def baseStart_1917164 : Nat := 118140960795 + 1917164 * 2 ^ 59
def prefixEnd_1917164 : Nat := 4983230072969 + 3 ^ 40 * 1917164 * 2
def baseEnd_1917164 : Nat := 328142208498814106911043

theorem tailTrace_1917164 : CollatzResearch.WordTrace tailWord_1917164 prefixEnd_1917164 328142208498814106911043 := by
  unfold tailWord_1917164
  simp only [CollatzResearch.WordTrace]
  refine ⟨34962357813224864194315273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46616477084299818925753697 34962357813224864194315273)
  ·
    refine ⟨26221768359918648145736455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34962357813224864194315273 26221768359918648145736455)
    ·
      refine ⟨39332652539877972218604683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26221768359918648145736455 39332652539877972218604683)
      ·
        refine ⟨58998978809816958327907025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39332652539877972218604683 58998978809816958327907025)
        ·
          refine ⟨44249234107362718745930269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58998978809816958327907025 44249234107362718745930269)
          ·
            refine ⟨16593462790261019529723851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44249234107362718745930269 16593462790261019529723851)
            ·
              refine ⟨24890194185391529294585777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16593462790261019529723851 24890194185391529294585777)
              ·
                refine ⟨18667645639043646970939333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24890194185391529294585777 18667645639043646970939333)
                ·
                  refine ⟨3500183557320683807051125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18667645639043646970939333 3500183557320683807051125)
                  ·
                    refine ⟨328142208498814106911043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3500183557320683807051125 328142208498814106911043)
                    ·
                      rfl

theorem cell23_1917164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_1917164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917164 prefixEnd_1917164 := by exact prefixLift 1917164
  have htrace : WordTrace (prefixWord ++ tailWord_1917164) baseStart_1917164 baseEnd_1917164 := by
    simpa [prefixWord, tailWord_1917164, baseEnd_1917164] using wordTrace_append hprefix tailTrace_1917164
  have hstable : (prefixWord ++ tailWord_1917164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917164).length < 2 ^ (prefixWord ++ tailWord_1917164).sum := by decide
  have hdescent : baseEnd_1917164 < baseStart_1917164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917184 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 4]
def baseStart_1917184 : Nat := 118140960795 + 1917184 * 2 ^ 59
def prefixEnd_1917184 : Nat := 4983230072969 + 3 ^ 40 * 1917184 * 2
def baseEnd_1917184 : Nat := 984436895109532242483037

theorem tailTrace_1917184 : CollatzResearch.WordTrace tailWord_1917184 prefixEnd_1917184 984436895109532242483037 := by
  unfold tailWord_1917184
  simp only [CollatzResearch.WordTrace]
  refine ⟨34962722543188635902179303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46616963390918181202905737 34962722543188635902179303)
  ·
    refine ⟨52444083814782953853268955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34962722543188635902179303 52444083814782953853268955)
    ·
      refine ⟨78666125722174430779903433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52444083814782953853268955 78666125722174430779903433)
      ·
        refine ⟨58999594291630823084927575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78666125722174430779903433 58999594291630823084927575)
        ·
          refine ⟨88499391437446234627391363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58999594291630823084927575 88499391437446234627391363)
          ·
            refine ⟨132749087156169351941087045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88499391437446234627391363 132749087156169351941087045)
            ·
              refine ⟨24890453841781753488953821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132749087156169351941087045 24890453841781753488953821)
              ·
                refine ⟨9333920190668157558357683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24890453841781753488953821 9333920190668157558357683)
                ·
                  refine ⟨14000880286002236337536525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9333920190668157558357683 14000880286002236337536525)
                  ·
                    refine ⟨5250330107250838626576197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14000880286002236337536525 5250330107250838626576197)
                    ·
                      refine ⟨984436895109532242483037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5250330107250838626576197 984436895109532242483037)
                      ·
                        rfl

theorem cell23_1917184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_1917184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917184 prefixEnd_1917184 := by exact prefixLift 1917184
  have htrace : WordTrace (prefixWord ++ tailWord_1917184) baseStart_1917184 baseEnd_1917184 := by
    simpa [prefixWord, tailWord_1917184, baseEnd_1917184] using wordTrace_append hprefix tailTrace_1917184
  have hstable : (prefixWord ++ tailWord_1917184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917184).length < 2 ^ (prefixWord ++ tailWord_1917184).sum := by decide
  have hdescent : baseEnd_1917184 < baseStart_1917184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917201 : List Nat := [1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 4]
def baseStart_1917201 : Nat := 118140960795 + 1917201 * 2 ^ 59
def prefixEnd_1917201 : Nat := 4983230072969 + 3 ^ 40 * 1917201 * 2
def baseEnd_1917201 : Nat := 984445624280658675970459

theorem tailTrace_1917201 : CollatzResearch.WordTrace tailWord_1917201 prefixEnd_1917201 984445624280658675970459 := by
  unfold tailWord_1917201
  simp only [CollatzResearch.WordTrace]
  refine ⟨69926065127315683707727457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46617376751543789138484971 69926065127315683707727457)
  ·
    refine ⟨52444548845486762780795593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69926065127315683707727457 52444548845486762780795593)
    ·
      refine ⟨39333411634115072085596695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52444548845486762780795593 39333411634115072085596695)
      ·
        refine ⟨59000117451172608128395043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39333411634115072085596695 59000117451172608128395043)
        ·
          refine ⟨88500176176758912192592565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59000117451172608128395043 88500176176758912192592565)
          ·
            refine ⟨8296891516571148018055553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88500176176758912192592565 8296891516571148018055553)
            ·
              refine ⟨6222668637428361013541665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8296891516571148018055553 6222668637428361013541665)
              ·
                refine ⟨4667001478071270760156249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6222668637428361013541665 4667001478071270760156249)
                ·
                  refine ⟨3500251108553453070117187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4667001478071270760156249 3500251108553453070117187)
                  ·
                    refine ⟨5250376662830179605175781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3500251108553453070117187 5250376662830179605175781)
                    ·
                      refine ⟨984445624280658675970459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5250376662830179605175781 984445624280658675970459)
                      ·
                        rfl

theorem cell23_1917201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_1917201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917201 prefixEnd_1917201 := by exact prefixLift 1917201
  have htrace : WordTrace (prefixWord ++ tailWord_1917201) baseStart_1917201 baseEnd_1917201 := by
    simpa [prefixWord, tailWord_1917201, baseEnd_1917201] using wordTrace_append hprefix tailTrace_1917201
  have hstable : (prefixWord ++ tailWord_1917201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917201).length < 2 ^ (prefixWord ++ tailWord_1917201).sum := by decide
  have hdescent : baseEnd_1917201 < baseStart_1917201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917218 : List Nat := [3, 3, 1, 1, 3, 1, 1, 1, 1, 6, 2]
def baseStart_1917218 : Nat := 118140960795 + 1917218 * 2 ^ 59
def prefixEnd_1917218 : Nat := 4983230072969 + 3 ^ 40 * 1917218 * 2
def baseEnd_1917218 : Nat := 984454353451785109457881

theorem tailTrace_1917218 : CollatzResearch.WordTrace tailWord_1917218 prefixEnd_1917218 984454353451785109457881 := by
  unfold tailWord_1917218
  simp only [CollatzResearch.WordTrace]
  refine ⟨17481671292063523902774077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46617790112169397074064205 17481671292063523902774077)
  ·
    refine ⟨6555626734523821463540279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17481671292063523902774077 6555626734523821463540279)
    ·
      refine ⟨9833440101785732195310419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6555626734523821463540279 9833440101785732195310419)
      ·
        refine ⟨14750160152678598292965629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9833440101785732195310419 14750160152678598292965629)
        ·
          refine ⟨5531310057254474359862111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14750160152678598292965629 5531310057254474359862111)
          ·
            refine ⟨8296965085881711539793167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5531310057254474359862111 8296965085881711539793167)
            ·
              refine ⟨12445447628822567309689751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8296965085881711539793167 12445447628822567309689751)
              ·
                refine ⟨18668171443233850964534627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12445447628822567309689751 18668171443233850964534627)
                ·
                  refine ⟨28002257164850776446801941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18668171443233850964534627 28002257164850776446801941)
                  ·
                    refine ⟨1312605804602380145943841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28002257164850776446801941 1312605804602380145943841)
                    ·
                      refine ⟨984454353451785109457881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1312605804602380145943841 984454353451785109457881)
                      ·
                        rfl

theorem cell23_1917218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_1917218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917218 prefixEnd_1917218 := by exact prefixLift 1917218
  have htrace : WordTrace (prefixWord ++ tailWord_1917218) baseStart_1917218 baseEnd_1917218 := by
    simpa [prefixWord, tailWord_1917218, baseEnd_1917218] using wordTrace_append hprefix tailTrace_1917218
  have hstable : (prefixWord ++ tailWord_1917218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917218).length < 2 ^ (prefixWord ++ tailWord_1917218).sum := by decide
  have hdescent : baseEnd_1917218 < baseStart_1917218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917288 : List Nat := [2, 1, 4, 2, 2, 1, 1, 4, 1, 5]
def baseStart_1917288 : Nat := 118140960795 + 1917288 * 2 ^ 59
def prefixEnd_1917288 : Nat := 4983230072969 + 3 ^ 40 * 1917288 * 2
def baseEnd_1917288 : Nat := 328163432365866611860853

theorem tailTrace_1917288 : CollatzResearch.WordTrace tailWord_1917288 prefixEnd_1917288 328163432365866611860853 := by
  unfold tailWord_1917288
  simp only [CollatzResearch.WordTrace]
  refine ⟨34964619139000248783072259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46619492185333665044096345 34964619139000248783072259)
  ·
    refine ⟨52446928708500373174608389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34964619139000248783072259 52446928708500373174608389)
    ·
      refine ⟨9833799132843819970239073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52446928708500373174608389 9833799132843819970239073)
      ·
        refine ⟨7375349349632864977679305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9833799132843819970239073 7375349349632864977679305)
        ·
          refine ⟨5531512012224648733259479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7375349349632864977679305 5531512012224648733259479)
          ·
            refine ⟨8297268018336973099889219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5531512012224648733259479 8297268018336973099889219)
            ·
              refine ⟨12445902027505459649833829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8297268018336973099889219 12445902027505459649833829)
              ·
                refine ⟨2333606630157273684343843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12445902027505459649833829 2333606630157273684343843)
                ·
                  refine ⟨3500409945235910526515765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2333606630157273684343843 3500409945235910526515765)
                  ·
                    refine ⟨328163432365866611860853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3500409945235910526515765 328163432365866611860853)
                    ·
                      rfl

theorem cell23_1917288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_1917288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917288 prefixEnd_1917288 := by exact prefixLift 1917288
  have htrace : WordTrace (prefixWord ++ tailWord_1917288) baseStart_1917288 baseEnd_1917288 := by
    simpa [prefixWord, tailWord_1917288, baseEnd_1917288] using wordTrace_append hprefix tailTrace_1917288
  have hstable : (prefixWord ++ tailWord_1917288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917288).length < 2 ^ (prefixWord ++ tailWord_1917288).sum := by decide
  have hdescent : baseEnd_1917288 < baseStart_1917288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917321 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 1, 1, 6]
def baseStart_1917321 : Nat := 118140960795 + 1917321 * 2 ^ 59
def prefixEnd_1917321 : Nat := 4983230072969 + 3 ^ 40 * 1917321 * 2
def baseEnd_1917321 : Nat := 984507241959198206469907

theorem tailTrace_1917321 : CollatzResearch.WordTrace tailWord_1917321 prefixEnd_1917321 984507241959198206469907 := by
  unfold tailWord_1917321
  simp only [CollatzResearch.WordTrace]
  refine ⟨69930441886880944202095817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46620294591253962801397211 69930441886880944202095817)
  ·
    refine ⟨52447831415160708151571863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69930441886880944202095817 52447831415160708151571863)
    ·
      refine ⟨78671747122741062227357795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52447831415160708151571863 78671747122741062227357795)
      ·
        refine ⟨118007620684111593341036693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78671747122741062227357795 118007620684111593341036693)
        ·
          refine ⟨5531607219567730937861095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118007620684111593341036693 5531607219567730937861095)
          ·
            refine ⟨8297410829351596406791643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5531607219567730937861095 8297410829351596406791643)
            ·
              refine ⟨12446116244027394610187465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8297410829351596406791643 12446116244027394610187465)
              ·
                refine ⟨9334587183020545957640599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12446116244027394610187465 9334587183020545957640599)
                ·
                  refine ⟨14001880774530818936460899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9334587183020545957640599 14001880774530818936460899)
                  ·
                    refine ⟨21002821161796228404691349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14001880774530818936460899 21002821161796228404691349)
                    ·
                      refine ⟨984507241959198206469907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21002821161796228404691349 984507241959198206469907)
                      ·
                        rfl

theorem cell23_1917321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 1, 6].length) (baseStart_1917321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917321 prefixEnd_1917321 := by exact prefixLift 1917321
  have htrace : WordTrace (prefixWord ++ tailWord_1917321) baseStart_1917321 baseEnd_1917321 := by
    simpa [prefixWord, tailWord_1917321, baseEnd_1917321] using wordTrace_append hprefix tailTrace_1917321
  have hstable : (prefixWord ++ tailWord_1917321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917321).length < 2 ^ (prefixWord ++ tailWord_1917321).sum := by decide
  have hdescent : baseEnd_1917321 < baseStart_1917321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917335 : List Nat := [1, 1, 3, 3, 1, 1, 6, 1, 2, 4]
def baseStart_1917335 : Nat := 118140960795 + 1917335 * 2 ^ 59
def prefixEnd_1917335 : Nat := 4983230072969 + 3 ^ 40 * 1917335 * 2
def baseEnd_1917335 : Nat := 328171476896120383898281

theorem tailTrace_1917335 : CollatzResearch.WordTrace tailWord_1917335 prefixEnd_1917335 328171476896120383898281 := by
  unfold tailWord_1917335
  simp only [CollatzResearch.WordTrace]
  refine ⟨69930952508830224593105459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46620635005886816395403639 69930952508830224593105459)
  ·
    refine ⟨104896428763245336889658189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69930952508830224593105459 104896428763245336889658189)
    ·
      refine ⟨39336160786217001333621821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104896428763245336889658189 39336160786217001333621821)
      ·
        refine ⟨14751060294831375500108183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39336160786217001333621821 14751060294831375500108183)
        ·
          refine ⟨22126590442247063250162275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14751060294831375500108183 22126590442247063250162275)
          ·
            refine ⟨33189885663370594875243413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22126590442247063250162275 33189885663370594875243413)
            ·
              refine ⟨1555775890470496634777035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 33189885663370594875243413 1555775890470496634777035)
              ·
                refine ⟨2333663835705744952165553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1555775890470496634777035 2333663835705744952165553)
                ·
                  refine ⟨1750247876779308714124165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2333663835705744952165553 1750247876779308714124165)
                  ·
                    refine ⟨328171476896120383898281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1750247876779308714124165 328171476896120383898281)
                    ·
                      rfl

theorem cell23_1917335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 2, 4].length) (baseStart_1917335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917335 prefixEnd_1917335 := by exact prefixLift 1917335
  have htrace : WordTrace (prefixWord ++ tailWord_1917335) baseStart_1917335 baseEnd_1917335 := by
    simpa [prefixWord, tailWord_1917335, baseEnd_1917335] using wordTrace_append hprefix tailTrace_1917335
  have hstable : (prefixWord ++ tailWord_1917335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917335).length < 2 ^ (prefixWord ++ tailWord_1917335).sum := by decide
  have hdescent : baseEnd_1917335 < baseStart_1917335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917342 : List Nat := [4, 3, 1, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_1917342 : Nat := 118140960795 + 1917342 * 2 ^ 59
def prefixEnd_1917342 : Nat := 4983230072969 + 3 ^ 40 * 1917342 * 2
def baseEnd_1917342 : Nat := 984518025052942624307311

theorem tailTrace_1917342 : CollatzResearch.WordTrace tailWord_1917342 prefixEnd_1917342 984518025052942624307311 := by
  unfold tailWord_1917342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8741400977475608098576285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46620805213203243192406853 8741400977475608098576285)
  ·
    refine ⟨3278025366553353036966107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8741400977475608098576285 3278025366553353036966107)
    ·
      refine ⟨4917038049830029555449161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3278025366553353036966107 4917038049830029555449161)
      ·
        refine ⟨3687778537372522166586871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4917038049830029555449161 3687778537372522166586871)
        ·
          refine ⟨5531667806058783249880307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3687778537372522166586871 5531667806058783249880307)
          ·
            refine ⟨8297501709088174874820461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5531667806058783249880307 8297501709088174874820461)
            ·
              refine ⟨3111563140908065578057673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8297501709088174874820461 3111563140908065578057673)
              ·
                refine ⟨2333672355681049183543255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3111563140908065578057673 2333672355681049183543255)
                ·
                  refine ⟨3500508533521573775314883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2333672355681049183543255 3500508533521573775314883)
                  ·
                    refine ⟨5250762800282360662972325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3500508533521573775314883 5250762800282360662972325)
                    ·
                      refine ⟨984518025052942624307311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5250762800282360662972325 984518025052942624307311)
                      ·
                        rfl

theorem cell23_1917342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_1917342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917342 prefixEnd_1917342 := by exact prefixLift 1917342
  have htrace : WordTrace (prefixWord ++ tailWord_1917342) baseStart_1917342 baseEnd_1917342 := by
    simpa [prefixWord, tailWord_1917342, baseEnd_1917342] using wordTrace_append hprefix tailTrace_1917342
  have hstable : (prefixWord ++ tailWord_1917342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917342).length < 2 ^ (prefixWord ++ tailWord_1917342).sum := by decide
  have hdescent : baseEnd_1917342 < baseStart_1917342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917415 : List Nat := [1, 1, 5, 2, 1, 1, 1, 4, 1, 4, 2]
def baseStart_1917415 : Nat := 118140960795 + 1917415 * 2 ^ 59
def prefixEnd_1917415 : Nat := 4983230072969 + 3 ^ 40 * 1917415 * 2
def baseEnd_1917415 : Nat := 984555509140720838694475

theorem tailTrace_1917415 : CollatzResearch.WordTrace tailWord_1917415 prefixEnd_1917415 984555509140720838694475 := by
  unfold tailWord_1917415
  simp only [CollatzResearch.WordTrace]
  refine ⟨69933870348540398256017699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46622580232360265504011799 69933870348540398256017699)
  ·
    refine ⟨104900805522810597384026549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69933870348540398256017699 104900805522810597384026549)
    ·
      refine ⟨9834450517763493504752489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 104900805522810597384026549 9834450517763493504752489)
      ·
        refine ⟨7375837888322620128564367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9834450517763493504752489 7375837888322620128564367)
        ·
          refine ⟨11063756832483930192846551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7375837888322620128564367 11063756832483930192846551)
          ·
            refine ⟨16595635248725895289269827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11063756832483930192846551 16595635248725895289269827)
            ·
              refine ⟨24893452873088842933904741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16595635248725895289269827 24893452873088842933904741)
              ·
                refine ⟨4667522413704158050107139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24893452873088842933904741 4667522413704158050107139)
                ·
                  refine ⟨7001283620556237075160709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4667522413704158050107139 7001283620556237075160709)
                  ·
                    refine ⟨1312740678854294451592633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7001283620556237075160709 1312740678854294451592633)
                    ·
                      refine ⟨984555509140720838694475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1312740678854294451592633 984555509140720838694475)
                      ·
                        rfl

theorem cell23_1917415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_1917415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917415 prefixEnd_1917415 := by exact prefixLift 1917415
  have htrace : WordTrace (prefixWord ++ tailWord_1917415) baseStart_1917415 baseEnd_1917415 := by
    simpa [prefixWord, tailWord_1917415, baseEnd_1917415] using wordTrace_append hprefix tailTrace_1917415
  have hstable : (prefixWord ++ tailWord_1917415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917415).length < 2 ^ (prefixWord ++ tailWord_1917415).sum := by decide
  have hdescent : baseEnd_1917415 < baseStart_1917415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917426 : List Nat := [3, 2, 1, 4, 3, 1, 1, 2, 2, 1, 3]
def baseStart_1917426 : Nat := 118140960795 + 1917426 * 2 ^ 59
def prefixEnd_1917426 : Nat := 4983230072969 + 3 ^ 40 * 1917426 * 2
def baseEnd_1917426 : Nat := 984561157427920295656925

theorem tailTrace_1917426 : CollatzResearch.WordTrace tailWord_1917426 prefixEnd_1917426 984561157427920295656925 := by
  unfold tailWord_1917426
  simp only [CollatzResearch.WordTrace]
  refine ⟨17483567887875136783667033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46622847701000364756445421 17483567887875136783667033)
  ·
    refine ⟨13112675915906352587750275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17483567887875136783667033 13112675915906352587750275)
    ·
      refine ⟨19669013873859528881625413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13112675915906352587750275 19669013873859528881625413)
      ·
        refine ⟨3687940101348661665304765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19669013873859528881625413 3687940101348661665304765)
        ·
          refine ⟨1382977538005748124489287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3687940101348661665304765 1382977538005748124489287)
          ·
            refine ⟨2074466307008622186733931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1382977538005748124489287 2074466307008622186733931)
            ·
              refine ⟨3111699460512933280100897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2074466307008622186733931 3111699460512933280100897)
              ·
                refine ⟨2333774595384699960075673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3111699460512933280100897 2333774595384699960075673)
                ·
                  refine ⟨1750330946538524970056755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2333774595384699960075673 1750330946538524970056755)
                  ·
                    refine ⟨2625496419807787455085133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1750330946538524970056755 2625496419807787455085133)
                    ·
                      refine ⟨984561157427920295656925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2625496419807787455085133 984561157427920295656925)
                      ·
                        rfl

theorem cell23_1917426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_1917426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917426 prefixEnd_1917426 := by exact prefixLift 1917426
  have htrace : WordTrace (prefixWord ++ tailWord_1917426) baseStart_1917426 baseEnd_1917426 := by
    simpa [prefixWord, tailWord_1917426, baseEnd_1917426] using wordTrace_append hprefix tailTrace_1917426
  have hstable : (prefixWord ++ tailWord_1917426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917426).length < 2 ^ (prefixWord ++ tailWord_1917426).sum := by decide
  have hdescent : baseEnd_1917426 < baseStart_1917426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917468 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 1, 7]
def baseStart_1917468 : Nat := 118140960795 + 1917468 * 2 ^ 59
def prefixEnd_1917468 : Nat := 4983230072969 + 3 ^ 40 * 1917468 * 2
def baseEnd_1917468 : Nat := 328194241205136377110577

theorem tailTrace_1917468 : CollatzResearch.WordTrace tailWord_1917468 prefixEnd_1917468 328194241205136377110577 := by
  unfold tailWord_1917468
  simp only [CollatzResearch.WordTrace]
  refine ⟨34967901708674194153848529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46623868944898925538464705 34967901708674194153848529)
  ·
    refine ⟨26225926281505645615386397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34967901708674194153848529 26225926281505645615386397)
    ·
      refine ⟨9834722355564617105769899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26225926281505645615386397 9834722355564617105769899)
      ·
        refine ⟨14752083533346925658654849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9834722355564617105769899 14752083533346925658654849)
        ·
          refine ⟨11064062650010194243991137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14752083533346925658654849 11064062650010194243991137)
          ·
            refine ⟨8298046987507645682993353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11064062650010194243991137 8298046987507645682993353)
            ·
              refine ⟨6223535240630734262245015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8298046987507645682993353 6223535240630734262245015)
              ·
                refine ⟨9335302860946101393367523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6223535240630734262245015 9335302860946101393367523)
                ·
                  refine ⟨14002954291419152090051285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9335302860946101393367523 14002954291419152090051285)
                  ·
                    refine ⟨328194241205136377110577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14002954291419152090051285 328194241205136377110577)
                    ·
                      rfl

theorem cell23_1917468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_1917468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917468 prefixEnd_1917468 := by exact prefixLift 1917468
  have htrace : WordTrace (prefixWord ++ tailWord_1917468) baseStart_1917468 baseEnd_1917468 := by
    simpa [prefixWord, tailWord_1917468, baseEnd_1917468] using wordTrace_append hprefix tailTrace_1917468
  have hstable : (prefixWord ++ tailWord_1917468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917468).length < 2 ^ (prefixWord ++ tailWord_1917468).sum := by decide
  have hdescent : baseEnd_1917468 < baseStart_1917468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917488 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 4]
def baseStart_1917488 : Nat := 118140960795 + 1917488 * 2 ^ 59
def prefixEnd_1917488 : Nat := 4983230072969 + 3 ^ 40 * 1917488 * 2
def baseEnd_1917488 : Nat := 984592993228499053081639

theorem tailTrace_1917488 : CollatzResearch.WordTrace tailWord_1917488 prefixEnd_1917488 984592993228499053081639 := by
  unfold tailWord_1917488
  simp only [CollatzResearch.WordTrace]
  refine ⟨34968266438637965861712559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46624355251517287815616745 34968266438637965861712559)
  ·
    refine ⟨52452399657956948792568839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34968266438637965861712559 52452399657956948792568839)
    ·
      refine ⟨78678599486935423188853259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52452399657956948792568839 78678599486935423188853259)
      ·
        refine ⟨118017899230403134783279889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78678599486935423188853259 118017899230403134783279889)
        ·
          refine ⟨88513424422802351087459917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118017899230403134783279889 88513424422802351087459917)
          ·
            refine ⟨33192534158550881657797469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88513424422802351087459917 33192534158550881657797469)
            ·
              refine ⟨12447200309456580621674051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33192534158550881657797469 12447200309456580621674051)
              ·
                refine ⟨18670800464184870932511077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12447200309456580621674051 18670800464184870932511077)
                ·
                  refine ⟨3500775087034663299845827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18670800464184870932511077 3500775087034663299845827)
                  ·
                    refine ⟨5251162630551994949768741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3500775087034663299845827 5251162630551994949768741)
                    ·
                      refine ⟨984592993228499053081639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5251162630551994949768741 984592993228499053081639)
                      ·
                        rfl

theorem cell23_1917488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 4].length) (baseStart_1917488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917488 prefixEnd_1917488 := by exact prefixLift 1917488
  have htrace : WordTrace (prefixWord ++ tailWord_1917488) baseStart_1917488 baseEnd_1917488 := by
    simpa [prefixWord, tailWord_1917488, baseEnd_1917488] using wordTrace_append hprefix tailTrace_1917488
  have hstable : (prefixWord ++ tailWord_1917488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917488).length < 2 ^ (prefixWord ++ tailWord_1917488).sum := by decide
  have hdescent : baseEnd_1917488 < baseStart_1917488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917518 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_1917518 : Nat := 118140960795 + 1917518 * 2 ^ 59
def prefixEnd_1917518 : Nat := 4983230072969 + 3 ^ 40 * 1917518 * 2
def baseEnd_1917518 : Nat := 984608397648133935706501

theorem tailTrace_1917518 : CollatzResearch.WordTrace tailWord_1917518 prefixEnd_1917518 984608397648133935706501 := by
  unfold tailWord_1917518
  simp only [CollatzResearch.WordTrace]
  refine ⟨8742203383395905855877151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46625084711444831231344805 8742203383395905855877151)
  ·
    refine ⟨13113305075093858783815727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8742203383395905855877151 13113305075093858783815727)
    ·
      refine ⟨19669957612640788175723591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13113305075093858783815727 19669957612640788175723591)
      ·
        refine ⟨29504936418961182263585387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19669957612640788175723591 29504936418961182263585387)
        ·
          refine ⟨44257404628441773395378081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29504936418961182263585387 44257404628441773395378081)
          ·
            refine ⟨33193053471331330046533561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44257404628441773395378081 33193053471331330046533561)
            ·
              refine ⟨24894790103498497534900171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33193053471331330046533561 24894790103498497534900171)
              ·
                refine ⟨37342185155247746302350257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24894790103498497534900171 37342185155247746302350257)
                ·
                  refine ⟨28006638866435809726762693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37342185155247746302350257 28006638866435809726762693)
                  ·
                    refine ⟨5251244787456714323768005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28006638866435809726762693 5251244787456714323768005)
                    ·
                      refine ⟨984608397648133935706501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5251244787456714323768005 984608397648133935706501)
                      ·
                        rfl

theorem cell23_1917518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_1917518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917518 prefixEnd_1917518 := by exact prefixLift 1917518
  have htrace : WordTrace (prefixWord ++ tailWord_1917518) baseStart_1917518 baseEnd_1917518 := by
    simpa [prefixWord, tailWord_1917518, baseEnd_1917518] using wordTrace_append hprefix tailTrace_1917518
  have hstable : (prefixWord ++ tailWord_1917518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917518).length < 2 ^ (prefixWord ++ tailWord_1917518).sum := by decide
  have hdescent : baseEnd_1917518 < baseStart_1917518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917525 : List Nat := [1, 3, 2, 2, 1, 1, 3, 3, 2, 2, 3]
def baseStart_1917525 : Nat := 118140960795 + 1917525 * 2 ^ 59
def prefixEnd_1917525 : Nat := 4983230072969 + 3 ^ 40 * 1917525 * 2
def baseEnd_1917525 : Nat := 984611992012715408318969

theorem tailTrace_1917525 : CollatzResearch.WordTrace tailWord_1917525 prefixEnd_1917525 984611992012715408318969 := by
  unfold tailWord_1917525
  simp only [CollatzResearch.WordTrace]
  refine ⟨69937882378141887042522029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46625254918761258028348019 69937882378141887042522029)
  ·
    refine ⟨26226705891803207640945761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69937882378141887042522029 26226705891803207640945761)
    ·
      refine ⟨19670029418852405730709321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26226705891803207640945761 19670029418852405730709321)
      ·
        refine ⟨14752522064139304298031991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19670029418852405730709321 14752522064139304298031991)
        ·
          refine ⟨22128783096208956447047987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14752522064139304298031991 22128783096208956447047987)
          ·
            refine ⟨33193174644313434670571981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22128783096208956447047987 33193174644313434670571981)
            ·
              refine ⟨12447440491617538001464493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33193174644313434670571981 12447440491617538001464493)
              ·
                refine ⟨4667790184356576750549185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12447440491617538001464493 4667790184356576750549185)
                ·
                  refine ⟨3500842638267432562911889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4667790184356576750549185 3500842638267432562911889)
                  ·
                    refine ⟨2625631978700574422183917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3500842638267432562911889 2625631978700574422183917)
                    ·
                      refine ⟨984611992012715408318969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2625631978700574422183917 984611992012715408318969)
                      ·
                        rfl

theorem cell23_1917525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_1917525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917525 prefixEnd_1917525 := by exact prefixLift 1917525
  have htrace : WordTrace (prefixWord ++ tailWord_1917525) baseStart_1917525 baseEnd_1917525 := by
    simpa [prefixWord, tailWord_1917525, baseEnd_1917525] using wordTrace_append hprefix tailTrace_1917525
  have hstable : (prefixWord ++ tailWord_1917525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917525).length < 2 ^ (prefixWord ++ tailWord_1917525).sum := by decide
  have hdescent : baseEnd_1917525 < baseStart_1917525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917549 : List Nat := [1, 5, 1, 1, 3, 2, 1, 4, 1, 4]
def baseStart_1917549 : Nat := 118140960795 + 1917549 * 2 ^ 59
def prefixEnd_1917549 : Nat := 4983230072969 + 3 ^ 40 * 1917549 * 2
def baseEnd_1917549 : Nat := 328208105182807771472953

theorem tailTrace_1917549 : CollatzResearch.WordTrace tailWord_1917549 prefixEnd_1917549 328208105182807771472953 := by
  unfold tailWord_1917549
  simp only [CollatzResearch.WordTrace]
  refine ⟨69938757730054939141395701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46625838486703292760930467 69938757730054939141395701)
  ·
    refine ⟨6556758537192650544505847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69938757730054939141395701 6556758537192650544505847)
    ·
      refine ⟨9835137805788975816758771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6556758537192650544505847 9835137805788975816758771)
      ·
        refine ⟨14752706708683463725138157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9835137805788975816758771 14752706708683463725138157)
        ·
          refine ⟨5532265015756298896926809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14752706708683463725138157 5532265015756298896926809)
          ·
            refine ⟨4149198761817224172695107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5532265015756298896926809 4149198761817224172695107)
            ·
              refine ⟨6223798142725836259042661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4149198761817224172695107 6223798142725836259042661)
              ·
                refine ⟨1166962151761094298570499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6223798142725836259042661 1166962151761094298570499)
                ·
                  refine ⟨1750443227641641447855749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1166962151761094298570499 1750443227641641447855749)
                  ·
                    refine ⟨328208105182807771472953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1750443227641641447855749 328208105182807771472953)
                    ·
                      rfl

theorem cell23_1917549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_1917549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917549 prefixEnd_1917549 := by exact prefixLift 1917549
  have htrace : WordTrace (prefixWord ++ tailWord_1917549) baseStart_1917549 baseEnd_1917549 := by
    simpa [prefixWord, tailWord_1917549, baseEnd_1917549] using wordTrace_append hprefix tailTrace_1917549
  have hstable : (prefixWord ++ tailWord_1917549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917549).length < 2 ^ (prefixWord ++ tailWord_1917549).sum := by decide
  have hdescent : baseEnd_1917549 < baseStart_1917549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917572 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 5, 1, 3]
def baseStart_1917572 : Nat := 118140960795 + 1917572 * 2 ^ 59
def prefixEnd_1917572 : Nat := 4983230072969 + 3 ^ 40 * 1917572 * 2
def baseEnd_1917572 : Nat := 984636125603476724431253

theorem tailTrace_1917572 : CollatzResearch.WordTrace tailWord_1917572 prefixEnd_1917572 984636125603476724431253 := by
  unfold tailWord_1917572
  simp only [CollatzResearch.WordTrace]
  refine ⟨34969798304485807034741485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46626397739314409379655313 34969798304485807034741485)
  ·
    refine ⟨13113674364182177638028057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34969798304485807034741485 13113674364182177638028057)
    ·
      refine ⟨9835255773136633228521043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13113674364182177638028057 9835255773136633228521043)
      ·
        refine ⟨14752883659704949842781565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9835255773136633228521043 14752883659704949842781565)
        ·
          refine ⟨5532331372389356191043087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14752883659704949842781565 5532331372389356191043087)
          ·
            refine ⟨8298497058584034286564631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5532331372389356191043087 8298497058584034286564631)
            ·
              refine ⟨12447745587876051429846947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8298497058584034286564631 12447745587876051429846947)
              ·
                refine ⟨18671618381814077144770421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12447745587876051429846947 18671618381814077144770421)
                ·
                  refine ⟨1750464223295069732322227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18671618381814077144770421 1750464223295069732322227)
                  ·
                    refine ⟨2625696334942604598483341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1750464223295069732322227 2625696334942604598483341)
                    ·
                      refine ⟨984636125603476724431253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2625696334942604598483341 984636125603476724431253)
                      ·
                        rfl

theorem cell23_1917572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_1917572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917572 prefixEnd_1917572 := by exact prefixLift 1917572
  have htrace : WordTrace (prefixWord ++ tailWord_1917572) baseStart_1917572 baseEnd_1917572 := by
    simpa [prefixWord, tailWord_1917572, baseEnd_1917572] using wordTrace_append hprefix tailTrace_1917572
  have hstable : (prefixWord ++ tailWord_1917572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917572).length < 2 ^ (prefixWord ++ tailWord_1917572).sum := by decide
  have hdescent : baseEnd_1917572 < baseStart_1917572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917575 : List Nat := [1, 1, 4, 2, 1, 2, 2, 4, 1, 5]
def baseStart_1917575 : Nat := 118140960795 + 1917575 * 2 ^ 59
def prefixEnd_1917575 : Nat := 4983230072969 + 3 ^ 40 * 1917575 * 2
def baseEnd_1917575 : Nat := 328212555348480070897913

theorem tailTrace_1917575 : CollatzResearch.WordTrace tailWord_1917575 prefixEnd_1917575 328212555348480070897913 := by
  unfold tailWord_1917575
  simp only [CollatzResearch.WordTrace]
  refine ⟨69939706027960745581842179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46626470685307163721228119 69939706027960745581842179)
  ·
    refine ⟨104909559041941118372763269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69939706027960745581842179 104909559041941118372763269)
    ·
      refine ⟨19670542320363959694893113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104909559041941118372763269 19670542320363959694893113)
      ·
        refine ⟨14752906740272969771169835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19670542320363959694893113 14752906740272969771169835)
        ·
          refine ⟨22129360110409454656754753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14752906740272969771169835 22129360110409454656754753)
          ·
            refine ⟨16597020082807090992566065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22129360110409454656754753 16597020082807090992566065)
            ·
              refine ⟨12447765062105318244424549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16597020082807090992566065 12447765062105318244424549)
              ·
                refine ⟨2333955949144747170829603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12447765062105318244424549 2333955949144747170829603)
                ·
                  refine ⟨3500933923717120756244405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2333955949144747170829603 3500933923717120756244405)
                  ·
                    refine ⟨328212555348480070897913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3500933923717120756244405 328212555348480070897913)
                    ·
                      rfl

theorem cell23_1917575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_1917575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917575 prefixEnd_1917575 := by exact prefixLift 1917575
  have htrace : WordTrace (prefixWord ++ tailWord_1917575) baseStart_1917575 baseEnd_1917575 := by
    simpa [prefixWord, tailWord_1917575, baseEnd_1917575] using wordTrace_append hprefix tailTrace_1917575
  have hstable : (prefixWord ++ tailWord_1917575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917575).length < 2 ^ (prefixWord ++ tailWord_1917575).sum := by decide
  have hdescent : baseEnd_1917575 < baseStart_1917575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917582 : List Nat := [4, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2]
def baseStart_1917582 : Nat := 118140960795 + 1917582 * 2 ^ 59
def prefixEnd_1917582 : Nat := 4983230072969 + 3 ^ 40 * 1917582 * 2
def baseEnd_1917582 : Nat := 984641260410021685306207

theorem tailTrace_1917582 : CollatzResearch.WordTrace tailWord_1917582 prefixEnd_1917582 984641260410021685306207 := by
  unfold tailWord_1917582
  simp only [CollatzResearch.WordTrace]
  refine ⟨8742495167366923222168375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46626640892623590518231333 8742495167366923222168375)
  ·
    refine ⟨13113742751050384833252563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8742495167366923222168375 13113742751050384833252563)
    ·
      refine ⟨19670614126575577249878845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13113742751050384833252563 19670614126575577249878845)
      ·
        refine ⟨7376480297465841468704567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19670614126575577249878845 7376480297465841468704567)
        ·
          refine ⟨11064720446198762203056851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7376480297465841468704567 11064720446198762203056851)
          ·
            refine ⟨16597080669298143304585277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11064720446198762203056851 16597080669298143304585277)
            ·
              refine ⟨6223905250986803739219479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16597080669298143304585277 6223905250986803739219479)
              ·
                refine ⟨9335857876480205608829219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6223905250986803739219479 9335857876480205608829219)
                ·
                  refine ⟨14003786814720308413243829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9335857876480205608829219 14003786814720308413243829)
                  ·
                    refine ⟨1312855013880028913741609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14003786814720308413243829 1312855013880028913741609)
                    ·
                      refine ⟨984641260410021685306207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1312855013880028913741609 984641260410021685306207)
                      ·
                        rfl

theorem cell23_1917582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_1917582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917582 prefixEnd_1917582 := by exact prefixLift 1917582
  have htrace : WordTrace (prefixWord ++ tailWord_1917582) baseStart_1917582 baseEnd_1917582 := by
    simpa [prefixWord, tailWord_1917582, baseEnd_1917582] using wordTrace_append hprefix tailTrace_1917582
  have hstable : (prefixWord ++ tailWord_1917582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917582).length < 2 ^ (prefixWord ++ tailWord_1917582).sum := by decide
  have hdescent : baseEnd_1917582 < baseStart_1917582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917615 : List Nat := [1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 5]
def baseStart_1917615 : Nat := 118140960795 + 1917615 * 2 ^ 59
def prefixEnd_1917615 : Nat := 4983230072969 + 3 ^ 40 * 1917615 * 2
def baseEnd_1917615 : Nat := 984658205271620056193555

theorem tailTrace_1917615 : CollatzResearch.WordTrace tailWord_1917615 prefixEnd_1917615 984658205271620056193555 := by
  unfold tailWord_1917615
  simp only [CollatzResearch.WordTrace]
  refine ⟨69941164947815832413298299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46627443298543888275532199 69941164947815832413298299)
  ·
    refine ⟨104911747421723748619947449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69941164947815832413298299 104911747421723748619947449)
    ·
      refine ⟨78683810566292811464960587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104911747421723748619947449 78683810566292811464960587)
      ·
        refine ⟨118025715849439217197440881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78683810566292811464960587 118025715849439217197440881)
        ·
          refine ⟨88519286887079412898080661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118025715849439217197440881 88519286887079412898080661)
          ·
            refine ⟨4149341572831847479597531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 88519286887079412898080661 4149341572831847479597531)
            ·
              refine ⟨6224012359247771219396297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4149341572831847479597531 6224012359247771219396297)
              ·
                refine ⟨4668009269435828414547223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6224012359247771219396297 4668009269435828414547223)
                ·
                  refine ⟨7002013904153742621820835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4668009269435828414547223 7002013904153742621820835)
                  ·
                    refine ⟨10503020856230613932731253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7002013904153742621820835 10503020856230613932731253)
                    ·
                      refine ⟨984658205271620056193555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10503020856230613932731253 984658205271620056193555)
                      ·
                        rfl

theorem cell23_1917615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 5].length) (baseStart_1917615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917615 prefixEnd_1917615 := by exact prefixLift 1917615
  have htrace : WordTrace (prefixWord ++ tailWord_1917615) baseStart_1917615 baseEnd_1917615 := by
    simpa [prefixWord, tailWord_1917615, baseEnd_1917615] using wordTrace_append hprefix tailTrace_1917615
  have hstable : (prefixWord ++ tailWord_1917615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917615).length < 2 ^ (prefixWord ++ tailWord_1917615).sum := by decide
  have hdescent : baseEnd_1917615 < baseStart_1917615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917618 : List Nat := [3, 2, 1, 1, 1, 2, 1, 12]
def baseStart_1917618 : Nat := 118140960795 + 1917618 * 2 ^ 59
def prefixEnd_1917618 : Nat := 4983230072969 + 3 ^ 40 * 1917618 * 2
def baseEnd_1917618 : Nat := 36468879470873464609483

theorem tailTrace_1917618 : CollatzResearch.WordTrace tailWord_1917618 prefixEnd_1917618 36468879470873464609483 := by
  unfold tailWord_1917618
  simp only [CollatzResearch.WordTrace]
  refine ⟨17485318591701240981414377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46627516244536642617105005 17485318591701240981414377)
  ·
    refine ⟨13113988943775930736060783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17485318591701240981414377 13113988943775930736060783)
    ·
      refine ⟨19670983415663896104091175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13113988943775930736060783 19670983415663896104091175)
      ·
        refine ⟨29506475123495844156136763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19670983415663896104091175 29506475123495844156136763)
        ·
          refine ⟨44259712685243766234205145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29506475123495844156136763 44259712685243766234205145)
          ·
            refine ⟨33194784513932824675653859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44259712685243766234205145 33194784513932824675653859)
            ·
              refine ⟨49792176770899237013480789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33194784513932824675653859 49792176770899237013480789)
              ·
                refine ⟨36468879470873464609483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 49792176770899237013480789 36468879470873464609483)
                ·
                  rfl

theorem cell23_1917618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 12].length) (baseStart_1917618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917618 prefixEnd_1917618 := by exact prefixLift 1917618
  have htrace : WordTrace (prefixWord ++ tailWord_1917618) baseStart_1917618 baseEnd_1917618 := by
    simpa [prefixWord, tailWord_1917618, baseEnd_1917618] using wordTrace_append hprefix tailTrace_1917618
  have hstable : (prefixWord ++ tailWord_1917618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917618).length < 2 ^ (prefixWord ++ tailWord_1917618).sum := by decide
  have hdescent : baseEnd_1917618 < baseStart_1917618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917629 : List Nat := [1, 4, 1, 2, 1, 3, 2, 2, 3, 2, 2]
def baseStart_1917629 : Nat := 118140960795 + 1917629 * 2 ^ 59
def prefixEnd_1917629 : Nat := 4983230072969 + 3 ^ 40 * 1917629 * 2
def baseEnd_1917629 : Nat := 984665394000783001418491

theorem tailTrace_1917629 : CollatzResearch.WordTrace tailWord_1917629 prefixEnd_1917629 984665394000783001418491 := by
  unfold tailWord_1917629
  simp only [CollatzResearch.WordTrace]
  refine ⟨69941675569765112804307941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46627783713176741869538627 69941675569765112804307941)
  ·
    refine ⟨13114064169330958650807739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69941675569765112804307941 13114064169330958650807739)
    ·
      refine ⟨19671096253996437976211609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13114064169330958650807739 19671096253996437976211609)
      ·
        refine ⟨14753322190497328482158707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19671096253996437976211609 14753322190497328482158707)
        ·
          refine ⟨22129983285745992723238061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14753322190497328482158707 22129983285745992723238061)
          ·
            refine ⟨8298743732154747271214273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22129983285745992723238061 8298743732154747271214273)
            ·
              refine ⟨6224057799116060453410705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8298743732154747271214273 6224057799116060453410705)
              ·
                refine ⟨4668043349337045340058029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6224057799116060453410705 4668043349337045340058029)
                ·
                  refine ⟨1750516256001392002521761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4668043349337045340058029 1750516256001392002521761)
                  ·
                    refine ⟨1312887192001044001891321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1750516256001392002521761 1312887192001044001891321)
                    ·
                      refine ⟨984665394000783001418491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1312887192001044001891321 984665394000783001418491)
                      ·
                        rfl

theorem cell23_1917629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_1917629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917629 prefixEnd_1917629 := by exact prefixLift 1917629
  have htrace : WordTrace (prefixWord ++ tailWord_1917629) baseStart_1917629 baseEnd_1917629 := by
    simpa [prefixWord, tailWord_1917629, baseEnd_1917629] using wordTrace_append hprefix tailTrace_1917629
  have hstable : (prefixWord ++ tailWord_1917629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917629).length < 2 ^ (prefixWord ++ tailWord_1917629).sum := by decide
  have hdescent : baseEnd_1917629 < baseStart_1917629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917632 : List Nat := [2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 3]
def baseStart_1917632 : Nat := 118140960795 + 1917632 * 2 ^ 59
def prefixEnd_1917632 : Nat := 4983230072969 + 3 ^ 40 * 1917632 * 2
def baseEnd_1917632 : Nat := 984666934442746489680977

theorem tailTrace_1917632 : CollatzResearch.WordTrace tailWord_1917632 prefixEnd_1917632 984666934442746489680977 := by
  unfold tailWord_1917632
  simp only [CollatzResearch.WordTrace]
  refine ⟨34970892494377122158333575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46627856659169496211111433 34970892494377122158333575)
  ·
    refine ⟨52456338741565683237500363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34970892494377122158333575 52456338741565683237500363)
    ·
      refine ⟨78684508112348524856250545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52456338741565683237500363 78684508112348524856250545)
      ·
        refine ⟨59013381084261393642187909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78684508112348524856250545 59013381084261393642187909)
        ·
          refine ⟨11065008953299011307910233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59013381084261393642187909 11065008953299011307910233)
          ·
            refine ⟨8298756714974258480932675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11065008953299011307910233 8298756714974258480932675)
            ·
              refine ⟨12448135072461387721399013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8298756714974258480932675 12448135072461387721399013)
              ·
                refine ⟨2334025326086510197762315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12448135072461387721399013 2334025326086510197762315)
                ·
                  refine ⟨3501037989129765296643473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334025326086510197762315 3501037989129765296643473)
                  ·
                    refine ⟨2625778491847323972482605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3501037989129765296643473 2625778491847323972482605)
                    ·
                      refine ⟨984666934442746489680977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2625778491847323972482605 984666934442746489680977)
                      ·
                        rfl

theorem cell23_1917632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 1, 2, 3].length) (baseStart_1917632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917632 prefixEnd_1917632 := by exact prefixLift 1917632
  have htrace : WordTrace (prefixWord ++ tailWord_1917632) baseStart_1917632 baseEnd_1917632 := by
    simpa [prefixWord, tailWord_1917632, baseEnd_1917632] using wordTrace_append hprefix tailTrace_1917632
  have hstable : (prefixWord ++ tailWord_1917632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917632).length < 2 ^ (prefixWord ++ tailWord_1917632).sum := by decide
  have hdescent : baseEnd_1917632 < baseStart_1917632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917652 : List Nat := [2, 4, 1, 3, 2, 2, 9]
def baseStart_1917652 : Nat := 118140960795 + 1917652 * 2 ^ 59
def prefixEnd_1917652 : Nat := 4983230072969 + 3 ^ 40 * 1917652 * 2
def baseEnd_1917652 : Nat := 12156508692047363104085

theorem tailTrace_1917652 : CollatzResearch.WordTrace tailWord_1917652 prefixEnd_1917652 12156508692047363104085 := by
  unfold tailWord_1917652
  simp only [CollatzResearch.WordTrace]
  refine ⟨34971257224340893866197605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46628342965787858488263473 34971257224340893866197605)
  ·
    refine ⟨6557110729563917599912051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34971257224340893866197605 6557110729563917599912051)
    ·
      refine ⟨9835666094345876399868077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6557110729563917599912051 9835666094345876399868077)
      ·
        refine ⟨3688374785379703649950529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9835666094345876399868077 3688374785379703649950529)
        ·
          refine ⟨2766281089034777737462897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3688374785379703649950529 2766281089034777737462897)
          ·
            refine ⟨2074710816776083303097173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2766281089034777737462897 2074710816776083303097173)
            ·
              refine ⟨12156508692047363104085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2074710816776083303097173 12156508692047363104085)
              ·
                rfl

theorem cell23_1917652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 9].length) (baseStart_1917652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917652 prefixEnd_1917652 := by exact prefixLift 1917652
  have htrace : WordTrace (prefixWord ++ tailWord_1917652) baseStart_1917652 baseEnd_1917652 := by
    simpa [prefixWord, tailWord_1917652, baseEnd_1917652] using wordTrace_append hprefix tailTrace_1917652
  have hstable : (prefixWord ++ tailWord_1917652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917652).length < 2 ^ (prefixWord ++ tailWord_1917652).sum := by decide
  have hdescent : baseEnd_1917652 < baseStart_1917652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917663 : List Nat := [1, 1, 2, 3, 2, 4, 3, 2, 1, 2, 2]
def baseStart_1917663 : Nat := 118140960795 + 1917663 * 2 ^ 59
def prefixEnd_1917663 : Nat := 4983230072969 + 3 ^ 40 * 1917663 * 2
def baseEnd_1917663 : Nat := 984682852343035868393335

theorem tailTrace_1917663 : CollatzResearch.WordTrace tailWord_1917663 prefixEnd_1917663 984682852343035868393335 := by
  unfold tailWord_1917663
  simp only [CollatzResearch.WordTrace]
  refine ⟨69942915651641936611045643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46628610434427957740697095 69942915651641936611045643)
  ·
    refine ⟨104914373477462904916568465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69942915651641936611045643 104914373477462904916568465)
    ·
      refine ⟨78685780108097178687426349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104914373477462904916568465 78685780108097178687426349)
      ·
        refine ⟨29507167540536442007784881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78685780108097178687426349 29507167540536442007784881)
        ·
          refine ⟨22130375655402331505838661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29507167540536442007784881 22130375655402331505838661)
          ·
            refine ⟨4149445435387937157344749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22130375655402331505838661 4149445435387937157344749)
            ·
              refine ⟨1556042038270476434004281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4149445435387937157344749 1556042038270476434004281)
              ·
                refine ⟨1167031528702857325503211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1556042038270476434004281 1167031528702857325503211)
                ·
                  refine ⟨1750547293054285988254817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1167031528702857325503211 1750547293054285988254817)
                  ·
                    refine ⟨1312910469790714491191113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1750547293054285988254817 1312910469790714491191113)
                    ·
                      refine ⟨984682852343035868393335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1312910469790714491191113 984682852343035868393335)
                      ·
                        rfl

theorem cell23_1917663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 2, 1, 2, 2].length) (baseStart_1917663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917663 prefixEnd_1917663 := by exact prefixLift 1917663
  have htrace : WordTrace (prefixWord ++ tailWord_1917663) baseStart_1917663 baseEnd_1917663 := by
    simpa [prefixWord, tailWord_1917663, baseEnd_1917663] using wordTrace_append hprefix tailTrace_1917663
  have hstable : (prefixWord ++ tailWord_1917663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917663).length < 2 ^ (prefixWord ++ tailWord_1917663).sum := by decide
  have hdescent : baseEnd_1917663 < baseStart_1917663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917679 : List Nat := [1, 1, 2, 1, 5, 3, 1, 3, 2, 1, 3]
def baseStart_1917679 : Nat := 118140960795 + 1917679 * 2 ^ 59
def prefixEnd_1917679 : Nat := 4983230072969 + 3 ^ 40 * 1917679 * 2
def baseEnd_1917679 : Nat := 984691068033507805793261

theorem tailTrace_1917679 : CollatzResearch.WordTrace tailWord_1917679 prefixEnd_1917679 984691068033507805793261 := by
  unfold tailWord_1917679
  simp only [CollatzResearch.WordTrace]
  refine ⟨69943499219583971343628091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46628999479722647562418727 69943499219583971343628091)
  ·
    refine ⟨104915248829375957015442137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69943499219583971343628091 104915248829375957015442137)
    ·
      refine ⟨78686436622031967761581603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104915248829375957015442137 78686436622031967761581603)
      ·
        refine ⟨118029654933047951642372405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78686436622031967761581603 118029654933047951642372405)
        ·
          refine ⟨11065280149973245466472413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118029654933047951642372405 11065280149973245466472413)
          ·
            refine ⟨4149480056239967049927155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11065280149973245466472413 4149480056239967049927155)
            ·
              refine ⟨6224220084359950574890733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4149480056239967049927155 6224220084359950574890733)
              ·
                refine ⟨2334082531634981465584025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6224220084359950574890733 2334082531634981465584025)
                ·
                  refine ⟨1750561898726236099188019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2334082531634981465584025 1750561898726236099188019)
                  ·
                    refine ⟨2625842848089354148782029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1750561898726236099188019 2625842848089354148782029)
                    ·
                      refine ⟨984691068033507805793261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2625842848089354148782029 984691068033507805793261)
                      ·
                        rfl

theorem cell23_1917679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 1, 3].length) (baseStart_1917679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917679 prefixEnd_1917679 := by exact prefixLift 1917679
  have htrace : WordTrace (prefixWord ++ tailWord_1917679) baseStart_1917679 baseEnd_1917679 := by
    simpa [prefixWord, tailWord_1917679, baseEnd_1917679] using wordTrace_append hprefix tailTrace_1917679
  have hstable : (prefixWord ++ tailWord_1917679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917679).length < 2 ^ (prefixWord ++ tailWord_1917679).sum := by decide
  have hdescent : baseEnd_1917679 < baseStart_1917679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917705 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 2, 1, 5]
def baseStart_1917705 : Nat := 118140960795 + 1917705 * 2 ^ 59
def prefixEnd_1917705 : Nat := 4983230072969 + 3 ^ 40 * 1917705 * 2
def baseEnd_1917705 : Nat := 984704418530524704068141

theorem tailTrace_1917705 : CollatzResearch.WordTrace tailWord_1917705 prefixEnd_1917705 984704418530524704068141 := by
  unfold tailWord_1917705
  simp only [CollatzResearch.WordTrace]
  refine ⟨69944447517489777784074569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46629631678326518522716379 69944447517489777784074569)
  ·
    refine ⟨52458335638117333338055927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69944447517489777784074569 52458335638117333338055927)
    ·
      refine ⟨78687503457176000007083891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52458335638117333338055927 78687503457176000007083891)
      ·
        refine ⟨118031255185764000010625837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78687503457176000007083891 118031255185764000010625837)
        ·
          refine ⟨44261720694661500003984689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118031255185764000010625837 44261720694661500003984689)
          ·
            refine ⟨33196290520996125002988517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44261720694661500003984689 33196290520996125002988517)
            ·
              refine ⟨6224304472686773438060347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33196290520996125002988517 6224304472686773438060347)
              ·
                refine ⟨9336456709030160157090521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6224304472686773438060347 9336456709030160157090521)
                ·
                  refine ⟨7002342531772620117817891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9336456709030160157090521 7002342531772620117817891)
                  ·
                    refine ⟨10503513797658930176726837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7002342531772620117817891 10503513797658930176726837)
                    ·
                      refine ⟨984704418530524704068141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10503513797658930176726837 984704418530524704068141)
                      ·
                        rfl

theorem cell23_1917705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 2, 1, 5].length) (baseStart_1917705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917705 prefixEnd_1917705 := by exact prefixLift 1917705
  have htrace : WordTrace (prefixWord ++ tailWord_1917705) baseStart_1917705 baseEnd_1917705 := by
    simpa [prefixWord, tailWord_1917705, baseEnd_1917705] using wordTrace_append hprefix tailTrace_1917705
  have hstable : (prefixWord ++ tailWord_1917705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917705).length < 2 ^ (prefixWord ++ tailWord_1917705).sum := by decide
  have hdescent : baseEnd_1917705 < baseStart_1917705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917706 : List Nat := [3, 1, 2, 2, 1, 2, 5, 1, 1, 3, 2]
def baseStart_1917706 : Nat := 118140960795 + 1917706 * 2 ^ 59
def prefixEnd_1917706 : Nat := 4983230072969 + 3 ^ 40 * 1917706 * 2
def baseEnd_1917706 : Nat := 984704932011179200155637

theorem tailTrace_1917706 : CollatzResearch.WordTrace tailWord_1917706 prefixEnd_1917706 984704932011179200155637 := by
  unfold tailWord_1917706
  simp only [CollatzResearch.WordTrace]
  refine ⟨17486120997621538738715243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46629655993657436636573981 17486120997621538738715243)
  ·
    refine ⟨26229181496432308108072865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17486120997621538738715243 26229181496432308108072865)
    ·
      refine ⟨19671886122324231081054649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26229181496432308108072865 19671886122324231081054649)
      ·
        refine ⟨14753914591743173310790987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19671886122324231081054649 14753914591743173310790987)
        ·
          refine ⟨22130871887614759966186481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14753914591743173310790987 22130871887614759966186481)
          ·
            refine ⟨16598153915711069974639861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22130871887614759966186481 16598153915711069974639861)
            ·
              refine ⟨1556076929597912810122487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16598153915711069974639861 1556076929597912810122487)
              ·
                refine ⟨2334115394396869215183731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1556076929597912810122487 2334115394396869215183731)
                ·
                  refine ⟨3501173091595303822775597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334115394396869215183731 3501173091595303822775597)
                  ·
                    refine ⟨1312939909348238933540849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3501173091595303822775597 1312939909348238933540849)
                    ·
                      refine ⟨984704932011179200155637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1312939909348238933540849 984704932011179200155637)
                      ·
                        rfl

theorem cell23_1917706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_1917706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917706 prefixEnd_1917706 := by exact prefixLift 1917706
  have htrace : WordTrace (prefixWord ++ tailWord_1917706) baseStart_1917706 baseEnd_1917706 := by
    simpa [prefixWord, tailWord_1917706, baseEnd_1917706] using wordTrace_append hprefix tailTrace_1917706
  have hstable : (prefixWord ++ tailWord_1917706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917706).length < 2 ^ (prefixWord ++ tailWord_1917706).sum := by decide
  have hdescent : baseEnd_1917706 < baseStart_1917706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917714 : List Nat := [3, 2, 4, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_1917714 : Nat := 118140960795 + 1917714 * 2 ^ 59
def prefixEnd_1917714 : Nat := 4983230072969 + 3 ^ 40 * 1917714 * 2
def baseEnd_1917714 : Nat := 984709039856415168855601

theorem tailTrace_1917714 : CollatzResearch.WordTrace tailWord_1917714 prefixEnd_1917714 984709039856415168855601 := by
  unfold tailWord_1917714
  simp only [CollatzResearch.WordTrace]
  refine ⟨17486193943614293080288049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46629850516304781547434797 17486193943614293080288049)
  ·
    refine ⟨13114645457710719810216037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17486193943614293080288049 13114645457710719810216037)
    ·
      refine ⟨2458996023320759964415507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13114645457710719810216037 2458996023320759964415507)
      ·
        refine ⟨3688494034981139946623261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2458996023320759964415507 3688494034981139946623261)
        ·
          refine ⟨1383185263117927479983723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3688494034981139946623261 1383185263117927479983723)
          ·
            refine ⟨2074777894676891219975585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383185263117927479983723 2074777894676891219975585)
            ·
              refine ⟨1556083421007668414981689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2074777894676891219975585 1556083421007668414981689)
              ·
                refine ⟨1167062565755751311236267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1556083421007668414981689 1167062565755751311236267)
                ·
                  refine ⟨1750593848633626966854401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1167062565755751311236267 1750593848633626966854401)
                  ·
                    refine ⟨1312945386475220225140801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1750593848633626966854401 1312945386475220225140801)
                    ·
                      refine ⟨984709039856415168855601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1312945386475220225140801 984709039856415168855601)
                      ·
                        rfl

theorem cell23_1917714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_1917714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917714 prefixEnd_1917714 := by exact prefixLift 1917714
  have htrace : WordTrace (prefixWord ++ tailWord_1917714) baseStart_1917714 baseEnd_1917714 := by
    simpa [prefixWord, tailWord_1917714, baseEnd_1917714] using wordTrace_append hprefix tailTrace_1917714
  have hstable : (prefixWord ++ tailWord_1917714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917714).length < 2 ^ (prefixWord ++ tailWord_1917714).sum := by decide
  have hdescent : baseEnd_1917714 < baseStart_1917714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917715 : List Nat := [1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 4]
def baseStart_1917715 : Nat := 118140960795 + 1917715 * 2 ^ 59
def prefixEnd_1917715 : Nat := 4983230072969 + 3 ^ 40 * 1917715 * 2
def baseEnd_1917715 : Nat := 984709553337069664943095

theorem tailTrace_1917715 : CollatzResearch.WordTrace tailWord_1917715 prefixEnd_1917715 984709553337069664943095 := by
  unfold tailWord_1917715
  simp only [CollatzResearch.WordTrace]
  refine ⟨69944812247453549491938599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46629874831635699661292399 69944812247453549491938599)
  ·
    refine ⟨104917218371180324237907899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69944812247453549491938599 104917218371180324237907899)
    ·
      refine ⟨157375827556770486356861849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104917218371180324237907899 157375827556770486356861849)
      ·
        refine ⟨118031870667577864767646387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157375827556770486356861849 118031870667577864767646387)
        ·
          refine ⟨177047806001366797151469581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118031870667577864767646387 177047806001366797151469581)
          ·
            refine ⟨66392927250512548931801093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177047806001366797151469581 66392927250512548931801093)
            ·
              refine ⟨12448673859471102924712705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66392927250512548931801093 12448673859471102924712705)
              ·
                refine ⟨9336505394603327193534529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12448673859471102924712705 9336505394603327193534529)
                ·
                  refine ⟨7002379045952495395150897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9336505394603327193534529 7002379045952495395150897)
                  ·
                    refine ⟨5251784284464371546363173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7002379045952495395150897 5251784284464371546363173)
                    ·
                      refine ⟨984709553337069664943095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5251784284464371546363173 984709553337069664943095)
                      ·
                        rfl

theorem cell23_1917715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 4].length) (baseStart_1917715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917715 prefixEnd_1917715 := by exact prefixLift 1917715
  have htrace : WordTrace (prefixWord ++ tailWord_1917715) baseStart_1917715 baseEnd_1917715 := by
    simpa [prefixWord, tailWord_1917715, baseEnd_1917715] using wordTrace_append hprefix tailTrace_1917715
  have hstable : (prefixWord ++ tailWord_1917715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917715).length < 2 ^ (prefixWord ++ tailWord_1917715).sum := by decide
  have hdescent : baseEnd_1917715 < baseStart_1917715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917736 : List Nat := [2, 1, 5, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_1917736 : Nat := 118140960795 + 1917736 * 2 ^ 59
def prefixEnd_1917736 : Nat := 4983230072969 + 3 ^ 40 * 1917736 * 2
def baseEnd_1917736 : Nat := 984720336430814082780499

theorem tailTrace_1917736 : CollatzResearch.WordTrace tailWord_1917736 prefixEnd_1917736 984720336430814082780499 := by
  unfold tailWord_1917736
  simp only [CollatzResearch.WordTrace]
  refine ⟨34972789090188735039226531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46630385453584980052302041 34972789090188735039226531)
  ·
    refine ⟨52459183635283102558839797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34972789090188735039226531 52459183635283102558839797)
    ·
      refine ⟨4918048465807790864891231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52459183635283102558839797 4918048465807790864891231)
      ·
        refine ⟨7377072698711686297336847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4918048465807790864891231 7377072698711686297336847)
        ·
          refine ⟨11065609048067529446005271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7377072698711686297336847 11065609048067529446005271)
          ·
            refine ⟨16598413572101294169007907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11065609048067529446005271 16598413572101294169007907)
            ·
              refine ⟨24897620358151941253511861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16598413572101294169007907 24897620358151941253511861)
              ·
                refine ⟨2334151908576744492516737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24897620358151941253511861 2334151908576744492516737)
                ·
                  refine ⟨1750613931432558369387553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2334151908576744492516737 1750613931432558369387553)
                  ·
                    refine ⟨1312960448574418777040665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1750613931432558369387553 1312960448574418777040665)
                    ·
                      refine ⟨984720336430814082780499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1312960448574418777040665 984720336430814082780499)
                      ·
                        rfl

theorem cell23_1917736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_1917736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917736 prefixEnd_1917736 := by exact prefixLift 1917736
  have htrace : WordTrace (prefixWord ++ tailWord_1917736) baseStart_1917736 baseEnd_1917736 := by
    simpa [prefixWord, tailWord_1917736, baseEnd_1917736] using wordTrace_append hprefix tailTrace_1917736
  have hstable : (prefixWord ++ tailWord_1917736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917736).length < 2 ^ (prefixWord ++ tailWord_1917736).sum := by decide
  have hdescent : baseEnd_1917736 < baseStart_1917736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917742 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 9]
def baseStart_1917742 : Nat := 118140960795 + 1917742 * 2 ^ 59
def prefixEnd_1917742 : Nat := 4983230072969 + 3 ^ 40 * 1917742 * 2
def baseEnd_1917742 : Nat := 109413713034971228811719

theorem tailTrace_1917742 : CollatzResearch.WordTrace tailWord_1917742 prefixEnd_1917742 109413713034971228811719 := by
  unfold tailWord_1917742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8743224627294466637896435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46630531345570488735447653 8743224627294466637896435)
  ·
    refine ⟨13114836940941699956844653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8743224627294466637896435 13114836940941699956844653)
    ·
      refine ⟨4918063852853137483816745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13114836940941699956844653 4918063852853137483816745)
      ·
        refine ⟨3688547889639853112862559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4918063852853137483816745 3688547889639853112862559)
        ·
          refine ⟨5532821834459779669293839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3688547889639853112862559 5532821834459779669293839)
          ·
            refine ⟨8299232751689669503940759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5532821834459779669293839 8299232751689669503940759)
            ·
              refine ⟨12448849127534504255911139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8299232751689669503940759 12448849127534504255911139)
              ·
                refine ⟨18673273691301756383866709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12448849127534504255911139 18673273691301756383866709)
                ·
                  refine ⟨109413713034971228811719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18673273691301756383866709 109413713034971228811719)
                  ·
                    rfl

theorem cell23_1917742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 9].length) (baseStart_1917742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917742 prefixEnd_1917742 := by exact prefixLift 1917742
  have htrace : WordTrace (prefixWord ++ tailWord_1917742) baseStart_1917742 baseEnd_1917742 := by
    simpa [prefixWord, tailWord_1917742, baseEnd_1917742] using wordTrace_append hprefix tailTrace_1917742
  have hstable : (prefixWord ++ tailWord_1917742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917742).length < 2 ^ (prefixWord ++ tailWord_1917742).sum := by decide
  have hdescent : baseEnd_1917742 < baseStart_1917742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917759 : List Nat := [1, 1, 2, 2, 5, 2, 2, 3, 5]
def baseStart_1917759 : Nat := 118140960795 + 1917759 * 2 ^ 59
def prefixEnd_1917759 : Nat := 4983230072969 + 3 ^ 40 * 1917759 * 2
def baseEnd_1917759 : Nat := 109414682942874165865877

theorem tailTrace_1917759 : CollatzResearch.WordTrace tailWord_1917759 prefixEnd_1917759 109414682942874165865877 := by
  unfold tailWord_1917759
  simp only [CollatzResearch.WordTrace]
  refine ⟨69946417059294145006540331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46630944706196096671026887 69946417059294145006540331)
  ·
    refine ⟨104919625588941217509810497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69946417059294145006540331 104919625588941217509810497)
    ·
      refine ⟨78689719191705913132357873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104919625588941217509810497 78689719191705913132357873)
      ·
        refine ⟨59017289393779434849268405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78689719191705913132357873 59017289393779434849268405)
        ·
          refine ⟨5532870880666822017118913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59017289393779434849268405 5532870880666822017118913)
          ·
            refine ⟨4149653160500116512839185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5532870880666822017118913 4149653160500116512839185)
            ·
              refine ⟨3112239870375087384629389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4149653160500116512839185 3112239870375087384629389)
              ·
                refine ⟨1167089951390657769236021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3112239870375087384629389 1167089951390657769236021)
                ·
                  refine ⟨109414682942874165865877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1167089951390657769236021 109414682942874165865877)
                  ·
                    rfl

theorem cell23_1917759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 5].length) (baseStart_1917759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917759 prefixEnd_1917759 := by exact prefixLift 1917759
  have htrace : WordTrace (prefixWord ++ tailWord_1917759) baseStart_1917759 baseEnd_1917759 := by
    simpa [prefixWord, tailWord_1917759, baseEnd_1917759] using wordTrace_append hprefix tailTrace_1917759
  have hstable : (prefixWord ++ tailWord_1917759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917759).length < 2 ^ (prefixWord ++ tailWord_1917759).sum := by decide
  have hdescent : baseEnd_1917759 < baseStart_1917759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917765 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 1, 2, 5]
def baseStart_1917765 : Nat := 118140960795 + 1917765 * 2 ^ 59
def prefixEnd_1917765 : Nat := 4983230072969 + 3 ^ 40 * 1917765 * 2
def baseEnd_1917765 : Nat := 984735227369794469317865

theorem tailTrace_1917765 : CollatzResearch.WordTrace tailWord_1917765 prefixEnd_1917765 984735227369794469317865 := by
  unfold tailWord_1917765
  simp only [CollatzResearch.WordTrace]
  refine ⟨69946635897272408031258749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46631090598181605354172499 69946635897272408031258749)
  ·
    refine ⟨26229988461477153011722031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69946635897272408031258749 26229988461477153011722031)
    ·
      refine ⟨39344982692215729517583047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26229988461477153011722031 39344982692215729517583047)
      ·
        refine ⟨59017474038323594276374571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39344982692215729517583047 59017474038323594276374571)
        ·
          refine ⟨88526211057485391414561857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59017474038323594276374571 88526211057485391414561857)
          ·
            refine ⟨66394658293114043560921393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88526211057485391414561857 66394658293114043560921393)
            ·
              refine ⟨49795993719835532670691045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66394658293114043560921393 49795993719835532670691045)
              ·
                refine ⟨9336748822469162375754571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49795993719835532670691045 9336748822469162375754571)
                ·
                  refine ⟨14005123233703743563631857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9336748822469162375754571 14005123233703743563631857)
                  ·
                    refine ⟨10503842425277807672723893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14005123233703743563631857 10503842425277807672723893)
                    ·
                      refine ⟨984735227369794469317865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10503842425277807672723893 984735227369794469317865)
                      ·
                        rfl

theorem cell23_1917765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_1917765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917765 prefixEnd_1917765 := by exact prefixLift 1917765
  have htrace : WordTrace (prefixWord ++ tailWord_1917765) baseStart_1917765 baseEnd_1917765 := by
    simpa [prefixWord, tailWord_1917765, baseEnd_1917765] using wordTrace_append hprefix tailTrace_1917765
  have hstable : (prefixWord ++ tailWord_1917765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917765).length < 2 ^ (prefixWord ++ tailWord_1917765).sum := by decide
  have hdescent : baseEnd_1917765 < baseStart_1917765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917829 : List Nat := [1, 3, 1, 1, 3, 4, 1, 2, 2, 2, 3]
def baseStart_1917829 : Nat := 118140960795 + 1917829 * 2 ^ 59
def prefixEnd_1917829 : Nat := 4983230072969 + 3 ^ 40 * 1917829 * 2
def baseEnd_1917829 : Nat := 984768090131682218917571

theorem tailTrace_1917829 : CollatzResearch.WordTrace tailWord_1917829 prefixEnd_1917829 984768090131682218917571 := by
  unfold tailWord_1917829
  simp only [CollatzResearch.WordTrace]
  refine ⟨69948970169040546961588541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46632646779360364641059027 69948970169040546961588541)
  ·
    refine ⟨26230863813390205110595703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69948970169040546961588541 26230863813390205110595703)
    ·
      refine ⟨39346295720085307665893555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26230863813390205110595703 39346295720085307665893555)
      ·
        refine ⟨59019443580127961498840333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39346295720085307665893555 59019443580127961498840333)
        ·
          refine ⟨22132291342547985562065125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59019443580127961498840333 22132291342547985562065125)
          ·
            refine ⟨4149804626727747292887211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22132291342547985562065125 4149804626727747292887211)
            ·
              refine ⟨6224706940091620939330817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4149804626727747292887211 6224706940091620939330817)
              ·
                refine ⟨4668530205068715704498113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6224706940091620939330817 4668530205068715704498113)
                ·
                  refine ⟨3501397653801536778373585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4668530205068715704498113 3501397653801536778373585)
                  ·
                    refine ⟨2626048240351152583780189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3501397653801536778373585 2626048240351152583780189)
                    ·
                      refine ⟨984768090131682218917571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2626048240351152583780189 984768090131682218917571)
                      ·
                        rfl

theorem cell23_1917829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_1917829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917829 prefixEnd_1917829 := by exact prefixLift 1917829
  have htrace : WordTrace (prefixWord ++ tailWord_1917829) baseStart_1917829 baseEnd_1917829 := by
    simpa [prefixWord, tailWord_1917829, baseEnd_1917829] using wordTrace_append hprefix tailTrace_1917829
  have hstable : (prefixWord ++ tailWord_1917829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917829).length < 2 ^ (prefixWord ++ tailWord_1917829).sum := by decide
  have hdescent : baseEnd_1917829 < baseStart_1917829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917832 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 8]
def baseStart_1917832 : Nat := 118140960795 + 1917832 * 2 ^ 59
def prefixEnd_1917832 : Nat := 4983230072969 + 3 ^ 40 * 1917832 * 2
def baseEnd_1917832 : Nat := 109418847841516189686673

theorem tailTrace_1917832 : CollatzResearch.WordTrace tailWord_1917832 prefixEnd_1917832 109418847841516189686673 := by
  unfold tailWord_1917832
  simp only [CollatzResearch.WordTrace]
  refine ⟨34974539794014839236973875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46632719725353118982631833 34974539794014839236973875)
  ·
    refine ⟨52461809691022258855460813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34974539794014839236973875 52461809691022258855460813)
    ·
      refine ⟨19673178634133347070797805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52461809691022258855460813 19673178634133347070797805)
      ·
        refine ⟨7377441987800005151549177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19673178634133347070797805 7377441987800005151549177)
        ·
          refine ⟨5533081490850003863661883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7377441987800005151549177 5533081490850003863661883)
          ·
            refine ⟨8299622236275005795492825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5533081490850003863661883 8299622236275005795492825)
            ·
              refine ⟨6224716677206254346619619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8299622236275005795492825 6224716677206254346619619)
              ·
                refine ⟨9337075015809381519929429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6224716677206254346619619 9337075015809381519929429)
                ·
                  refine ⟨109418847841516189686673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9337075015809381519929429 109418847841516189686673)
                  ·
                    rfl

theorem cell23_1917832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 8].length) (baseStart_1917832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917832 prefixEnd_1917832 := by exact prefixLift 1917832
  have htrace : WordTrace (prefixWord ++ tailWord_1917832) baseStart_1917832 baseEnd_1917832 := by
    simpa [prefixWord, tailWord_1917832, baseEnd_1917832] using wordTrace_append hprefix tailTrace_1917832
  have hstable : (prefixWord ++ tailWord_1917832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917832).length < 2 ^ (prefixWord ++ tailWord_1917832).sum := by decide
  have hdescent : baseEnd_1917832 < baseStart_1917832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917835 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 8]
def baseStart_1917835 : Nat := 118140960795 + 1917835 * 2 ^ 59
def prefixEnd_1917835 : Nat := 4983230072969 + 3 ^ 40 * 1917835 * 2
def baseEnd_1917835 : Nat := 984771171015609195442543

theorem tailTrace_1917835 : CollatzResearch.WordTrace tailWord_1917835 prefixEnd_1917835 984771171015609195442543 := by
  unfold tailWord_1917835
  simp only [CollatzResearch.WordTrace]
  refine ⟨69949189007018809986306959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46632792671345873324204639 69949189007018809986306959)
  ·
    refine ⟨104923783510528214979460439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69949189007018809986306959 104923783510528214979460439)
    ·
      refine ⟨157385675265792322469190659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104923783510528214979460439 157385675265792322469190659)
      ·
        refine ⟨236078512898688483703785989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157385675265792322469190659 236078512898688483703785989)
        ·
          refine ⟨44264721168504090694459873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236078512898688483703785989 44264721168504090694459873)
          ·
            refine ⟨33198540876378068020844905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44264721168504090694459873 33198540876378068020844905)
            ·
              refine ⟨24898905657283551015633679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33198540876378068020844905 24898905657283551015633679)
              ·
                refine ⟨37348358485925326523450519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24898905657283551015633679 37348358485925326523450519)
                ·
                  refine ⟨56022537728887989785175779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37348358485925326523450519 56022537728887989785175779)
                  ·
                    refine ⟨84033806593331984677763669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56022537728887989785175779 84033806593331984677763669)
                    ·
                      refine ⟨984771171015609195442543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 84033806593331984677763669 984771171015609195442543)
                      ·
                        rfl

theorem cell23_1917835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 8].length) (baseStart_1917835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917835 prefixEnd_1917835 := by exact prefixLift 1917835
  have htrace : WordTrace (prefixWord ++ tailWord_1917835) baseStart_1917835 baseEnd_1917835 := by
    simpa [prefixWord, tailWord_1917835, baseEnd_1917835] using wordTrace_append hprefix tailTrace_1917835
  have hstable : (prefixWord ++ tailWord_1917835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917835).length < 2 ^ (prefixWord ++ tailWord_1917835).sum := by decide
  have hdescent : baseEnd_1917835 < baseStart_1917835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917859 : List Nat := [1, 1, 1, 4, 1, 2, 2, 4, 3, 1, 3]
def baseStart_1917859 : Nat := 118140960795 + 1917859 * 2 ^ 59
def prefixEnd_1917859 : Nat := 4983230072969 + 3 ^ 40 * 1917859 * 2
def baseEnd_1917859 : Nat := 984783494551317101542433

theorem tailTrace_1917859 : CollatzResearch.WordTrace tailWord_1917859 prefixEnd_1917859 984783494551317101542433 := by
  unfold tailWord_1917859
  simp only [CollatzResearch.WordTrace]
  refine ⟨69950064358931862085180631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46633376239287908056787087 69950064358931862085180631)
  ·
    refine ⟨104925096538397793127770947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69950064358931862085180631 104925096538397793127770947)
    ·
      refine ⟨157387644807596689691656421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104925096538397793127770947 157387644807596689691656421)
      ·
        refine ⟨29510183401424379317185579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157387644807596689691656421 29510183401424379317185579)
        ·
          refine ⟨44265275102136568975778369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29510183401424379317185579 44265275102136568975778369)
          ·
            refine ⟨33198956326602426731833777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44265275102136568975778369 33198956326602426731833777)
            ·
              refine ⟨24899217244951820048875333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33198956326602426731833777 24899217244951820048875333)
              ·
                refine ⟨4668603233428466259164125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24899217244951820048875333 4668603233428466259164125)
                ·
                  refine ⟨1750726212535674847186547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4668603233428466259164125 1750726212535674847186547)
                  ·
                    refine ⟨2626089318803512270779821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1750726212535674847186547 2626089318803512270779821)
                    ·
                      refine ⟨984783494551317101542433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2626089318803512270779821 984783494551317101542433)
                      ·
                        rfl

theorem cell23_1917859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_1917859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917859 prefixEnd_1917859 := by exact prefixLift 1917859
  have htrace : WordTrace (prefixWord ++ tailWord_1917859) baseStart_1917859 baseEnd_1917859 := by
    simpa [prefixWord, tailWord_1917859, baseEnd_1917859] using wordTrace_append hprefix tailTrace_1917859
  have hstable : (prefixWord ++ tailWord_1917859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917859).length < 2 ^ (prefixWord ++ tailWord_1917859).sum := by decide
  have hdescent : baseEnd_1917859 < baseStart_1917859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917886 : List Nat := [4, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2]
def baseStart_1917886 : Nat := 118140960795 + 1917886 * 2 ^ 59
def prefixEnd_1917886 : Nat := 4983230072969 + 3 ^ 40 * 1917886 * 2
def baseEnd_1917886 : Nat := 984797358528988495904809

theorem tailTrace_1917886 : CollatzResearch.WordTrace tailWord_1917886 prefixEnd_1917886 984797358528988495904809 := by
  unfold tailWord_1917886
  simp only [CollatzResearch.WordTrace]
  refine ⟨8743881141229255712051689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46634032753222697130942341 8743881141229255712051689)
  ·
    refine ⟨6557910855921941784038767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8743881141229255712051689 6557910855921941784038767)
    ·
      refine ⟨9836866283882912676058151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6557910855921941784038767 9836866283882912676058151)
      ·
        refine ⟨14755299425824369014087227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9836866283882912676058151 14755299425824369014087227)
        ·
          refine ⟨22132949138736553521130841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14755299425824369014087227 22132949138736553521130841)
          ·
            refine ⟨16599711854052415140848131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22132949138736553521130841 16599711854052415140848131)
            ·
              refine ⟨24899567781078622711272197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16599711854052415140848131 24899567781078622711272197)
              ·
                refine ⟨4668668958952241758363537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24899567781078622711272197 4668668958952241758363537)
                ·
                  refine ⟨3501501719214181318772653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4668668958952241758363537 3501501719214181318772653)
                  ·
                    refine ⟨1313063144705317994539745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3501501719214181318772653 1313063144705317994539745)
                    ·
                      refine ⟨984797358528988495904809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1313063144705317994539745 984797358528988495904809)
                      ·
                        rfl

theorem cell23_1917886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_1917886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917886 prefixEnd_1917886 := by exact prefixLift 1917886
  have htrace : WordTrace (prefixWord ++ tailWord_1917886) baseStart_1917886 baseEnd_1917886 := by
    simpa [prefixWord, tailWord_1917886, baseEnd_1917886] using wordTrace_append hprefix tailTrace_1917886
  have hstable : (prefixWord ++ tailWord_1917886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917886).length < 2 ^ (prefixWord ++ tailWord_1917886).sum := by decide
  have hdescent : baseEnd_1917886 < baseStart_1917886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917966 : List Nat := [4, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3]
def baseStart_1917966 : Nat := 118140960795 + 1917966 * 2 ^ 59
def prefixEnd_1917966 : Nat := 4983230072969 + 3 ^ 40 * 1917966 * 2
def baseEnd_1917966 : Nat := 984838436981348182904441

theorem tailTrace_1917966 : CollatzResearch.WordTrace tailWord_1917966 prefixEnd_1917966 984838436981348182904441 := by
  unfold tailWord_1917966
  simp only [CollatzResearch.WordTrace]
  refine ⟨8744245871193027419915719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46635977979696146239550501 8744245871193027419915719)
  ·
    refine ⟨13116368806789541129873579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8744245871193027419915719 13116368806789541129873579)
    ·
      refine ⟨19674553210184311694810369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13116368806789541129873579 19674553210184311694810369)
      ·
        refine ⟨14755914907638233771107777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19674553210184311694810369 14755914907638233771107777)
        ·
          refine ⟨11066936180728675328330833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14755914907638233771107777 11066936180728675328330833)
          ·
            refine ⟨8300202135546506496248125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11066936180728675328330833 8300202135546506496248125)
            ·
              refine ⟨3112575800829939936093047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8300202135546506496248125 3112575800829939936093047)
              ·
                refine ⟨4668863701244909904139571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3112575800829939936093047 4668863701244909904139571)
                ·
                  refine ⟨7003295551867364856209357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4668863701244909904139571 7003295551867364856209357)
                  ·
                    refine ⟨2626235831950261821078509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7003295551867364856209357 2626235831950261821078509)
                    ·
                      refine ⟨984838436981348182904441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2626235831950261821078509 984838436981348182904441)
                      ·
                        rfl

theorem cell23_1917966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_1917966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917966 prefixEnd_1917966 := by exact prefixLift 1917966
  have htrace : WordTrace (prefixWord ++ tailWord_1917966) baseStart_1917966 baseEnd_1917966 := by
    simpa [prefixWord, tailWord_1917966, baseEnd_1917966] using wordTrace_append hprefix tailTrace_1917966
  have hstable : (prefixWord ++ tailWord_1917966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917966).length < 2 ^ (prefixWord ++ tailWord_1917966).sum := by decide
  have hdescent : baseEnd_1917966 < baseStart_1917966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1917984 : List Nat := [2, 1, 1, 7, 1, 2, 1, 3, 1, 2, 2]
def baseStart_1917984 : Nat := 118140960795 + 1917984 * 2 ^ 59
def prefixEnd_1917984 : Nat := 4983230072969 + 3 ^ 40 * 1917984 * 2
def baseEnd_1917984 : Nat := 984847679633129112479359

theorem tailTrace_1917984 : CollatzResearch.WordTrace tailWord_1917984 prefixEnd_1917984 984847679633129112479359 := by
  unfold tailWord_1917984
  simp only [CollatzResearch.WordTrace]
  refine ⟨34977311741739504216740503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46636415655652672288987337 34977311741739504216740503)
  ·
    refine ⟨52465967612609256325110755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34977311741739504216740503 52465967612609256325110755)
    ·
      refine ⟨78698951418913884487666133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52465967612609256325110755 78698951418913884487666133)
      ·
        refine ⟨1844506673880794167679675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 78698951418913884487666133 1844506673880794167679675)
        ·
          refine ⟨2766760010821191251519513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1844506673880794167679675 2766760010821191251519513)
          ·
            refine ⟨2075070008115893438639635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2766760010821191251519513 2075070008115893438639635)
            ·
              refine ⟨3112605012173840157959453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2075070008115893438639635 3112605012173840157959453)
              ·
                refine ⟨1167226879565190059234795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3112605012173840157959453 1167226879565190059234795)
                ·
                  refine ⟨1750840319347785088852193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1167226879565190059234795 1750840319347785088852193)
                  ·
                    refine ⟨1313130239510838816639145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1750840319347785088852193 1313130239510838816639145)
                    ·
                      refine ⟨984847679633129112479359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1313130239510838816639145 984847679633129112479359)
                      ·
                        rfl

theorem cell23_1917984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_1917984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1917984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1917984 prefixEnd_1917984 := by exact prefixLift 1917984
  have htrace : WordTrace (prefixWord ++ tailWord_1917984) baseStart_1917984 baseEnd_1917984 := by
    simpa [prefixWord, tailWord_1917984, baseEnd_1917984] using wordTrace_append hprefix tailTrace_1917984
  have hstable : (prefixWord ++ tailWord_1917984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1917984).length < 2 ^ (prefixWord ++ tailWord_1917984).sum := by decide
  have hdescent : baseEnd_1917984 < baseStart_1917984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1917984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918017 : List Nat := [1, 2, 5, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_1918017 : Nat := 118140960795 + 1918017 * 2 ^ 59
def prefixEnd_1918017 : Nat := 4983230072969 + 3 ^ 40 * 1918017 * 2
def baseEnd_1918017 : Nat := 984864624494727483366707

theorem tailTrace_1918017 : CollatzResearch.WordTrace tailWord_1918017 prefixEnd_1918017 984864624494727483366707 := by
  unfold tailWord_1918017
  simp only [CollatzResearch.WordTrace]
  refine ⟨69955827092359455069432305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46637218061572970046288203 69955827092359455069432305)
  ·
    refine ⟨52466870319269591302074229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69955827092359455069432305 52466870319269591302074229)
    ·
      refine ⟨4918769092431524184569459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52466870319269591302074229 4918769092431524184569459)
      ·
        refine ⟨7378153638647286276854189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4918769092431524184569459 7378153638647286276854189)
        ·
          refine ⟨2766807614492732353820321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7378153638647286276854189 2766807614492732353820321)
          ·
            refine ⟨2075105710869549265365241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2766807614492732353820321 2075105710869549265365241)
            ·
              refine ⟨1556329283152161949023931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2075105710869549265365241 1556329283152161949023931)
              ·
                refine ⟨2334493924728242923535897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1556329283152161949023931 2334493924728242923535897)
                ·
                  refine ⟨1750870443546182192651923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2334493924728242923535897 1750870443546182192651923)
                  ·
                    refine ⟨2626305665319273288977885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1750870443546182192651923 2626305665319273288977885)
                    ·
                      refine ⟨984864624494727483366707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2626305665319273288977885 984864624494727483366707)
                      ·
                        rfl

theorem cell23_1918017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_1918017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918017 prefixEnd_1918017 := by exact prefixLift 1918017
  have htrace : WordTrace (prefixWord ++ tailWord_1918017) baseStart_1918017 baseEnd_1918017 := by
    simpa [prefixWord, tailWord_1918017, baseEnd_1918017] using wordTrace_append hprefix tailTrace_1918017
  have hstable : (prefixWord ++ tailWord_1918017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918017).length < 2 ^ (prefixWord ++ tailWord_1918017).sum := by decide
  have hdescent : baseEnd_1918017 < baseStart_1918017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918032 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 8]
def baseStart_1918032 : Nat := 118140960795 + 1918032 * 2 ^ 59
def prefixEnd_1918032 : Nat := 4983230072969 + 3 ^ 40 * 1918032 * 2
def baseEnd_1918032 : Nat := 984872326704544924679137

theorem tailTrace_1918032 : CollatzResearch.WordTrace tailWord_1918032 prefixEnd_1918032 984872326704544924679137 := by
  unfold tailWord_1918032
  simp only [CollatzResearch.WordTrace]
  refine ⟨34978187093652556315614175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46637582791536741754152233 34978187093652556315614175)
  ·
    refine ⟨52467280640478834473421263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34978187093652556315614175 52467280640478834473421263)
    ·
      refine ⟨78700920960718251710131895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52467280640478834473421263 78700920960718251710131895)
      ·
        refine ⟨118051381441077377565197843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78700920960718251710131895 118051381441077377565197843)
        ·
          refine ⟨177077072161616066347796765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118051381441077377565197843 177077072161616066347796765)
          ·
            refine ⟨66403902060606024880423787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177077072161616066347796765 66403902060606024880423787)
            ·
              refine ⟨99605853090909037320635681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66403902060606024880423787 99605853090909037320635681)
              ·
                refine ⟨74704389818181777990476761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99605853090909037320635681 74704389818181777990476761)
                ·
                  refine ⟨56028292363636333492857571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74704389818181777990476761 56028292363636333492857571)
                  ·
                    refine ⟨84042438545454500239286357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56028292363636333492857571 84042438545454500239286357)
                    ·
                      refine ⟨984872326704544924679137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 84042438545454500239286357 984872326704544924679137)
                      ·
                        rfl

theorem cell23_1918032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_1918032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918032 prefixEnd_1918032 := by exact prefixLift 1918032
  have htrace : WordTrace (prefixWord ++ tailWord_1918032) baseStart_1918032 baseEnd_1918032 := by
    simpa [prefixWord, tailWord_1918032, baseEnd_1918032] using wordTrace_append hprefix tailTrace_1918032
  have hstable : (prefixWord ++ tailWord_1918032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918032).length < 2 ^ (prefixWord ++ tailWord_1918032).sum := by decide
  have hdescent : baseEnd_1918032 < baseStart_1918032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918039 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 3]
def baseStart_1918039 : Nat := 118140960795 + 1918039 * 2 ^ 59
def prefixEnd_1918039 : Nat := 4983230072969 + 3 ^ 40 * 1918039 * 2
def baseEnd_1918039 : Nat := 984875921069126397291605

theorem tailTrace_1918039 : CollatzResearch.WordTrace tailWord_1918039 prefixEnd_1918039 984875921069126397291605 := by
  unfold tailWord_1918039
  simp only [CollatzResearch.WordTrace]
  refine ⟨69956629498279752826733171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46637752998853168551155447 69956629498279752826733171)
  ·
    refine ⟨104934944247419629240099757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69956629498279752826733171 104934944247419629240099757)
    ·
      refine ⟨39350604092782360965037409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104934944247419629240099757 39350604092782360965037409)
      ·
        refine ⟨29512953069586770723778057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39350604092782360965037409 29512953069586770723778057)
        ·
          refine ⟨22134714802190078042833543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29512953069586770723778057 22134714802190078042833543)
          ·
            refine ⟨33202072203285117064250315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22134714802190078042833543 33202072203285117064250315)
            ·
              refine ⟨49803108304927675596375473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33202072203285117064250315 49803108304927675596375473)
              ·
                refine ⟨37352331228695756697281605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49803108304927675596375473 37352331228695756697281605)
                ·
                  refine ⟨7003562105380454380740301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37352331228695756697281605 7003562105380454380740301)
                  ·
                    refine ⟨2626335789517670392777613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7003562105380454380740301 2626335789517670392777613)
                    ·
                      refine ⟨984875921069126397291605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2626335789517670392777613 984875921069126397291605)
                      ·
                        rfl

theorem cell23_1918039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_1918039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918039 prefixEnd_1918039 := by exact prefixLift 1918039
  have htrace : WordTrace (prefixWord ++ tailWord_1918039) baseStart_1918039 baseEnd_1918039 := by
    simpa [prefixWord, tailWord_1918039, baseEnd_1918039] using wordTrace_append hprefix tailTrace_1918039
  have hstable : (prefixWord ++ tailWord_1918039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918039).length < 2 ^ (prefixWord ++ tailWord_1918039).sum := by decide
  have hdescent : baseEnd_1918039 < baseStart_1918039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918066 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 1, 7, 2]
def baseStart_1918066 : Nat := 118140960795 + 1918066 * 2 ^ 59
def prefixEnd_1918066 : Nat := 4983230072969 + 3 ^ 40 * 1918066 * 2
def baseEnd_1918066 : Nat := 984889785046797791653981

theorem tailTrace_1918066 : CollatzResearch.WordTrace tailWord_1918066 prefixEnd_1918066 984889785046797791653981 := by
  unfold tailWord_1918066
  simp only [CollatzResearch.WordTrace]
  refine ⟨17489403567295484109491513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46638409512787957625310701 17489403567295484109491513)
  ·
    refine ⟨13117052675471613082118635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17489403567295484109491513 13117052675471613082118635)
    ·
      refine ⟨19675579013207419623177953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13117052675471613082118635 19675579013207419623177953)
      ·
        refine ⟨14756684259905564717383465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19675579013207419623177953 14756684259905564717383465)
        ·
          refine ⟨11067513194929173538037599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14756684259905564717383465 11067513194929173538037599)
          ·
            refine ⟨16601269792393760307056399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11067513194929173538037599 16601269792393760307056399)
            ·
              refine ⟨24901904688590640460584599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16601269792393760307056399 24901904688590640460584599)
              ·
                refine ⟨37352857032885960690876899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24901904688590640460584599 37352857032885960690876899)
                ·
                  refine ⟨56029285549328941036315349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37352857032885960690876899 56029285549328941036315349)
                  ·
                    refine ⟨1313186380062397055538641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56029285549328941036315349 1313186380062397055538641)
                    ·
                      refine ⟨984889785046797791653981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1313186380062397055538641 984889785046797791653981)
                      ·
                        rfl

theorem cell23_1918066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_1918066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918066 prefixEnd_1918066 := by exact prefixLift 1918066
  have htrace : WordTrace (prefixWord ++ tailWord_1918066) baseStart_1918066 baseEnd_1918066 := by
    simpa [prefixWord, tailWord_1918066, baseEnd_1918066] using wordTrace_append hprefix tailTrace_1918066
  have hstable : (prefixWord ++ tailWord_1918066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918066).length < 2 ^ (prefixWord ++ tailWord_1918066).sum := by decide
  have hdescent : baseEnd_1918066 < baseStart_1918066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918109 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_1918109 : Nat := 118140960795 + 1918109 * 2 ^ 59
def prefixEnd_1918109 : Nat := 4983230072969 + 3 ^ 40 * 1918109 * 2
def baseEnd_1918109 : Nat := 984911864714941123416283

theorem tailTrace_1918109 : CollatzResearch.WordTrace tailWord_1918109 prefixEnd_1918109 984911864714941123416283 := by
  unfold tailWord_1918109
  simp only [CollatzResearch.WordTrace]
  refine ⟨69959182608026154781781381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46639455072017436521187587 69959182608026154781781381)
  ·
    refine ⟨13117346739004904021584009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69959182608026154781781381 13117346739004904021584009)
    ·
      refine ⟨9838010054253678016188007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13117346739004904021584009 9838010054253678016188007)
      ·
        refine ⟨14757015081380517024282011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9838010054253678016188007 14757015081380517024282011)
        ·
          refine ⟨22135522622070775536423017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14757015081380517024282011 22135522622070775536423017)
          ·
            refine ⟨16601641966553081652317263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22135522622070775536423017 16601641966553081652317263)
            ·
              refine ⟨24902462949829622478475895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16601641966553081652317263 24902462949829622478475895)
              ·
                refine ⟨37353694424744433717713843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24902462949829622478475895 37353694424744433717713843)
                ·
                  refine ⟨56030541637116650576570765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37353694424744433717713843 56030541637116650576570765)
                  ·
                    refine ⟨21011453113918743966214037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56030541637116650576570765 21011453113918743966214037)
                    ·
                      refine ⟨984911864714941123416283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21011453113918743966214037 984911864714941123416283)
                      ·
                        rfl

theorem cell23_1918109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_1918109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918109 prefixEnd_1918109 := by exact prefixLift 1918109
  have htrace : WordTrace (prefixWord ++ tailWord_1918109) baseStart_1918109 baseEnd_1918109 := by
    simpa [prefixWord, tailWord_1918109, baseEnd_1918109] using wordTrace_append hprefix tailTrace_1918109
  have hstable : (prefixWord ++ tailWord_1918109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918109).length < 2 ^ (prefixWord ++ tailWord_1918109).sum := by decide
  have hdescent : baseEnd_1918109 < baseStart_1918109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918180 : List Nat := [2, 3, 1, 1, 1, 2, 2, 6, 1, 1, 3]
def baseStart_1918180 : Nat := 118140960795 + 1918180 * 2 ^ 59
def prefixEnd_1918180 : Nat := 4983230072969 + 3 ^ 40 * 1918180 * 2
def baseEnd_1918180 : Nat := 984948321841410345628457

theorem tailTrace_1918180 : CollatzResearch.WordTrace tailWord_1918180 prefixEnd_1918180 984948321841410345628457 := by
  unfold tailWord_1918180
  simp only [CollatzResearch.WordTrace]
  refine ⟨34980886095384466953807997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46641181460512622605077329 34980886095384466953807997)
  ·
    refine ⟨13117832285769175107677999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34980886095384466953807997 13117832285769175107677999)
    ·
      refine ⟨19676748428653762661516999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13117832285769175107677999 19676748428653762661516999)
      ·
        refine ⟨29515122642980643992275499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19676748428653762661516999 29515122642980643992275499)
        ·
          refine ⟨44272683964470965988413249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29515122642980643992275499 44272683964470965988413249)
          ·
            refine ⟨33204512973353224491309937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44272683964470965988413249 33204512973353224491309937)
            ·
              refine ⟨24903384730014918368482453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33204512973353224491309937 24903384730014918368482453)
              ·
                refine ⟨1167346159219449298522615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24903384730014918368482453 1167346159219449298522615)
                ·
                  refine ⟨1751019238829173947783923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1167346159219449298522615 1751019238829173947783923)
                  ·
                    refine ⟨2626528858243760921675885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1751019238829173947783923 2626528858243760921675885)
                    ·
                      refine ⟨984948321841410345628457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2626528858243760921675885 984948321841410345628457)
                      ·
                        rfl

theorem cell23_1918180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 1, 1, 3].length) (baseStart_1918180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918180 prefixEnd_1918180 := by exact prefixLift 1918180
  have htrace : WordTrace (prefixWord ++ tailWord_1918180) baseStart_1918180 baseEnd_1918180 := by
    simpa [prefixWord, tailWord_1918180, baseEnd_1918180] using wordTrace_append hprefix tailTrace_1918180
  have hstable : (prefixWord ++ tailWord_1918180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918180).length < 2 ^ (prefixWord ++ tailWord_1918180).sum := by decide
  have hdescent : baseEnd_1918180 < baseStart_1918180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918220 : List Nat := [2, 2, 1, 2, 2, 4, 3, 1, 1, 1, 4]
def baseStart_1918220 : Nat := 118140960795 + 1918220 * 2 ^ 59
def prefixEnd_1918220 : Nat := 4983230072969 + 3 ^ 40 * 1918220 * 2
def baseEnd_1918220 : Nat := 984968861067590189128273

theorem tailTrace_1918220 : CollatzResearch.WordTrace tailWord_1918220 prefixEnd_1918220 984968861067590189128273 := by
  unfold tailWord_1918220
  simp only [CollatzResearch.WordTrace]
  refine ⟨34981615555312010369536057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46642154073749347159381409 34981615555312010369536057)
  ·
    refine ⟨26236211666484007777152043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34981615555312010369536057 26236211666484007777152043)
    ·
      refine ⟨39354317499726011665728065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26236211666484007777152043 39354317499726011665728065)
      ·
        refine ⟨29515738124794508749296049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39354317499726011665728065 29515738124794508749296049)
        ·
          refine ⟨22136803593595881561972037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29515738124794508749296049 22136803593595881561972037)
          ·
            refine ⟨4150650673799227792869757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22136803593595881561972037 4150650673799227792869757)
            ·
              refine ⟨1556494002674710422326159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4150650673799227792869757 1556494002674710422326159)
              ·
                refine ⟨2334741004012065633489239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1556494002674710422326159 2334741004012065633489239)
                ·
                  refine ⟨3502111506018098450233859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334741004012065633489239 3502111506018098450233859)
                  ·
                    refine ⟨5253167259027147675350789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3502111506018098450233859 5253167259027147675350789)
                    ·
                      refine ⟨984968861067590189128273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5253167259027147675350789 984968861067590189128273)
                      ·
                        rfl

theorem cell23_1918220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_1918220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918220 prefixEnd_1918220 := by exact prefixLift 1918220
  have htrace : WordTrace (prefixWord ++ tailWord_1918220) baseStart_1918220 baseEnd_1918220 := by
    simpa [prefixWord, tailWord_1918220, baseEnd_1918220] using wordTrace_append hprefix tailTrace_1918220
  have hstable : (prefixWord ++ tailWord_1918220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918220).length < 2 ^ (prefixWord ++ tailWord_1918220).sum := by decide
  have hdescent : baseEnd_1918220 < baseStart_1918220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918250 : List Nat := [3, 1, 4, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1918250 : Nat := 118140960795 + 1918250 * 2 ^ 59
def prefixEnd_1918250 : Nat := 4983230072969 + 3 ^ 40 * 1918250 * 2
def baseEnd_1918250 : Nat := 984984265487225071753135

theorem tailTrace_1918250 : CollatzResearch.WordTrace tailWord_1918250 prefixEnd_1918250 984984265487225071753135 := by
  unfold tailWord_1918250
  simp only [CollatzResearch.WordTrace]
  refine ⟨17491081325128833965666051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46642883533676890575109469 17491081325128833965666051)
  ·
    refine ⟨26236621987693250948499077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17491081325128833965666051 26236621987693250948499077)
    ·
      refine ⟨4919366622692484552843577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26236621987693250948499077 4919366622692484552843577)
      ·
        refine ⟨3689524967019363414632683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4919366622692484552843577 3689524967019363414632683)
        ·
          refine ⟨5534287450529045121949025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3689524967019363414632683 5534287450529045121949025)
          ·
            refine ⟨4150715587896783841461769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5534287450529045121949025 4150715587896783841461769)
            ·
              refine ⟨3113036690922587881096327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4150715587896783841461769 3113036690922587881096327)
              ·
                refine ⟨4669555036383881821644491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3113036690922587881096327 4669555036383881821644491)
                ·
                  refine ⟨7004332554575822732466737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4669555036383881821644491 7004332554575822732466737)
                  ·
                    refine ⟨5253249415931867049350053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7004332554575822732466737 5253249415931867049350053)
                    ·
                      refine ⟨984984265487225071753135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5253249415931867049350053 984984265487225071753135)
                      ·
                        rfl

theorem cell23_1918250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1918250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918250 prefixEnd_1918250 := by exact prefixLift 1918250
  have htrace : WordTrace (prefixWord ++ tailWord_1918250) baseStart_1918250 baseEnd_1918250 := by
    simpa [prefixWord, tailWord_1918250, baseEnd_1918250] using wordTrace_append hprefix tailTrace_1918250
  have hstable : (prefixWord ++ tailWord_1918250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918250).length < 2 ^ (prefixWord ++ tailWord_1918250).sum := by decide
  have hdescent : baseEnd_1918250 < baseStart_1918250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918266 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5]
def baseStart_1918266 : Nat := 118140960795 + 1918266 * 2 ^ 59
def prefixEnd_1918266 : Nat := 4983230072969 + 3 ^ 40 * 1918266 * 2
def baseEnd_1918266 : Nat := 984992481177697009153061

theorem tailTrace_1918266 : CollatzResearch.WordTrace tailWord_1918266 prefixEnd_1918266 984992481177697009153061 := by
  unfold tailWord_1918266
  simp only [CollatzResearch.WordTrace]
  refine ⟨17491227217114342648811663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46643272578971580396831101 17491227217114342648811663)
  ·
    refine ⟨26236840825671513973217495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17491227217114342648811663 26236840825671513973217495)
    ·
      refine ⟨39355261238507270959826243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26236840825671513973217495 39355261238507270959826243)
      ·
        refine ⟨59032891857760906439739365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39355261238507270959826243 59032891857760906439739365)
        ·
          refine ⟨11068667223330169957451131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59032891857760906439739365 11068667223330169957451131)
          ·
            refine ⟨16603000834995254936176697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11068667223330169957451131 16603000834995254936176697)
            ·
              refine ⟨12452250626246441202132523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16603000834995254936176697 12452250626246441202132523)
              ·
                refine ⟨18678375939369661803198785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12452250626246441202132523 18678375939369661803198785)
                ·
                  refine ⟨14008781954527246352399089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18678375939369661803198785 14008781954527246352399089)
                  ·
                    refine ⟨10506586465895434764299317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14008781954527246352399089 10506586465895434764299317)
                    ·
                      refine ⟨984992481177697009153061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10506586465895434764299317 984992481177697009153061)
                      ·
                        rfl

theorem cell23_1918266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_1918266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918266 prefixEnd_1918266 := by exact prefixLift 1918266
  have htrace : WordTrace (prefixWord ++ tailWord_1918266) baseStart_1918266 baseEnd_1918266 := by
    simpa [prefixWord, tailWord_1918266, baseEnd_1918266] using wordTrace_append hprefix tailTrace_1918266
  have hstable : (prefixWord ++ tailWord_1918266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918266).length < 2 ^ (prefixWord ++ tailWord_1918266).sum := by decide
  have hdescent : baseEnd_1918266 < baseStart_1918266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918270 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 4, 1, 3]
def baseStart_1918270 : Nat := 118140960795 + 1918270 * 2 ^ 59
def prefixEnd_1918270 : Nat := 4983230072969 + 3 ^ 40 * 1918270 * 2
def baseEnd_1918270 : Nat := 984994535100314993503043

theorem tailTrace_1918270 : CollatzResearch.WordTrace tailWord_1918270 prefixEnd_1918270 984994535100314993503043 := by
  unfold tailWord_1918270
  simp only [CollatzResearch.WordTrace]
  refine ⟨8745631845055359909799033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46643369840295252852261509 8745631845055359909799033)
  ·
    refine ⟨6559223883791519932349275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8745631845055359909799033 6559223883791519932349275)
    ·
      refine ⟨9838835825687279898523913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6559223883791519932349275 9838835825687279898523913)
      ·
        refine ⟨7379126869265459923892935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9838835825687279898523913 7379126869265459923892935)
        ·
          refine ⟨11068690303898189885839403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7379126869265459923892935 11068690303898189885839403)
          ·
            refine ⟨16603035455847284828759105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11068690303898189885839403 16603035455847284828759105)
            ·
              refine ⟨12452276591885463621569329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16603035455847284828759105 12452276591885463621569329)
              ·
                refine ⟨9339207443914097716176997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12452276591885463621569329 9339207443914097716176997)
                ·
                  refine ⟨1751101395733893321783187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9339207443914097716176997 1751101395733893321783187)
                  ·
                    refine ⟨2626652093600839982674781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1751101395733893321783187 2626652093600839982674781)
                    ·
                      refine ⟨984994535100314993503043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2626652093600839982674781 984994535100314993503043)
                      ·
                        rfl

theorem cell23_1918270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_1918270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918270 prefixEnd_1918270 := by exact prefixLift 1918270
  have htrace : WordTrace (prefixWord ++ tailWord_1918270) baseStart_1918270 baseEnd_1918270 := by
    simpa [prefixWord, tailWord_1918270, baseEnd_1918270] using wordTrace_append hprefix tailTrace_1918270
  have hstable : (prefixWord ++ tailWord_1918270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918270).length < 2 ^ (prefixWord ++ tailWord_1918270).sum := by decide
  have hdescent : baseEnd_1918270 < baseStart_1918270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918286 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 4, 6]
def baseStart_1918286 : Nat := 118140960795 + 1918286 * 2 ^ 59
def prefixEnd_1918286 : Nat := 4983230072969 + 3 ^ 40 * 1918286 * 2
def baseEnd_1918286 : Nat := 328334250263595643634323

theorem tailTrace_1918286 : CollatzResearch.WordTrace tailWord_1918286 prefixEnd_1918286 328334250263595643634323 := by
  unfold tailWord_1918286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8745704791048114251371839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46643758885589942673983141 8745704791048114251371839)
  ·
    refine ⟨13118557186572171377057759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8745704791048114251371839 13118557186572171377057759)
    ·
      refine ⟨19677835779858257065586639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13118557186572171377057759 19677835779858257065586639)
      ·
        refine ⟨29516753669787385598379959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19677835779858257065586639 29516753669787385598379959)
        ·
          refine ⟨44275130504681078397569939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29516753669787385598379959 44275130504681078397569939)
          ·
            refine ⟨66412695757021617596354909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44275130504681078397569939 66412695757021617596354909)
            ·
              refine ⟨24904760908883106598633091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66412695757021617596354909 24904760908883106598633091)
              ·
                refine ⟨37357141363324659897949637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24904760908883106598633091 37357141363324659897949637)
                ·
                  refine ⟨7004464005623373730865557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37357141363324659897949637 7004464005623373730865557)
                  ·
                    refine ⟨328334250263595643634323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7004464005623373730865557 328334250263595643634323)
                    ·
                      rfl

theorem cell23_1918286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_1918286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918286 prefixEnd_1918286 := by exact prefixLift 1918286
  have htrace : WordTrace (prefixWord ++ tailWord_1918286) baseStart_1918286 baseEnd_1918286 := by
    simpa [prefixWord, tailWord_1918286, baseEnd_1918286] using wordTrace_append hprefix tailTrace_1918286
  have hstable : (prefixWord ++ tailWord_1918286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918286).length < 2 ^ (prefixWord ++ tailWord_1918286).sum := by decide
  have hdescent : baseEnd_1918286 < baseStart_1918286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918301 : List Nat := [1, 4, 5, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_1918301 : Nat := 118140960795 + 1918301 * 2 ^ 59
def prefixEnd_1918301 : Nat := 4983230072969 + 3 ^ 40 * 1918301 * 2
def baseEnd_1918301 : Nat := 985010453000604372215401

theorem tailTrace_1918301 : CollatzResearch.WordTrace tailWord_1918301 prefixEnd_1918301 985010453000604372215401 := by
  unfold tailWord_1918301
  simp only [CollatzResearch.WordTrace]
  refine ⟨69966185423330571572770757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46644123615553714381847171 69966185423330571572770757)
  ·
    refine ⟨13118659766874482169894517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69966185423330571572770757 13118659766874482169894517)
    ·
      refine ⟨1229874353144482703427611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13118659766874482169894517 1229874353144482703427611)
      ·
        refine ⟨1844811529716724055141417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1229874353144482703427611 1844811529716724055141417)
        ·
          refine ⟨1383608647287543041356063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1844811529716724055141417 1383608647287543041356063)
          ·
            refine ⟨2075412970931314562034095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383608647287543041356063 2075412970931314562034095)
            ·
              refine ⟨3113119456396971843051143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2075412970931314562034095 3113119456396971843051143)
              ·
                refine ⟨4669679184595457764576715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3113119456396971843051143 4669679184595457764576715)
                ·
                  refine ⟨7004518776893186646865073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4669679184595457764576715 7004518776893186646865073)
                  ·
                    refine ⟨5253389082669889985148805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7004518776893186646865073 5253389082669889985148805)
                    ·
                      refine ⟨985010453000604372215401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5253389082669889985148805 985010453000604372215401)
                      ·
                        rfl

theorem cell23_1918301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_1918301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918301 prefixEnd_1918301 := by exact prefixLift 1918301
  have htrace : WordTrace (prefixWord ++ tailWord_1918301) baseStart_1918301 baseEnd_1918301 := by
    simpa [prefixWord, tailWord_1918301, baseEnd_1918301] using wordTrace_append hprefix tailTrace_1918301
  have hstable : (prefixWord ++ tailWord_1918301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918301).length < 2 ^ (prefixWord ++ tailWord_1918301).sum := by decide
  have hdescent : baseEnd_1918301 < baseStart_1918301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918314 : List Nat := [3, 1, 3, 3, 2, 1, 2, 2, 1, 3, 2]
def baseStart_1918314 : Nat := 118140960795 + 1918314 * 2 ^ 59
def prefixEnd_1918314 : Nat := 4983230072969 + 3 ^ 40 * 1918314 * 2
def baseEnd_1918314 : Nat := 985017128249112821352841

theorem tailTrace_1918314 : CollatzResearch.WordTrace tailWord_1918314 prefixEnd_1918314 985017128249112821352841 := by
  unfold tailWord_1918314
  simp only [CollatzResearch.WordTrace]
  refine ⟨17491664893070868698248499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46644439714855649861995997 17491664893070868698248499)
  ·
    refine ⟨26237497339606303047372749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17491664893070868698248499 26237497339606303047372749)
    ·
      refine ⟨9839061502352363642764781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26237497339606303047372749 9839061502352363642764781)
      ·
        refine ⟨3689648063382136366036793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9839061502352363642764781 3689648063382136366036793)
        ·
          refine ⟨2767236047536602274527595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3689648063382136366036793 2767236047536602274527595)
          ·
            refine ⟨4150854071304903411791393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2767236047536602274527595 4150854071304903411791393)
            ·
              refine ⟨3113140553478677558843545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4150854071304903411791393 3113140553478677558843545)
              ·
                refine ⟨2334855415109008169132659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3113140553478677558843545 2334855415109008169132659)
                ·
                  refine ⟨3502283122663512253698989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2334855415109008169132659 3502283122663512253698989)
                  ·
                    refine ⟨1313356170998817095137121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3502283122663512253698989 1313356170998817095137121)
                    ·
                      refine ⟨985017128249112821352841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1313356170998817095137121 985017128249112821352841)
                      ·
                        rfl

theorem cell23_1918314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_1918314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918314 prefixEnd_1918314 := by exact prefixLift 1918314
  have htrace : WordTrace (prefixWord ++ tailWord_1918314) baseStart_1918314 baseEnd_1918314 := by
    simpa [prefixWord, tailWord_1918314, baseEnd_1918314] using wordTrace_append hprefix tailTrace_1918314
  have hstable : (prefixWord ++ tailWord_1918314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918314).length < 2 ^ (prefixWord ++ tailWord_1918314).sum := by decide
  have hdescent : baseEnd_1918314 < baseStart_1918314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918353 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 1, 7, 2]
def baseStart_1918353 : Nat := 118140960795 + 1918353 * 2 ^ 59
def prefixEnd_1918353 : Nat := 4983230072969 + 3 ^ 40 * 1918353 * 2
def baseEnd_1918353 : Nat := 985037153994638168765161

theorem tailTrace_1918353 : CollatzResearch.WordTrace tailWord_1918353 prefixEnd_1918353 985037153994638168765161 := by
  unfold tailWord_1918353
  simp only [CollatzResearch.WordTrace]
  refine ⟨69968082019142184453663713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46645388012761456302442475 69968082019142184453663713)
  ·
    refine ⟨52476061514356638340247785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69968082019142184453663713 52476061514356638340247785)
    ·
      refine ⟨39357046135767478755185839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52476061514356638340247785 39357046135767478755185839)
      ·
        refine ⟨59035569203651218132778759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39357046135767478755185839 59035569203651218132778759)
        ·
          refine ⟨88553353805476827199168139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59035569203651218132778759 88553353805476827199168139)
          ·
            refine ⟨132830030708215240798752209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88553353805476827199168139 132830030708215240798752209)
            ·
              refine ⟨99622523031161430599064157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132830030708215240798752209 99622523031161430599064157)
              ·
                refine ⟨37358446136685536474649059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99622523031161430599064157 37358446136685536474649059)
                ·
                  refine ⟨56037669205028304711973589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37358446136685536474649059 56037669205028304711973589)
                  ·
                    refine ⟨1313382871992850891686881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56037669205028304711973589 1313382871992850891686881)
                    ·
                      refine ⟨985037153994638168765161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1313382871992850891686881 985037153994638168765161)
                      ·
                        rfl

theorem cell23_1918353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 7, 2].length) (baseStart_1918353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918353 prefixEnd_1918353 := by exact prefixLift 1918353
  have htrace : WordTrace (prefixWord ++ tailWord_1918353) baseStart_1918353 baseEnd_1918353 := by
    simpa [prefixWord, tailWord_1918353, baseEnd_1918353] using wordTrace_append hprefix tailTrace_1918353
  have hstable : (prefixWord ++ tailWord_1918353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918353).length < 2 ^ (prefixWord ++ tailWord_1918353).sum := by decide
  have hdescent : baseEnd_1918353 < baseStart_1918353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918437 : List Nat := [1, 3, 1, 5, 1, 1, 3, 1, 2, 2, 3]
def baseStart_1918437 : Nat := 118140960795 + 1918437 * 2 ^ 59
def prefixEnd_1918437 : Nat := 4983230072969 + 3 ^ 40 * 1918437 * 2
def baseEnd_1918437 : Nat := 985080286369615840114775

theorem tailTrace_1918437 : CollatzResearch.WordTrace tailWord_1918437 prefixEnd_1918437 985080286369615840114775 := by
  unfold tailWord_1918437
  simp only [CollatzResearch.WordTrace]
  refine ⟨69971145750837866799721565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46647430500558577866481043 69971145750837866799721565)
  ·
    refine ⟨26239179656564200049895587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69971145750837866799721565 26239179656564200049895587)
    ·
      refine ⟨39358769484846300074843381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26239179656564200049895587 39358769484846300074843381)
      ·
        refine ⟨3689884639204340632016567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39358769484846300074843381 3689884639204340632016567)
        ·
          refine ⟨5534826958806510948024851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3689884639204340632016567 5534826958806510948024851)
          ·
            refine ⟨8302240438209766422037277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5534826958806510948024851 8302240438209766422037277)
            ·
              refine ⟨3113340164328662408263979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8302240438209766422037277 3113340164328662408263979)
              ·
                refine ⟨4670010246492993612395969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3113340164328662408263979 4670010246492993612395969)
                ·
                  refine ⟨3502507684869745209296977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4670010246492993612395969 3502507684869745209296977)
                  ·
                    refine ⟨2626880763652308906972733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3502507684869745209296977 2626880763652308906972733)
                    ·
                      refine ⟨985080286369615840114775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2626880763652308906972733 985080286369615840114775)
                      ·
                        rfl

theorem cell23_1918437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_1918437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918437 prefixEnd_1918437 := by exact prefixLift 1918437
  have htrace : WordTrace (prefixWord ++ tailWord_1918437) baseStart_1918437 baseEnd_1918437 := by
    simpa [prefixWord, tailWord_1918437, baseEnd_1918437] using wordTrace_append hprefix tailTrace_1918437
  have hstable : (prefixWord ++ tailWord_1918437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918437).length < 2 ^ (prefixWord ++ tailWord_1918437).sum := by decide
  have hdescent : baseEnd_1918437 < baseStart_1918437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918490 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2]
def baseStart_1918490 : Nat := 118140960795 + 1918490 * 2 ^ 59
def prefixEnd_1918490 : Nat := 4983230072969 + 3 ^ 40 * 1918490 * 2
def baseEnd_1918490 : Nat := 985107500844304132752031

theorem tailTrace_1918490 : CollatzResearch.WordTrace tailWord_1918490 prefixEnd_1918490 985107500844304132752031 := by
  unfold tailWord_1918490
  simp only [CollatzResearch.WordTrace]
  refine ⟨17493269704911464212850231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46648719213097237900933949 17493269704911464212850231)
  ·
    refine ⟨26239904557367196319275347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17493269704911464212850231 26239904557367196319275347)
    ·
      refine ⟨39359856836050794478913021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26239904557367196319275347 39359856836050794478913021)
      ·
        refine ⟨14759946313519047929592383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39359856836050794478913021 14759946313519047929592383)
        ·
          refine ⟨22139919470278571894388575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14759946313519047929592383 22139919470278571894388575)
          ·
            refine ⟨33209879205417857841582863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22139919470278571894388575 33209879205417857841582863)
            ·
              refine ⟨49814818808126786762374295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33209879205417857841582863 49814818808126786762374295)
              ·
                refine ⟨74722228212190180143561443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49814818808126786762374295 74722228212190180143561443)
                ·
                  refine ⟨112083342318285270215342165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74722228212190180143561443 112083342318285270215342165)
                  ·
                    refine ⟨1313476667792405510336041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112083342318285270215342165 1313476667792405510336041)
                    ·
                      refine ⟨985107500844304132752031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1313476667792405510336041 985107500844304132752031)
                      ·
                        rfl

theorem cell23_1918490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_1918490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918490 prefixEnd_1918490 := by exact prefixLift 1918490
  have htrace : WordTrace (prefixWord ++ tailWord_1918490) baseStart_1918490 baseEnd_1918490 := by
    simpa [prefixWord, tailWord_1918490, baseEnd_1918490] using wordTrace_append hprefix tailTrace_1918490
  have hstable : (prefixWord ++ tailWord_1918490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918490).length < 2 ^ (prefixWord ++ tailWord_1918490).sum := by decide
  have hdescent : baseEnd_1918490 < baseStart_1918490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918518 : List Nat := [5, 1, 2, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_1918518 : Nat := 118140960795 + 1918518 * 2 ^ 59
def prefixEnd_1918518 : Nat := 4983230072969 + 3 ^ 40 * 1918518 * 2
def baseEnd_1918518 : Nat := 985121878302630023201903

theorem tailTrace_1918518 : CollatzResearch.WordTrace tailWord_1918518 prefixEnd_1918518 985121878302630023201903 := by
  unfold tailWord_1918518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4373381253971526102088763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46649400042362945088946805 4373381253971526102088763)
  ·
    refine ⟨6560071880957289153133145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4373381253971526102088763 6560071880957289153133145)
    ·
      refine ⟨4920053910717966864849859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6560071880957289153133145 4920053910717966864849859)
      ·
        refine ⟨7380080866076950297274789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4920053910717966864849859 7380080866076950297274789)
        ·
          refine ⟨1383765162389428180739023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7380080866076950297274789 1383765162389428180739023)
          ·
            refine ⟨2075647743584142271108535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1383765162389428180739023 2075647743584142271108535)
            ·
              refine ⟨3113471615376213406662803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2075647743584142271108535 3113471615376213406662803)
              ·
                refine ⟨4670207423064320109994205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3113471615376213406662803 4670207423064320109994205)
                ·
                  refine ⟨1751327783649120041247827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4670207423064320109994205 1751327783649120041247827)
                  ·
                    refine ⟨2626991675473680061871741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1751327783649120041247827 2626991675473680061871741)
                    ·
                      refine ⟨985121878302630023201903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2626991675473680061871741 985121878302630023201903)
                      ·
                        rfl

theorem cell23_1918518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_1918518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918518 prefixEnd_1918518 := by exact prefixLift 1918518
  have htrace : WordTrace (prefixWord ++ tailWord_1918518) baseStart_1918518 baseEnd_1918518 := by
    simpa [prefixWord, tailWord_1918518, baseEnd_1918518] using wordTrace_append hprefix tailTrace_1918518
  have hstable : (prefixWord ++ tailWord_1918518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918518).length < 2 ^ (prefixWord ++ tailWord_1918518).sum := by decide
  have hdescent : baseEnd_1918518 < baseStart_1918518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918533 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 2, 2, 6]
def baseStart_1918533 : Nat := 118140960795 + 1918533 * 2 ^ 59
def prefixEnd_1918533 : Nat := 4983230072969 + 3 ^ 40 * 1918533 * 2
def baseEnd_1918533 : Nat := 985129580512447464514333

theorem tailTrace_1918533 : CollatzResearch.WordTrace tailWord_1918533 prefixEnd_1918533 985129580512447464514333 := by
  unfold tailWord_1918533
  simp only [CollatzResearch.WordTrace]
  refine ⟨69974647158490075195216253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46649764772326716796810835 69974647158490075195216253)
  ·
    refine ⟨26240492684433778198206095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69974647158490075195216253 26240492684433778198206095)
    ·
      refine ⟨39360739026650667297309143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26240492684433778198206095 39360739026650667297309143)
      ·
        refine ⟨59041108539976000945963715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39360739026650667297309143 59041108539976000945963715)
        ·
          refine ⟨88561662809964001418945573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59041108539976000945963715 88561662809964001418945573)
          ·
            refine ⟨16605311776868250266052295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88561662809964001418945573 16605311776868250266052295)
            ·
              refine ⟨24907967665302375399078443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16605311776868250266052295 24907967665302375399078443)
              ·
                refine ⟨37361951497953563098617665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24907967665302375399078443 37361951497953563098617665)
                ·
                  refine ⟨28021463623465172323963249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37361951497953563098617665 28021463623465172323963249)
                  ·
                    refine ⟨21016097717598879242972437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28021463623465172323963249 21016097717598879242972437)
                    ·
                      refine ⟨985129580512447464514333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21016097717598879242972437 985129580512447464514333)
                      ·
                        rfl

theorem cell23_1918533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_1918533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918533 prefixEnd_1918533 := by exact prefixLift 1918533
  have htrace : WordTrace (prefixWord ++ tailWord_1918533) baseStart_1918533 baseEnd_1918533 := by
    simpa [prefixWord, tailWord_1918533, baseEnd_1918533] using wordTrace_append hprefix tailTrace_1918533
  have hstable : (prefixWord ++ tailWord_1918533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918533).length < 2 ^ (prefixWord ++ tailWord_1918533).sum := by decide
  have hdescent : baseEnd_1918533 < baseStart_1918533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918541 : List Nat := [1, 6, 1, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_1918541 : Nat := 118140960795 + 1918541 * 2 ^ 59
def prefixEnd_1918541 : Nat := 4983230072969 + 3 ^ 40 * 1918541 * 2
def baseEnd_1918541 : Nat := 985133688357683433214297

theorem tailTrace_1918541 : CollatzResearch.WordTrace tailWord_1918541 prefixEnd_1918541 985133688357683433214297 := by
  unfold tailWord_1918541
  simp only [CollatzResearch.WordTrace]
  refine ⟨69974938942461092561507477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46649959294974061707671651 69974938942461092561507477)
  ·
    refine ⟨3280075262927863713820663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 69974938942461092561507477 3280075262927863713820663)
    ·
      refine ⟨4920112894391795570730995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3280075262927863713820663 4920112894391795570730995)
      ·
        refine ⟨7380169341587693356096493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4920112894391795570730995 7380169341587693356096493)
        ·
          refine ⟨2767563503095385008536185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7380169341587693356096493 2767563503095385008536185)
          ·
            refine ⟨2075672627321538756402139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2767563503095385008536185 2075672627321538756402139)
            ·
              refine ⟨3113508940982308134603209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2075672627321538756402139 3113508940982308134603209)
              ·
                refine ⟨2335131705736731100952407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3113508940982308134603209 2335131705736731100952407)
                ·
                  refine ⟨3502697558605096651428611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2335131705736731100952407 3502697558605096651428611)
                  ·
                    refine ⟨5254046337907644977142917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3502697558605096651428611 5254046337907644977142917)
                    ·
                      refine ⟨985133688357683433214297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5254046337907644977142917 985133688357683433214297)
                      ·
                        rfl

theorem cell23_1918541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_1918541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918541 prefixEnd_1918541 := by exact prefixLift 1918541
  have htrace : WordTrace (prefixWord ++ tailWord_1918541) baseStart_1918541 baseEnd_1918541 := by
    simpa [prefixWord, tailWord_1918541, baseEnd_1918541] using wordTrace_append hprefix tailTrace_1918541
  have hstable : (prefixWord ++ tailWord_1918541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918541).length < 2 ^ (prefixWord ++ tailWord_1918541).sum := by decide
  have hdescent : baseEnd_1918541 < baseStart_1918541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918553 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 1, 4, 5]
def baseStart_1918553 : Nat := 118140960795 + 1918553 * 2 ^ 59
def prefixEnd_1918553 : Nat := 4983230072969 + 3 ^ 40 * 1918553 * 2
def baseEnd_1918553 : Nat := 985139850125537386264241

theorem tailTrace_1918553 : CollatzResearch.WordTrace tailWord_1918553 prefixEnd_1918553 985139850125537386264241 := by
  unfold tailWord_1918553
  simp only [CollatzResearch.WordTrace]
  refine ⟨69975376618417618610944313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46650251078945079073962875 69975376618417618610944313)
  ·
    refine ⟨52481532463813213958208235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69975376618417618610944313 52481532463813213958208235)
    ·
      refine ⟨78722298695719820937312353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52481532463813213958208235 78722298695719820937312353)
      ·
        refine ⟨59041724021789865702984265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78722298695719820937312353 59041724021789865702984265)
        ·
          refine ⟨44281293016342399277238199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59041724021789865702984265 44281293016342399277238199)
          ·
            refine ⟨66421939524513598915857299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44281293016342399277238199 66421939524513598915857299)
            ·
              refine ⟨99632909286770398373785949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66421939524513598915857299 99632909286770398373785949)
              ·
                refine ⟨37362340982538899390169731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99632909286770398373785949 37362340982538899390169731)
                ·
                  refine ⟨56043511473808349085254597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37362340982538899390169731 56043511473808349085254597)
                  ·
                    refine ⟨10508158401339065453485237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56043511473808349085254597 10508158401339065453485237)
                    ·
                      refine ⟨985139850125537386264241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10508158401339065453485237 985139850125537386264241)
                      ·
                        rfl

theorem cell23_1918553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_1918553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918553 prefixEnd_1918553 := by exact prefixLift 1918553
  have htrace : WordTrace (prefixWord ++ tailWord_1918553) baseStart_1918553 baseEnd_1918553 := by
    simpa [prefixWord, tailWord_1918553, baseEnd_1918553] using wordTrace_append hprefix tailTrace_1918553
  have hstable : (prefixWord ++ tailWord_1918553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918553).length < 2 ^ (prefixWord ++ tailWord_1918553).sum := by decide
  have hdescent : baseEnd_1918553 < baseStart_1918553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918637 : List Nat := [1, 5, 2, 1, 1, 1, 4, 1, 7]
def baseStart_1918637 : Nat := 118140960795 + 1918637 * 2 ^ 59
def prefixEnd_1918637 : Nat := 4983230072969 + 3 ^ 40 * 1918637 * 2
def baseEnd_1918637 : Nat := 109464775833390561957095

theorem tailTrace_1918637 : CollatzResearch.WordTrace tailWord_1918637 prefixEnd_1918637 109464775833390561957095 := by
  unfold tailWord_1918637
  simp only [CollatzResearch.WordTrace]
  refine ⟨69978440350113300957002165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46652293566742200638001443 69978440350113300957002165)
  ·
    refine ⟨6560478782823121964718953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69978440350113300957002165 6560478782823121964718953)
    ·
      refine ⟨4920359087117341473539215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6560478782823121964718953 4920359087117341473539215)
      ·
        refine ⟨7380538630676012210308823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4920359087117341473539215 7380538630676012210308823)
        ·
          refine ⟨11070807946014018315463235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7380538630676012210308823 11070807946014018315463235)
          ·
            refine ⟨16606211919021027473194853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11070807946014018315463235 16606211919021027473194853)
            ·
              refine ⟨3113664734816442651224035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16606211919021027473194853 3113664734816442651224035)
              ·
                refine ⟨4670497102224663976836053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3113664734816442651224035 4670497102224663976836053)
                ·
                  refine ⟨109464775833390561957095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4670497102224663976836053 109464775833390561957095)
                  ·
                    rfl

theorem cell23_1918637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_1918637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918637 prefixEnd_1918637 := by exact prefixLift 1918637
  have htrace : WordTrace (prefixWord ++ tailWord_1918637) baseStart_1918637 baseEnd_1918637 := by
    simpa [prefixWord, tailWord_1918637, baseEnd_1918637] using wordTrace_append hprefix tailTrace_1918637
  have hstable : (prefixWord ++ tailWord_1918637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918637).length < 2 ^ (prefixWord ++ tailWord_1918637).sum := by decide
  have hdescent : baseEnd_1918637 < baseStart_1918637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918647 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 3]
def baseStart_1918647 : Nat := 118140960795 + 1918647 * 2 ^ 59
def prefixEnd_1918647 : Nat := 4983230072969 + 3 ^ 40 * 1918647 * 2
def baseEnd_1918647 : Nat := 985188117307060018488809

theorem tailTrace_1918647 : CollatzResearch.WordTrace tailWord_1918647 prefixEnd_1918647 985188117307060018488809 := by
  unfold tailWord_1918647
  simp only [CollatzResearch.WordTrace]
  refine ⟨69978805080077072664866195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46652536720051381776577463 69978805080077072664866195)
  ·
    refine ⟨104968207620115608997299293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69978805080077072664866195 104968207620115608997299293)
    ·
      refine ⟨39363077857543353373987235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104968207620115608997299293 39363077857543353373987235)
      ·
        refine ⟨59044616786315030060980853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39363077857543353373987235 59044616786315030060980853)
        ·
          refine ⟨5535432823717034068216955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59044616786315030060980853 5535432823717034068216955)
          ·
            refine ⟨8303149235575551102325433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5535432823717034068216955 8303149235575551102325433)
            ·
              refine ⟨6227361926681663326744075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8303149235575551102325433 6227361926681663326744075)
              ·
                refine ⟨9341042890022494990116113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6227361926681663326744075 9341042890022494990116113)
                ·
                  refine ⟨7005782167516871242587085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9341042890022494990116113 7005782167516871242587085)
                  ·
                    refine ⟨2627168312818826715970157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7005782167516871242587085 2627168312818826715970157)
                    ·
                      refine ⟨985188117307060018488809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2627168312818826715970157 985188117307060018488809)
                      ·
                        rfl

theorem cell23_1918647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_1918647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918647 prefixEnd_1918647 := by exact prefixLift 1918647
  have htrace : WordTrace (prefixWord ++ tailWord_1918647) baseStart_1918647 baseEnd_1918647 := by
    simpa [prefixWord, tailWord_1918647, baseEnd_1918647] using wordTrace_append hprefix tailTrace_1918647
  have hstable : (prefixWord ++ tailWord_1918647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918647).length < 2 ^ (prefixWord ++ tailWord_1918647).sum := by decide
  have hdescent : baseEnd_1918647 < baseStart_1918647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918650 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 1, 7]
def baseStart_1918650 : Nat := 118140960795 + 1918650 * 2 ^ 59
def prefixEnd_1918650 : Nat := 4983230072969 + 3 ^ 40 * 1918650 * 2
def baseEnd_1918650 : Nat := 328396552583007835583765

theorem tailTrace_1918650 : CollatzResearch.WordTrace tailWord_1918650 prefixEnd_1918650 328396552583007835583765 := by
  unfold tailWord_1918650
  simp only [CollatzResearch.WordTrace]
  refine ⟨17494728624766551044306351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46652609666044136118150269 17494728624766551044306351)
  ·
    refine ⟨26242092937149826566459527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17494728624766551044306351 26242092937149826566459527)
    ·
      refine ⟨39363139405724739849689291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26242092937149826566459527 39363139405724739849689291)
      ·
        refine ⟨59044709108587109774533937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39363139405724739849689291 59044709108587109774533937)
        ·
          refine ⟨44283531831440332330900453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59044709108587109774533937 44283531831440332330900453)
          ·
            refine ⟨8303162218395062312043835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44283531831440332330900453 8303162218395062312043835)
            ·
              refine ⟨12454743327592593468065753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8303162218395062312043835 12454743327592593468065753)
              ·
                refine ⟨9341057495694445101049315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12454743327592593468065753 9341057495694445101049315)
                ·
                  refine ⟨14011586243541667651573973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9341057495694445101049315 14011586243541667651573973)
                  ·
                    refine ⟨328396552583007835583765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14011586243541667651573973 328396552583007835583765)
                    ·
                      rfl

theorem cell23_1918650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_1918650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918650 prefixEnd_1918650 := by exact prefixLift 1918650
  have htrace : WordTrace (prefixWord ++ tailWord_1918650) baseStart_1918650 baseEnd_1918650 := by
    simpa [prefixWord, tailWord_1918650, baseEnd_1918650] using wordTrace_append hprefix tailTrace_1918650
  have hstable : (prefixWord ++ tailWord_1918650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918650).length < 2 ^ (prefixWord ++ tailWord_1918650).sum := by decide
  have hdescent : baseEnd_1918650 < baseStart_1918650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918687 : List Nat := [1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 4]
def baseStart_1918687 : Nat := 118140960795 + 1918687 * 2 ^ 59
def prefixEnd_1918687 : Nat := 4983230072969 + 3 ^ 40 * 1918687 * 2
def baseEnd_1918687 : Nat := 985208656533239861988625

theorem tailTrace_1918687 : CollatzResearch.WordTrace tailWord_1918687 prefixEnd_1918687 985208656533239861988625 := by
  unfold tailWord_1918687
  simp only [CollatzResearch.WordTrace]
  refine ⟨69980263999932159496322315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46653509333288106330881543 69980263999932159496322315)
  ·
    refine ⟨104970395999898239244483473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69980263999932159496322315 104970395999898239244483473)
    ·
      refine ⟨78727796999923679433362605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104970395999898239244483473 78727796999923679433362605)
      ·
        refine ⟨29522923874971379787510977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78727796999923679433362605 29522923874971379787510977)
        ·
          refine ⟨22142192906228534840633233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29522923874971379787510977 22142192906228534840633233)
          ·
            refine ⟨16606644679671401130474925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22142192906228534840633233 16606644679671401130474925)
            ·
              refine ⟨6227491754876775423928097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16606644679671401130474925 6227491754876775423928097)
              ·
                refine ⟨4670618816157581567946073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6227491754876775423928097 4670618816157581567946073)
                ·
                  refine ⟨3502964112118186175959555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4670618816157581567946073 3502964112118186175959555)
                  ·
                    refine ⟨5254446168177279263939333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3502964112118186175959555 5254446168177279263939333)
                    ·
                      refine ⟨985208656533239861988625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5254446168177279263939333 985208656533239861988625)
                      ·
                        rfl

theorem cell23_1918687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_1918687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918687 prefixEnd_1918687 := by exact prefixLift 1918687
  have htrace : WordTrace (prefixWord ++ tailWord_1918687) baseStart_1918687 baseEnd_1918687 := by
    simpa [prefixWord, tailWord_1918687, baseEnd_1918687] using wordTrace_append hprefix tailTrace_1918687
  have hstable : (prefixWord ++ tailWord_1918687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918687).length < 2 ^ (prefixWord ++ tailWord_1918687).sum := by decide
  have hdescent : baseEnd_1918687 < baseStart_1918687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918700 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 6]
def baseStart_1918700 : Nat := 118140960795 + 1918700 * 2 ^ 59
def prefixEnd_1918700 : Nat := 4983230072969 + 3 ^ 40 * 1918700 * 2
def baseEnd_1918700 : Nat := 985215331781748311126065

theorem tailTrace_1918700 : CollatzResearch.WordTrace tailWord_1918700 prefixEnd_1918700 985215331781748311126065 := by
  unfold tailWord_1918700
  simp only [CollatzResearch.WordTrace]
  refine ⟨34990369074442531358272777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46653825432590041811030369 34990369074442531358272777)
  ·
    refine ⟨26242776805831898518704583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34990369074442531358272777 26242776805831898518704583)
    ·
      refine ⟨39364165208747847778056875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26242776805831898518704583 39364165208747847778056875)
      ·
        refine ⟨59046247813121771667085313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39364165208747847778056875 59046247813121771667085313)
        ·
          refine ⟨44284685859841328750313985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59046247813121771667085313 44284685859841328750313985)
          ·
            refine ⟨33213514394880996562735489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44284685859841328750313985 33213514394880996562735489)
            ·
              refine ⟨24910135796160747422051617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33213514394880996562735489 24910135796160747422051617)
              ·
                refine ⟨18682601847120560566538713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24910135796160747422051617 18682601847120560566538713)
                ·
                  refine ⟨14011951385340420424904035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18682601847120560566538713 14011951385340420424904035)
                  ·
                    refine ⟨21017927078010630637356053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14011951385340420424904035 21017927078010630637356053)
                    ·
                      refine ⟨985215331781748311126065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21017927078010630637356053 985215331781748311126065)
                      ·
                        rfl

theorem cell23_1918700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_1918700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918700 prefixEnd_1918700 := by exact prefixLift 1918700
  have htrace : WordTrace (prefixWord ++ tailWord_1918700) baseStart_1918700 baseEnd_1918700 := by
    simpa [prefixWord, tailWord_1918700, baseEnd_1918700] using wordTrace_append hprefix tailTrace_1918700
  have hstable : (prefixWord ++ tailWord_1918700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918700).length < 2 ^ (prefixWord ++ tailWord_1918700).sum := by decide
  have hdescent : baseEnd_1918700 < baseStart_1918700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918724 : List Nat := [2, 3, 2, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_1918724 : Nat := 118140960795 + 1918724 * 2 ^ 59
def prefixEnd_1918724 : Nat := 4983230072969 + 3 ^ 40 * 1918724 * 2
def baseEnd_1918724 : Nat := 985227655317456217225955

theorem tailTrace_1918724 : CollatzResearch.WordTrace tailWord_1918724 prefixEnd_1918724 985227655317456217225955 := by
  unfold tailWord_1918724
  simp only [CollatzResearch.WordTrace]
  refine ⟨34990806750399057407709613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46654409000532076543612817 34990806750399057407709613)
  ·
    refine ⟨13121552531399646527891105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34990806750399057407709613 13121552531399646527891105)
    ·
      refine ⟨9841164398549734895918329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13121552531399646527891105 9841164398549734895918329)
      ·
        refine ⟨7380873298912301171938747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9841164398549734895918329 7380873298912301171938747)
        ·
          refine ⟨11071309948368451757908121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7380873298912301171938747 11071309948368451757908121)
          ·
            refine ⟨8303482461276338818431091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11071309948368451757908121 8303482461276338818431091)
            ·
              refine ⟨12455223691914508227646637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8303482461276338818431091 12455223691914508227646637)
              ·
                refine ⟨4670708884467940585367489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12455223691914508227646637 4670708884467940585367489)
                ·
                  refine ⟨3503031663350955439025617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4670708884467940585367489 3503031663350955439025617)
                  ·
                    refine ⟨2627273747513216579269213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3503031663350955439025617 2627273747513216579269213)
                    ·
                      refine ⟨985227655317456217225955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2627273747513216579269213 985227655317456217225955)
                      ·
                        rfl

theorem cell23_1918724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_1918724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918724 prefixEnd_1918724 := by exact prefixLift 1918724
  have htrace : WordTrace (prefixWord ++ tailWord_1918724) baseStart_1918724 baseEnd_1918724 := by
    simpa [prefixWord, tailWord_1918724, baseEnd_1918724] using wordTrace_append hprefix tailTrace_1918724
  have hstable : (prefixWord ++ tailWord_1918724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918724).length < 2 ^ (prefixWord ++ tailWord_1918724).sum := by decide
  have hdescent : baseEnd_1918724 < baseStart_1918724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918757 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 3, 5]
def baseStart_1918757 : Nat := 118140960795 + 1918757 * 2 ^ 59
def prefixEnd_1918757 : Nat := 4983230072969 + 3 ^ 40 * 1918757 * 2
def baseEnd_1918757 : Nat := 328414866726351529371101

theorem tailTrace_1918757 : CollatzResearch.WordTrace tailWord_1918757 prefixEnd_1918757 328414866726351529371101 := by
  unfold tailWord_1918757
  simp only [CollatzResearch.WordTrace]
  refine ⟨69982817109678561451370525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46655211406452374300913683 69982817109678561451370525)
  ·
    refine ⟨26243556416129460544263947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69982817109678561451370525 26243556416129460544263947)
    ·
      refine ⟨39365334624194190816395921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26243556416129460544263947 39365334624194190816395921)
      ·
        refine ⟨29524000968145643112296941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39365334624194190816395921 29524000968145643112296941)
        ·
          refine ⟨11071500363054616167111353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29524000968145643112296941 11071500363054616167111353)
          ·
            refine ⟨8303625272290962125333515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11071500363054616167111353 8303625272290962125333515)
            ·
              refine ⟨12455437908436443188000273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8303625272290962125333515 12455437908436443188000273)
              ·
                refine ⟨9341578431327332391000205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12455437908436443188000273 9341578431327332391000205)
                ·
                  refine ⟨3503091911747749646625077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9341578431327332391000205 3503091911747749646625077)
                  ·
                    refine ⟨328414866726351529371101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3503091911747749646625077 328414866726351529371101)
                    ·
                      rfl

theorem cell23_1918757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_1918757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918757 prefixEnd_1918757 := by exact prefixLift 1918757
  have htrace : WordTrace (prefixWord ++ tailWord_1918757) baseStart_1918757 baseEnd_1918757 := by
    simpa [prefixWord, tailWord_1918757, baseEnd_1918757] using wordTrace_append hprefix tailTrace_1918757
  have hstable : (prefixWord ++ tailWord_1918757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918757).length < 2 ^ (prefixWord ++ tailWord_1918757).sum := by decide
  have hdescent : baseEnd_1918757 < baseStart_1918757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918771 : List Nat := [1, 1, 1, 2, 7, 1, 1, 2, 3, 1, 3]
def baseStart_1918771 : Nat := 118140960795 + 1918771 * 2 ^ 59
def prefixEnd_1918771 : Nat := 4983230072969 + 3 ^ 40 * 1918771 * 2
def baseEnd_1918771 : Nat := 985251788908217533338239

theorem tailTrace_1918771 : CollatzResearch.WordTrace tailWord_1918771 prefixEnd_1918771 985251788908217533338239 := by
  unfold tailWord_1918771
  simp only [CollatzResearch.WordTrace]
  refine ⟨69983327731627841842380167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46655551821085227894920111 69983327731627841842380167)
  ·
    refine ⟨104974991597441762763570251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69983327731627841842380167 104974991597441762763570251)
    ·
      refine ⟨157462487396162644145355377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104974991597441762763570251 157462487396162644145355377)
      ·
        refine ⟨118096865547121983109016533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157462487396162644145355377 118096865547121983109016533)
        ·
          refine ⟨2767895286260671479117575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 118096865547121983109016533 2767895286260671479117575)
          ·
            refine ⟨4151842929391007218676363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2767895286260671479117575 4151842929391007218676363)
            ·
              refine ⟨6227764394086510828014545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4151842929391007218676363 6227764394086510828014545)
              ·
                refine ⟨4670823295564883121010909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6227764394086510828014545 4670823295564883121010909)
                ·
                  refine ⟨1751558735836831170379091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4670823295564883121010909 1751558735836831170379091)
                  ·
                    refine ⟨2627338103755246755568637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1751558735836831170379091 2627338103755246755568637)
                    ·
                      refine ⟨985251788908217533338239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2627338103755246755568637 985251788908217533338239)
                      ·
                        rfl

theorem cell23_1918771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 1, 3].length) (baseStart_1918771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918771 prefixEnd_1918771 := by exact prefixLift 1918771
  have htrace : WordTrace (prefixWord ++ tailWord_1918771) baseStart_1918771 baseEnd_1918771 := by
    simpa [prefixWord, tailWord_1918771, baseEnd_1918771] using wordTrace_append hprefix tailTrace_1918771
  have hstable : (prefixWord ++ tailWord_1918771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918771).length < 2 ^ (prefixWord ++ tailWord_1918771).sum := by decide
  have hdescent : baseEnd_1918771 < baseStart_1918771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918781 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 1, 5, 2]
def baseStart_1918781 : Nat := 118140960795 + 1918781 * 2 ^ 59
def prefixEnd_1918781 : Nat := 4983230072969 + 3 ^ 40 * 1918781 * 2
def baseEnd_1918781 : Nat := 985256923714762494213193

theorem tailTrace_1918781 : CollatzResearch.WordTrace tailWord_1918781 prefixEnd_1918781 985256923714762494213193 := by
  unfold tailWord_1918781
  simp only [CollatzResearch.WordTrace]
  refine ⟨69983692461591613550244197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46655794974394409033496131 69983692461591613550244197)
  ·
    refine ⟨13121942336548427540670787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69983692461591613550244197 13121942336548427540670787)
    ·
      refine ⟨19682913504822641311006181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13121942336548427540670787 19682913504822641311006181)
      ·
        refine ⟨3690546282154245245813659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19682913504822641311006181 3690546282154245245813659)
        ·
          refine ⟨5535819423231367868720489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3690546282154245245813659 5535819423231367868720489)
          ·
            refine ⟨4151864567423525901540367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5535819423231367868720489 4151864567423525901540367)
            ·
              refine ⟨6227796851135288852310551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4151864567423525901540367 6227796851135288852310551)
              ·
                refine ⟨9341695276702933278465827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6227796851135288852310551 9341695276702933278465827)
                ·
                  refine ⟨14012542915054399917698741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9341695276702933278465827 14012542915054399917698741)
                  ·
                    refine ⟨1313675898286349992284257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14012542915054399917698741 1313675898286349992284257)
                    ·
                      refine ⟨985256923714762494213193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1313675898286349992284257 985256923714762494213193)
                      ·
                        rfl

theorem cell23_1918781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_1918781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918781 prefixEnd_1918781 := by exact prefixLift 1918781
  have htrace : WordTrace (prefixWord ++ tailWord_1918781) baseStart_1918781 baseEnd_1918781 := by
    simpa [prefixWord, tailWord_1918781, baseEnd_1918781] using wordTrace_append hprefix tailTrace_1918781
  have hstable : (prefixWord ++ tailWord_1918781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918781).length < 2 ^ (prefixWord ++ tailWord_1918781).sum := by decide
  have hdescent : baseEnd_1918781 < baseStart_1918781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918787 : List Nat := [1, 1, 1, 3, 1, 5, 2, 2, 1, 6]
def baseStart_1918787 : Nat := 118140960795 + 1918787 * 2 ^ 59
def prefixEnd_1918787 : Nat := 4983230072969 + 3 ^ 40 * 1918787 * 2
def baseEnd_1918787 : Nat := 328420001532896490246055

theorem tailTrace_1918787 : CollatzResearch.WordTrace tailWord_1918787 prefixEnd_1918787 328420001532896490246055 := by
  unfold tailWord_1918787
  simp only [CollatzResearch.WordTrace]
  refine ⟨69983911299569876574962615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46655940866379917716641743 69983911299569876574962615)
  ·
    refine ⟨104975866949354814862443923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69983911299569876574962615 104975866949354814862443923)
    ·
      refine ⟨157463800424032222293665885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104975866949354814862443923 157463800424032222293665885)
      ·
        refine ⟨59048925159012083360124707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157463800424032222293665885 59048925159012083360124707)
        ·
          refine ⟨88573387738518125040187061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59048925159012083360124707 88573387738518125040187061)
          ·
            refine ⟨8303755100486074222517537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88573387738518125040187061 8303755100486074222517537)
            ·
              refine ⟨6227816325364555666888153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8303755100486074222517537 6227816325364555666888153)
              ·
                refine ⟨4670862244023416750166115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6227816325364555666888153 4670862244023416750166115)
                ·
                  refine ⟨7006293366035125125249173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4670862244023416750166115 7006293366035125125249173)
                  ·
                    refine ⟨328420001532896490246055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7006293366035125125249173 328420001532896490246055)
                    ·
                      rfl

theorem cell23_1918787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 6].length) (baseStart_1918787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918787 prefixEnd_1918787 := by exact prefixLift 1918787
  have htrace : WordTrace (prefixWord ++ tailWord_1918787) baseStart_1918787 baseEnd_1918787 := by
    simpa [prefixWord, tailWord_1918787, baseEnd_1918787] using wordTrace_append hprefix tailTrace_1918787
  have hstable : (prefixWord ++ tailWord_1918787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918787).length < 2 ^ (prefixWord ++ tailWord_1918787).sum := by decide
  have hdescent : baseEnd_1918787 < baseStart_1918787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918794 : List Nat := [3, 1, 2, 1, 1, 1, 5, 3, 1, 1, 4]
def baseStart_1918794 : Nat := 118140960795 + 1918794 * 2 ^ 59
def prefixEnd_1918794 : Nat := 4983230072969 + 3 ^ 40 * 1918794 * 2
def baseEnd_1918794 : Nat := 985263598963270943350633

theorem tailTrace_1918794 : CollatzResearch.WordTrace tailWord_1918794 prefixEnd_1918794 985263598963270943350633 := by
  unfold tailWord_1918794
  simp only [CollatzResearch.WordTrace]
  refine ⟨17496041652636129192616859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46656111073696344513644957 17496041652636129192616859)
  ·
    refine ⟨26244062478954193788925289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17496041652636129192616859 26244062478954193788925289)
    ·
      refine ⟨19683046859215645341693967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26244062478954193788925289 19683046859215645341693967)
      ·
        refine ⟨29524570288823468012540951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19683046859215645341693967 29524570288823468012540951)
        ·
          refine ⟨44286855433235202018811427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29524570288823468012540951 44286855433235202018811427)
          ·
            refine ⟨66430283149852803028217141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44286855433235202018811427 66430283149852803028217141)
            ·
              refine ⟨6227839045298700283895357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66430283149852803028217141 6227839045298700283895357)
              ·
                refine ⟨2335439641987012606460759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6227839045298700283895357 2335439641987012606460759)
                ·
                  refine ⟨3503159462980518909691139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2335439641987012606460759 3503159462980518909691139)
                  ·
                    refine ⟨5254739194470778364536709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3503159462980518909691139 5254739194470778364536709)
                    ·
                      refine ⟨985263598963270943350633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5254739194470778364536709 985263598963270943350633)
                      ·
                        rfl

theorem cell23_1918794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_1918794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918794 prefixEnd_1918794 := by exact prefixLift 1918794
  have htrace : WordTrace (prefixWord ++ tailWord_1918794) baseStart_1918794 baseEnd_1918794 := by
    simpa [prefixWord, tailWord_1918794, baseEnd_1918794] using wordTrace_append hprefix tailTrace_1918794
  have hstable : (prefixWord ++ tailWord_1918794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918794).length < 2 ^ (prefixWord ++ tailWord_1918794).sum := by decide
  have hdescent : baseEnd_1918794 < baseStart_1918794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918857 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 2, 2, 5]
def baseStart_1918857 : Nat := 118140960795 + 1918857 * 2 ^ 59
def prefixEnd_1918857 : Nat := 4983230072969 + 3 ^ 40 * 1918857 * 2
def baseEnd_1918857 : Nat := 985295948244504196862843

theorem tailTrace_1918857 : CollatzResearch.WordTrace tailWord_1918857 prefixEnd_1918857 985295948244504196862843 := by
  unfold tailWord_1918857
  simp only [CollatzResearch.WordTrace]
  refine ⟨69986464409316278530010825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46657642939544185686673883 69986464409316278530010825)
  ·
    refine ⟨52489848306987208897508119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69986464409316278530010825 52489848306987208897508119)
    ·
      refine ⟨78734772460480813346262179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52489848306987208897508119 78734772460480813346262179)
      ·
        refine ⟨118102158690721220019393269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78734772460480813346262179 118102158690721220019393269)
        ·
          refine ⟨11072077377255114376818119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118102158690721220019393269 11072077377255114376818119)
          ·
            refine ⟨16608116065882671565227179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11072077377255114376818119 16608116065882671565227179)
            ·
              refine ⟨24912174098824007347840769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16608116065882671565227179 24912174098824007347840769)
              ·
                refine ⟨18684130574118005510880577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24912174098824007347840769 18684130574118005510880577)
                ·
                  refine ⟨14013097930588504133160433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18684130574118005510880577 14013097930588504133160433)
                  ·
                    refine ⟨10509823447941378099870325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14013097930588504133160433 10509823447941378099870325)
                    ·
                      refine ⟨985295948244504196862843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10509823447941378099870325 985295948244504196862843)
                      ·
                        rfl

theorem cell23_1918857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_1918857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918857 prefixEnd_1918857 := by exact prefixLift 1918857
  have htrace : WordTrace (prefixWord ++ tailWord_1918857) baseStart_1918857 baseEnd_1918857 := by
    simpa [prefixWord, tailWord_1918857, baseEnd_1918857] using wordTrace_append hprefix tailTrace_1918857
  have hstable : (prefixWord ++ tailWord_1918857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918857).length < 2 ^ (prefixWord ++ tailWord_1918857).sum := by decide
  have hdescent : baseEnd_1918857 < baseStart_1918857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918862 : List Nat := [4, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2]
def baseStart_1918862 : Nat := 118140960795 + 1918862 * 2 ^ 59
def prefixEnd_1918862 : Nat := 4983230072969 + 3 ^ 40 * 1918862 * 2
def baseEnd_1918862 : Nat := 985298515647776677300321

theorem tailTrace_1918862 : CollatzResearch.WordTrace tailWord_1918862 prefixEnd_1918862 985298515647776677300321 := by
  unfold tailWord_1918862
  simp only [CollatzResearch.WordTrace]
  refine ⟨8748330846787270547992855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46657764516198776255961893 8748330846787270547992855)
  ·
    refine ⟨13122496270180905821989283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8748330846787270547992855 13122496270180905821989283)
    ·
      refine ⟨19683744405271358732983925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13122496270180905821989283 19683744405271358732983925)
      ·
        refine ⟨1845351037994189881217243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19683744405271358732983925 1845351037994189881217243)
        ·
          refine ⟨2768026556991284821825865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1845351037994189881217243 2768026556991284821825865)
          ·
            refine ⟨2076019917743463616369399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2768026556991284821825865 2076019917743463616369399)
            ·
              refine ⟨3114029876615195424554099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2076019917743463616369399 3114029876615195424554099)
              ·
                refine ⟨4671044814922793136831149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3114029876615195424554099 4671044814922793136831149)
                ·
                  refine ⟨1751641805596047426311681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4671044814922793136831149 1751641805596047426311681)
                  ·
                    refine ⟨1313731354197035569733761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1751641805596047426311681 1313731354197035569733761)
                    ·
                      refine ⟨985298515647776677300321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1313731354197035569733761 985298515647776677300321)
                      ·
                        rfl

theorem cell23_1918862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_1918862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918862 prefixEnd_1918862 := by exact prefixLift 1918862
  have htrace : WordTrace (prefixWord ++ tailWord_1918862) baseStart_1918862 baseEnd_1918862 := by
    simpa [prefixWord, tailWord_1918862, baseEnd_1918862] using wordTrace_append hprefix tailTrace_1918862
  have hstable : (prefixWord ++ tailWord_1918862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918862).length < 2 ^ (prefixWord ++ tailWord_1918862).sum := by decide
  have hdescent : baseEnd_1918862 < baseStart_1918862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918872 : List Nat := [2, 1, 2, 6, 2, 1, 2, 1, 2, 4]
def baseStart_1918872 : Nat := 118140960795 + 1918872 * 2 ^ 59
def prefixEnd_1918872 : Nat := 4983230072969 + 3 ^ 40 * 1918872 * 2
def baseEnd_1918872 : Nat := 328434550151440546058425

theorem tailTrace_1918872 : CollatzResearch.WordTrace tailWord_1918872 prefixEnd_1918872 328434550151440546058425 := by
  unfold tailWord_1918872
  simp only [CollatzResearch.WordTrace]
  refine ⟨34993505752130968045903435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46658007669507957394537913 34993505752130968045903435)
  ·
    refine ⟨52490258628196452068855153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34993505752130968045903435 52490258628196452068855153)
    ·
      refine ⟨39367693971147339051641365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52490258628196452068855153 39367693971147339051641365)
      ·
        refine ⟨1845360654897531518045689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39367693971147339051641365 1845360654897531518045689)
        ·
          refine ⟨1384020491173148638534267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1845360654897531518045689 1384020491173148638534267)
          ·
            refine ⟨2076030736759722957801401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1384020491173148638534267 2076030736759722957801401)
            ·
              refine ⟨1557023052569792218351051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2076030736759722957801401 1557023052569792218351051)
              ·
                refine ⟨2335534578854688327526577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1557023052569792218351051 2335534578854688327526577)
                ·
                  refine ⟨1751650934141016245644933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2335534578854688327526577 1751650934141016245644933)
                  ·
                    refine ⟨328434550151440546058425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1751650934141016245644933 328434550151440546058425)
                    ·
                      rfl

theorem cell23_1918872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 2, 4].length) (baseStart_1918872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918872 prefixEnd_1918872 := by exact prefixLift 1918872
  have htrace : WordTrace (prefixWord ++ tailWord_1918872) baseStart_1918872 baseEnd_1918872 := by
    simpa [prefixWord, tailWord_1918872, baseEnd_1918872] using wordTrace_append hprefix tailTrace_1918872
  have hstable : (prefixWord ++ tailWord_1918872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918872).length < 2 ^ (prefixWord ++ tailWord_1918872).sum := by decide
  have hdescent : baseEnd_1918872 < baseStart_1918872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918901 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 3, 4, 2]
def baseStart_1918901 : Nat := 118140960795 + 1918901 * 2 ^ 59
def prefixEnd_1918901 : Nat := 4983230072969 + 3 ^ 40 * 1918901 * 2
def baseEnd_1918901 : Nat := 985318541393302024712641

theorem tailTrace_1918901 : CollatzResearch.WordTrace tailWord_1918901 prefixEnd_1918901 985318541393302024712641 := by
  unfold tailWord_1918901
  simp only [CollatzResearch.WordTrace]
  refine ⟨69988069221156874044612557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46658712814104582696408371 69988069221156874044612557)
  ·
    refine ⟨26245525957933827766729709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69988069221156874044612557 26245525957933827766729709)
    ·
      refine ⟨9842072234225185412523641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26245525957933827766729709 9842072234225185412523641)
      ·
        refine ⟨7381554175668889059392731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9842072234225185412523641 7381554175668889059392731)
        ·
          refine ⟨11072331263503333589089097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7381554175668889059392731 11072331263503333589089097)
          ·
            refine ⟨8304248447627500191816823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11072331263503333589089097 8304248447627500191816823)
            ·
              refine ⟨12456372671441250287725235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8304248447627500191816823 12456372671441250287725235)
              ·
                refine ⟨18684559007161875431587853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12456372671441250287725235 18684559007161875431587853)
                ·
                  refine ⟨7006709627685703286845445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18684559007161875431587853 7006709627685703286845445)
                  ·
                    refine ⟨1313758055191069366283521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7006709627685703286845445 1313758055191069366283521)
                    ·
                      refine ⟨985318541393302024712641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1313758055191069366283521 985318541393302024712641)
                      ·
                        rfl

theorem cell23_1918901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_1918901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918901 prefixEnd_1918901 := by exact prefixLift 1918901
  have htrace : WordTrace (prefixWord ++ tailWord_1918901) baseStart_1918901 baseEnd_1918901 := by
    simpa [prefixWord, tailWord_1918901, baseEnd_1918901] using wordTrace_append hprefix tailTrace_1918901
  have hstable : (prefixWord ++ tailWord_1918901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918901).length < 2 ^ (prefixWord ++ tailWord_1918901).sum := by decide
  have hdescent : baseEnd_1918901 < baseStart_1918901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918941 : List Nat := [1, 4, 3, 1, 3, 1, 1, 2, 7]
def baseStart_1918941 : Nat := 118140960795 + 1918941 * 2 ^ 59
def prefixEnd_1918941 : Nat := 4983230072969 + 3 ^ 40 * 1918941 * 2
def baseEnd_1918941 : Nat := 109482120068831318690273

theorem tailTrace_1918941 : CollatzResearch.WordTrace tailWord_1918941 prefixEnd_1918941 109482120068831318690273 := by
  unfold tailWord_1918941
  simp only [CollatzResearch.WordTrace]
  refine ⟨69989528141011960876068677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46659685427341307250712451 69989528141011960876068677)
  ·
    refine ⟨13123036526439742664262877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69989528141011960876068677 13123036526439742664262877)
    ·
      refine ⟨4921138697414903499098579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13123036526439742664262877 4921138697414903499098579)
      ·
        refine ⟨7381708046122355248647869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4921138697414903499098579 7381708046122355248647869)
        ·
          refine ⟨2768140517295883218242951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7381708046122355248647869 2768140517295883218242951)
          ·
            refine ⟨4152210775943824827364427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2768140517295883218242951 4152210775943824827364427)
            ·
              refine ⟨6228316163915737241046641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4152210775943824827364427 6228316163915737241046641)
              ·
                refine ⟨4671237122936802930784981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6228316163915737241046641 4671237122936802930784981)
                ·
                  refine ⟨109482120068831318690273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4671237122936802930784981 109482120068831318690273)
                  ·
                    rfl

theorem cell23_1918941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_1918941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918941 prefixEnd_1918941 := by exact prefixLift 1918941
  have htrace : WordTrace (prefixWord ++ tailWord_1918941) baseStart_1918941 baseEnd_1918941 := by
    simpa [prefixWord, tailWord_1918941, baseEnd_1918941] using wordTrace_append hprefix tailTrace_1918941
  have hstable : (prefixWord ++ tailWord_1918941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918941).length < 2 ^ (prefixWord ++ tailWord_1918941).sum := by decide
  have hdescent : baseEnd_1918941 < baseStart_1918941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918954 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 1, 7]
def baseStart_1918954 : Nat := 118140960795 + 1918954 * 2 ^ 59
def prefixEnd_1918954 : Nat := 4983230072969 + 3 ^ 40 * 1918954 * 2
def baseEnd_1918954 : Nat := 328448585289330105783299

theorem tailTrace_1918954 : CollatzResearch.WordTrace tailWord_1918954 prefixEnd_1918954 328448585289330105783299 := by
  unfold tailWord_1918954
  simp only [CollatzResearch.WordTrace]
  refine ⟨17497500572491216024072979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46660001526643242730861277 17497500572491216024072979)
  ·
    refine ⟨26246250858736824036109469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17497500572491216024072979 26246250858736824036109469)
    ·
      refine ⟨9842344072026309013541051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26246250858736824036109469 9842344072026309013541051)
      ·
        refine ⟨14763516108039463520311577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9842344072026309013541051 14763516108039463520311577)
        ·
          refine ⟨11072637081029597640233683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14763516108039463520311577 11072637081029597640233683)
          ·
            refine ⟨16608955621544396460350525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11072637081029597640233683 16608955621544396460350525)
            ·
              refine ⟨6228358358079148672631447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16608955621544396460350525 6228358358079148672631447)
              ·
                refine ⟨9342537537118723008947171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6228358358079148672631447 9342537537118723008947171)
                ·
                  refine ⟨14013806305678084513420757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9342537537118723008947171 14013806305678084513420757)
                  ·
                    refine ⟨328448585289330105783299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14013806305678084513420757 328448585289330105783299)
                    ·
                      rfl

theorem cell23_1918954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_1918954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918954 prefixEnd_1918954 := by exact prefixLift 1918954
  have htrace : WordTrace (prefixWord ++ tailWord_1918954) baseStart_1918954 baseEnd_1918954 := by
    simpa [prefixWord, tailWord_1918954, baseEnd_1918954] using wordTrace_append hprefix tailTrace_1918954
  have hstable : (prefixWord ++ tailWord_1918954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918954).length < 2 ^ (prefixWord ++ tailWord_1918954).sum := by decide
  have hdescent : baseEnd_1918954 < baseStart_1918954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918958 : List Nat := [4, 1, 2, 1, 3, 2, 2, 3, 5]
def baseStart_1918958 : Nat := 118140960795 + 1918958 * 2 ^ 59
def prefixEnd_1918958 : Nat := 4983230072969 + 3 ^ 40 * 1918958 * 2
def baseEnd_1918958 : Nat := 109483089976734255744431

theorem tailTrace_1918958 : CollatzResearch.WordTrace tailWord_1918958 prefixEnd_1918958 109483089976734255744431 := by
  unfold tailWord_1918958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8748768522743796597429691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46660098787966915186291685 8748768522743796597429691)
  ·
    refine ⟨13123152784115694896144537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8748768522743796597429691 13123152784115694896144537)
    ·
      refine ⟨9842364588086771172108403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13123152784115694896144537 9842364588086771172108403)
      ·
        refine ⟨14763546882130156758162605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9842364588086771172108403 14763546882130156758162605)
        ·
          refine ⟨5536330080798808784310977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14763546882130156758162605 5536330080798808784310977)
          ·
            refine ⟨4152247560599106588233233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5536330080798808784310977 4152247560599106588233233)
            ·
              refine ⟨3114185670449329941174925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4152247560599106588233233 3114185670449329941174925)
              ·
                refine ⟨1167819626418498727940597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3114185670449329941174925 1167819626418498727940597)
                ·
                  refine ⟨109483089976734255744431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1167819626418498727940597 109483089976734255744431)
                  ·
                    rfl

theorem cell23_1918958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_1918958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918958 prefixEnd_1918958 := by exact prefixLift 1918958
  have htrace : WordTrace (prefixWord ++ tailWord_1918958) baseStart_1918958 baseEnd_1918958 := by
    simpa [prefixWord, tailWord_1918958, baseEnd_1918958] using wordTrace_append hprefix tailTrace_1918958
  have hstable : (prefixWord ++ tailWord_1918958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918958).length < 2 ^ (prefixWord ++ tailWord_1918958).sum := by decide
  have hdescent : baseEnd_1918958 < baseStart_1918958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1918967 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 3, 10]
def baseStart_1918967 : Nat := 118140960795 + 1918967 * 2 ^ 59
def prefixEnd_1918967 : Nat := 4983230072969 + 3 ^ 40 * 1918967 * 2
def baseEnd_1918967 : Nat := 328450810372166255495779

theorem tailTrace_1918967 : CollatzResearch.WordTrace tailWord_1918967 prefixEnd_1918967 328450810372166255495779 := by
  unfold tailWord_1918967
  simp only [CollatzResearch.WordTrace]
  refine ⟨69990476438917767316515155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46660317625945178211010103 69990476438917767316515155)
  ·
    refine ⟨104985714658376650974772733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69990476438917767316515155 104985714658376650974772733)
    ·
      refine ⟨39369642996891244115539775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104985714658376650974772733 39369642996891244115539775)
      ·
        refine ⟨59054464495336866173309663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39369642996891244115539775 59054464495336866173309663)
        ·
          refine ⟨88581696743005299259964495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59054464495336866173309663 88581696743005299259964495)
          ·
            refine ⟨132872545114507948889946743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88581696743005299259964495 132872545114507948889946743)
            ·
              refine ⟨199308817671761923334920115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132872545114507948889946743 199308817671761923334920115)
              ·
                refine ⟨298963226507642885002380173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199308817671761923334920115 298963226507642885002380173)
                ·
                  refine ⟨112111209940366081875892565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 298963226507642885002380173 112111209940366081875892565)
                  ·
                    refine ⟨328450810372166255495779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 112111209940366081875892565 328450810372166255495779)
                    ·
                      rfl

theorem cell23_1918967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_1918967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1918967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1918967 prefixEnd_1918967 := by exact prefixLift 1918967
  have htrace : WordTrace (prefixWord ++ tailWord_1918967) baseStart_1918967 baseEnd_1918967 := by
    simpa [prefixWord, tailWord_1918967, baseEnd_1918967] using wordTrace_append hprefix tailTrace_1918967
  have hstable : (prefixWord ++ tailWord_1918967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1918967).length < 2 ^ (prefixWord ++ tailWord_1918967).sum := by decide
  have hdescent : baseEnd_1918967 < baseStart_1918967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1918967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919011 : List Nat := [1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 3]
def baseStart_1919011 : Nat := 118140960795 + 1919011 * 2 ^ 59
def prefixEnd_1919011 : Nat := 4983230072969 + 3 ^ 40 * 1919011 * 2
def baseEnd_1919011 : Nat := 985375024265296594337135

theorem tailTrace_1919011 : CollatzResearch.WordTrace tailWord_1919011 prefixEnd_1919011 985375024265296594337135 := by
  unfold tailWord_1919011
  simp only [CollatzResearch.WordTrace]
  refine ⟨69992081250758362831116887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46661387500505575220744591 69992081250758362831116887)
  ·
    refine ⟨104988121876137544246675331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69992081250758362831116887 104988121876137544246675331)
    ·
      refine ⟨157482182814206316370012997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104988121876137544246675331 157482182814206316370012997)
      ·
        refine ⟨29527909277663684319377437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157482182814206316370012997 29527909277663684319377437)
        ·
          refine ⟨11072965979123881619766539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29527909277663684319377437 11072965979123881619766539)
          ·
            refine ⟨16609448968685822429649809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11072965979123881619766539 16609448968685822429649809)
            ·
              refine ⟨12457086726514366822237357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16609448968685822429649809 12457086726514366822237357)
              ·
                refine ⟨4671407522442887558339009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12457086726514366822237357 4671407522442887558339009)
                ·
                  refine ⟨3503555641832165668754257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4671407522442887558339009 3503555641832165668754257)
                  ·
                    refine ⟨2627666731374124251565693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3503555641832165668754257 2627666731374124251565693)
                    ·
                      refine ⟨985375024265296594337135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2627666731374124251565693 985375024265296594337135)
                      ·
                        rfl

theorem cell23_1919011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_1919011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919011 prefixEnd_1919011 := by exact prefixLift 1919011
  have htrace : WordTrace (prefixWord ++ tailWord_1919011) baseStart_1919011 baseEnd_1919011 := by
    simpa [prefixWord, tailWord_1919011, baseEnd_1919011] using wordTrace_append hprefix tailTrace_1919011
  have hstable : (prefixWord ++ tailWord_1919011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919011).length < 2 ^ (prefixWord ++ tailWord_1919011).sum := by decide
  have hdescent : baseEnd_1919011 < baseStart_1919011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919061 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 3, 5]
def baseStart_1919061 : Nat := 118140960795 + 1919061 * 2 ^ 59
def prefixEnd_1919061 : Nat := 4983230072969 + 3 ^ 40 * 1919061 * 2
def baseEnd_1919061 : Nat := 328466899432673799570635

theorem tailTrace_1919061 : CollatzResearch.WordTrace tailWord_1919061 prefixEnd_1919061 328466899432673799570635 := by
  unfold tailWord_1919061
  simp only [CollatzResearch.WordTrace]
  refine ⟨69993904900577221370437037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46662603267051480913624691 69993904900577221370437037)
  ·
    refine ⟨26247714337716458013913889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69993904900577221370437037 26247714337716458013913889)
    ·
      refine ⟨19685785753287343510435417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26247714337716458013913889 19685785753287343510435417)
      ·
        refine ⟨14764339314965507632826563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19685785753287343510435417 14764339314965507632826563)
        ·
          refine ⟨22146508972448261449239845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14764339314965507632826563 22146508972448261449239845)
          ·
            refine ⟨4152470432334049021732471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22146508972448261449239845 4152470432334049021732471)
            ·
              refine ⟨6228705648501073532598707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4152470432334049021732471 6228705648501073532598707)
              ·
                refine ⟨9343058472751610298898061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6228705648501073532598707 9343058472751610298898061)
                ·
                  refine ⟨3503646927281853862086773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9343058472751610298898061 3503646927281853862086773)
                  ·
                    refine ⟨328466899432673799570635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3503646927281853862086773 328466899432673799570635)
                    ·
                      rfl

theorem cell23_1919061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_1919061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919061 prefixEnd_1919061 := by exact prefixLift 1919061
  have htrace : WordTrace (prefixWord ++ tailWord_1919061) baseStart_1919061 baseEnd_1919061 := by
    simpa [prefixWord, tailWord_1919061, baseEnd_1919061] using wordTrace_append hprefix tailTrace_1919061
  have hstable : (prefixWord ++ tailWord_1919061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919061).length < 2 ^ (prefixWord ++ tailWord_1919061).sum := by decide
  have hdescent : baseEnd_1919061 < baseStart_1919061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919062 : List Nat := [5, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1919062 : Nat := 118140960795 + 1919062 * 2 ^ 59
def prefixEnd_1919062 : Nat := 4983230072969 + 3 ^ 40 * 1919062 * 2
def baseEnd_1919062 : Nat := 985401211778675894799401

theorem tailTrace_1919062 : CollatzResearch.WordTrace tailWord_1919062 prefixEnd_1919062 985401211778675894799401 := by
  unfold tailWord_1919062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4374621335848349908826465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46662627582382399027482293 4374621335848349908826465)
  ·
    refine ⟨3280966001886262431619849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4374621335848349908826465 3280966001886262431619849)
    ·
      refine ⟨2460724501414696823714887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3280966001886262431619849 2460724501414696823714887)
      ·
        refine ⟨3691086752122045235572331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2460724501414696823714887 3691086752122045235572331)
        ·
          refine ⟨5536630128183067853358497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3691086752122045235572331 5536630128183067853358497)
          ·
            refine ⟨4152472596137300890018873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5536630128183067853358497 4152472596137300890018873)
            ·
              refine ⟨3114354447102975667514155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4152472596137300890018873 3114354447102975667514155)
              ·
                refine ⟨4671531670654463501271233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3114354447102975667514155 4671531670654463501271233)
                ·
                  refine ⟨3503648752990847625953425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4671531670654463501271233 3503648752990847625953425)
                  ·
                    refine ⟨2627736564743135719465069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3503648752990847625953425 2627736564743135719465069)
                    ·
                      refine ⟨985401211778675894799401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2627736564743135719465069 985401211778675894799401)
                      ·
                        rfl

theorem cell23_1919062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1919062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919062 prefixEnd_1919062 := by exact prefixLift 1919062
  have htrace : WordTrace (prefixWord ++ tailWord_1919062) baseStart_1919062 baseEnd_1919062 := by
    simpa [prefixWord, tailWord_1919062, baseEnd_1919062] using wordTrace_append hprefix tailTrace_1919062
  have hstable : (prefixWord ++ tailWord_1919062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919062).length < 2 ^ (prefixWord ++ tailWord_1919062).sum := by decide
  have hdescent : baseEnd_1919062 < baseStart_1919062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919098 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2]
def baseStart_1919098 : Nat := 118140960795 + 1919098 * 2 ^ 59
def prefixEnd_1919098 : Nat := 4983230072969 + 3 ^ 40 * 1919098 * 2
def baseEnd_1919098 : Nat := 985419697082237753949235

theorem tailTrace_1919098 : CollatzResearch.WordTrace tailWord_1919098 prefixEnd_1919098 985419697082237753949235 := by
  unfold tailWord_1919098
  simp only [CollatzResearch.WordTrace]
  refine ⟨17498813600360794172383487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46663502934295451126355965 17498813600360794172383487)
  ·
    refine ⟨26248220400541191258575231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17498813600360794172383487 26248220400541191258575231)
    ·
      refine ⟨39372330600811786887862847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26248220400541191258575231 39372330600811786887862847)
      ·
        refine ⟨59058495901217680331794271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39372330600811786887862847 59058495901217680331794271)
        ·
          refine ⟨88587743851826520497691407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59058495901217680331794271 88587743851826520497691407)
          ·
            refine ⟨132881615777739780746537111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88587743851826520497691407 132881615777739780746537111)
            ·
              refine ⟨199322423666609671119805667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132881615777739780746537111 199322423666609671119805667)
              ·
                refine ⟨298983635499914506679708501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199322423666609671119805667 298983635499914506679708501)
                ·
                  refine ⟨1751857239257311562576417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 298983635499914506679708501 1751857239257311562576417)
                  ·
                    refine ⟨1313892929442983671932313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1751857239257311562576417 1313892929442983671932313)
                    ·
                      refine ⟨985419697082237753949235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1313892929442983671932313 985419697082237753949235)
                      ·
                        rfl

theorem cell23_1919098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2].length) (baseStart_1919098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919098 prefixEnd_1919098 := by exact prefixLift 1919098
  have htrace : WordTrace (prefixWord ++ tailWord_1919098) baseStart_1919098 baseEnd_1919098 := by
    simpa [prefixWord, tailWord_1919098, baseEnd_1919098] using wordTrace_append hprefix tailTrace_1919098
  have hstable : (prefixWord ++ tailWord_1919098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919098).length < 2 ^ (prefixWord ++ tailWord_1919098).sum := by decide
  have hdescent : baseEnd_1919098 < baseStart_1919098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919108 : List Nat := [2, 3, 2, 1, 2, 1, 1, 5, 2, 4]
def baseStart_1919108 : Nat := 118140960795 + 1919108 * 2 ^ 59
def prefixEnd_1919108 : Nat := 4983230072969 + 3 ^ 40 * 1919108 * 2
def baseEnd_1919108 : Nat := 328474943962927571608063

theorem tailTrace_1919108 : CollatzResearch.WordTrace tailWord_1919108 prefixEnd_1919108 328474943962927571608063 := by
  unfold tailWord_1919108
  simp only [CollatzResearch.WordTrace]
  refine ⟨34997809565703474198698989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46663746087604632264931985 34997809565703474198698989)
  ·
    refine ⟨13124178587138802824512121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34997809565703474198698989 13124178587138802824512121)
    ·
      refine ⟨9843133940354102118384091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13124178587138802824512121 9843133940354102118384091)
      ·
        refine ⟨14764700910531153177576137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9843133940354102118384091 14764700910531153177576137)
        ·
          refine ⟨11073525682898364883182103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14764700910531153177576137 11073525682898364883182103)
          ·
            refine ⟨16610288524347547324773155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11073525682898364883182103 16610288524347547324773155)
            ·
              refine ⟨24915432786521320987159733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16610288524347547324773155 24915432786521320987159733)
              ·
                refine ⟨2335821823736373842546225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24915432786521320987159733 2335821823736373842546225)
                ·
                  refine ⟨1751866367802280381909669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2335821823736373842546225 1751866367802280381909669)
                  ·
                    refine ⟨328474943962927571608063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1751866367802280381909669 328474943962927571608063)
                    ·
                      rfl

theorem cell23_1919108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_1919108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919108 prefixEnd_1919108 := by exact prefixLift 1919108
  have htrace : WordTrace (prefixWord ++ tailWord_1919108) baseStart_1919108 baseEnd_1919108 := by
    simpa [prefixWord, tailWord_1919108, baseEnd_1919108] using wordTrace_append hprefix tailTrace_1919108
  have hstable : (prefixWord ++ tailWord_1919108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919108).length < 2 ^ (prefixWord ++ tailWord_1919108).sum := by decide
  have hdescent : baseEnd_1919108 < baseStart_1919108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919111 : List Nat := [1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 4]
def baseStart_1919111 : Nat := 118140960795 + 1919111 * 2 ^ 59
def prefixEnd_1919111 : Nat := 4983230072969 + 3 ^ 40 * 1919111 * 2
def baseEnd_1919111 : Nat := 985426372330746203086675

theorem tailTrace_1919111 : CollatzResearch.WordTrace tailWord_1919111 prefixEnd_1919111 985426372330746203086675 := by
  unfold tailWord_1919111
  simp only [CollatzResearch.WordTrace]
  refine ⟨69995728550396079909757187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46663819033597386606504791 69995728550396079909757187)
  ·
    refine ⟨104993592825594119864635781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69995728550396079909757187 104993592825594119864635781)
    ·
      refine ⟨19686298654798897474619209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 104993592825594119864635781 19686298654798897474619209)
      ·
        refine ⟨14764723991099173105964407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19686298654798897474619209 14764723991099173105964407)
        ·
          refine ⟨22147085986648759658946611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14764723991099173105964407 22147085986648759658946611)
          ·
            refine ⟨33220628979973139488419917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22147085986648759658946611 33220628979973139488419917)
            ·
              refine ⟨12457735867489927308157469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33220628979973139488419917 12457735867489927308157469)
              ·
                refine ⟨4671650950308722740559051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12457735867489927308157469 4671650950308722740559051)
                ·
                  refine ⟨7007476425463084110838577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4671650950308722740559051 7007476425463084110838577)
                  ·
                    refine ⟨5255607319097313083128933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7007476425463084110838577 5255607319097313083128933)
                    ·
                      refine ⟨985426372330746203086675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5255607319097313083128933 985426372330746203086675)
                      ·
                        rfl

theorem cell23_1919111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_1919111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919111 prefixEnd_1919111 := by exact prefixLift 1919111
  have htrace : WordTrace (prefixWord ++ tailWord_1919111) baseStart_1919111 baseEnd_1919111 := by
    simpa [prefixWord, tailWord_1919111, baseEnd_1919111] using wordTrace_append hprefix tailTrace_1919111
  have hstable : (prefixWord ++ tailWord_1919111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919111).length < 2 ^ (prefixWord ++ tailWord_1919111).sum := by decide
  have hdescent : baseEnd_1919111 < baseStart_1919111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919131 : List Nat := [1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 3]
def baseStart_1919131 : Nat := 118140960795 + 1919131 * 2 ^ 59
def prefixEnd_1919131 : Nat := 4983230072969 + 3 ^ 40 * 1919131 * 2
def baseEnd_1919131 : Nat := 985436641943836124836583

theorem tailTrace_1919131 : CollatzResearch.WordTrace tailWord_1919131 prefixEnd_1919131 985436641943836124836583 := by
  unfold tailWord_1919131
  simp only [CollatzResearch.WordTrace]
  refine ⟨69996458010323623325485247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46664305340215748883656831 69996458010323623325485247)
  ·
    refine ⟨104994687015485434988227871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69996458010323623325485247 104994687015485434988227871)
    ·
      refine ⟨157492030523228152482341807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104994687015485434988227871 157492030523228152482341807)
      ·
        refine ⟨236238045784842228723512711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157492030523228152482341807 236238045784842228723512711)
        ·
          refine ⟨354357068677263343085269067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236238045784842228723512711 354357068677263343085269067)
          ·
            refine ⟨531535603015895014627903601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354357068677263343085269067 531535603015895014627903601)
            ·
              refine ⟨398651702261921260970927701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531535603015895014627903601 398651702261921260970927701)
              ·
                refine ⟨4671699635881889777003059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 398651702261921260970927701 4671699635881889777003059)
                ·
                  refine ⟨7007549453822834665504589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4671699635881889777003059 7007549453822834665504589)
                  ·
                    refine ⟨2627831045183562999564221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7007549453822834665504589 2627831045183562999564221)
                    ·
                      refine ⟨985436641943836124836583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2627831045183562999564221 985436641943836124836583)
                      ·
                        rfl

theorem cell23_1919131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 3, 3].length) (baseStart_1919131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919131 prefixEnd_1919131 := by exact prefixLift 1919131
  have htrace : WordTrace (prefixWord ++ tailWord_1919131) baseStart_1919131 baseEnd_1919131 := by
    simpa [prefixWord, tailWord_1919131, baseEnd_1919131] using wordTrace_append hprefix tailTrace_1919131
  have hstable : (prefixWord ++ tailWord_1919131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919131).length < 2 ^ (prefixWord ++ tailWord_1919131).sum := by decide
  have hdescent : baseEnd_1919131 < baseStart_1919131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919135 : List Nat := [1, 1, 2, 6, 1, 2, 1, 3, 1, 2, 3]
def baseStart_1919135 : Nat := 118140960795 + 1919135 * 2 ^ 59
def prefixEnd_1919135 : Nat := 4983230072969 + 3 ^ 40 * 1919135 * 2
def baseEnd_1919135 : Nat := 985438695866454109186565

theorem tailTrace_1919135 : CollatzResearch.WordTrace tailWord_1919135 prefixEnd_1919135 985438695866454109186565 := by
  unfold tailWord_1919135
  simp only [CollatzResearch.WordTrace]
  refine ⟨69996603902309132008630859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46664402601539421339087239 69996603902309132008630859)
  ·
    refine ⟨104994905853463698012946289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69996603902309132008630859 104994905853463698012946289)
    ·
      refine ⟨78746179390097773509709717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104994905853463698012946289 78746179390097773509709717)
      ·
        refine ⟨3691227158910833133267643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 78746179390097773509709717 3691227158910833133267643)
        ·
          refine ⟨5536840738366249699901465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3691227158910833133267643 5536840738366249699901465)
          ·
            refine ⟨4152630553774687274926099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5536840738366249699901465 4152630553774687274926099)
            ·
              refine ⟨6228945830662030912389149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4152630553774687274926099 6228945830662030912389149)
              ·
                refine ⟨2335854686498261592145931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6228945830662030912389149 2335854686498261592145931)
                ·
                  refine ⟨3503782029747392388218897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2335854686498261592145931 3503782029747392388218897)
                  ·
                    refine ⟨2627836522310544291164173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3503782029747392388218897 2627836522310544291164173)
                    ·
                      refine ⟨985438695866454109186565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2627836522310544291164173 985438695866454109186565)
                      ·
                        rfl

theorem cell23_1919135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_1919135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919135 prefixEnd_1919135 := by exact prefixLift 1919135
  have htrace : WordTrace (prefixWord ++ tailWord_1919135) baseStart_1919135 baseEnd_1919135 := by
    simpa [prefixWord, tailWord_1919135, baseEnd_1919135] using wordTrace_append hprefix tailTrace_1919135
  have hstable : (prefixWord ++ tailWord_1919135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919135).length < 2 ^ (prefixWord ++ tailWord_1919135).sum := by decide
  have hdescent : baseEnd_1919135 < baseStart_1919135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919149 : List Nat := [1, 5, 2, 1, 2, 1, 2, 4, 1, 2, 2]
def baseStart_1919149 : Nat := 118140960795 + 1919149 * 2 ^ 59
def prefixEnd_1919149 : Nat := 4983230072969 + 3 ^ 40 * 1919149 * 2
def baseEnd_1919149 : Nat := 985445884595617054411501

theorem tailTrace_1919149 : CollatzResearch.WordTrace tailWord_1919149 prefixEnd_1919149 985445884595617054411501 := by
  unfold tailWord_1919149
  simp only [CollatzResearch.WordTrace]
  refine ⟨69997114524258412399640501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46664743016172274933093667 69997114524258412399640501)
  ·
    refine ⟨6562229486649226162466297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 69997114524258412399640501 6562229486649226162466297)
    ·
      refine ⟨4921672114986919621849723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6562229486649226162466297 4921672114986919621849723)
      ·
        refine ⟨7382508172480379432774585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4921672114986919621849723 7382508172480379432774585)
        ·
          refine ⟨5536881129360284574580939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7382508172480379432774585 5536881129360284574580939)
          ·
            refine ⟨8305321694040426861871409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5536881129360284574580939 8305321694040426861871409)
            ·
              refine ⟨6228991270530320146403557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8305321694040426861871409 6228991270530320146403557)
              ·
                refine ⟨1167935863224435027450667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6228991270530320146403557 1167935863224435027450667)
                ·
                  refine ⟨1751903794836652541176001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1167935863224435027450667 1751903794836652541176001)
                  ·
                    refine ⟨1313927846127489405882001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1751903794836652541176001 1313927846127489405882001)
                    ·
                      refine ⟨985445884595617054411501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1313927846127489405882001 985445884595617054411501)
                      ·
                        rfl

theorem cell23_1919149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_1919149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919149 prefixEnd_1919149 := by exact prefixLift 1919149
  have htrace : WordTrace (prefixWord ++ tailWord_1919149) baseStart_1919149 baseEnd_1919149 := by
    simpa [prefixWord, tailWord_1919149, baseEnd_1919149] using wordTrace_append hprefix tailTrace_1919149
  have hstable : (prefixWord ++ tailWord_1919149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919149).length < 2 ^ (prefixWord ++ tailWord_1919149).sum := by decide
  have hdescent : baseEnd_1919149 < baseStart_1919149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919191 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 3]
def baseStart_1919191 : Nat := 118140960795 + 1919191 * 2 ^ 59
def prefixEnd_1919191 : Nat := 4983230072969 + 3 ^ 40 * 1919191 * 2
def baseEnd_1919191 : Nat := 985467450783105890086307

theorem tailTrace_1919191 : CollatzResearch.WordTrace tailWord_1919191 prefixEnd_1919191 985467450783105890086307 := by
  unfold tailWord_1919191
  simp only [CollatzResearch.WordTrace]
  refine ⟨69998646390106253572669427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46665764260070835715112951 69998646390106253572669427)
  ·
    refine ⟨104997969585159380359004141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69998646390106253572669427 104997969585159380359004141)
    ·
      refine ⟨39374238594434767634626553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104997969585159380359004141 39374238594434767634626553)
      ·
        refine ⟨29530678945826075725969915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39374238594434767634626553 29530678945826075725969915)
        ·
          refine ⟨44296018418739113588954873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29530678945826075725969915 44296018418739113588954873)
          ·
            refine ⟨33222013814054335191716155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44296018418739113588954873 33222013814054335191716155)
            ·
              refine ⟨49833020721081502787574233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33222013814054335191716155 49833020721081502787574233)
              ·
                refine ⟨37374765540811127090680675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49833020721081502787574233 37374765540811127090680675)
                ·
                  refine ⟨56062148311216690636021013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37374765540811127090680675 56062148311216690636021013)
                  ·
                    refine ⟨2627913202088282373563485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56062148311216690636021013 2627913202088282373563485)
                    ·
                      refine ⟨985467450783105890086307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2627913202088282373563485 985467450783105890086307)
                      ·
                        rfl

theorem cell23_1919191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_1919191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919191 prefixEnd_1919191 := by exact prefixLift 1919191
  have htrace : WordTrace (prefixWord ++ tailWord_1919191) baseStart_1919191 baseEnd_1919191 := by
    simpa [prefixWord, tailWord_1919191, baseEnd_1919191] using wordTrace_append hprefix tailTrace_1919191
  have hstable : (prefixWord ++ tailWord_1919191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919191).length < 2 ^ (prefixWord ++ tailWord_1919191).sum := by decide
  have hdescent : baseEnd_1919191 < baseStart_1919191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919268 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_1919268 : Nat := 118140960795 + 1919268 * 2 ^ 59
def prefixEnd_1919268 : Nat := 4983230072969 + 3 ^ 40 * 1919268 * 2
def baseEnd_1919268 : Nat := 985506988793502088823453

theorem tailTrace_1919268 : CollatzResearch.WordTrace tailWord_1919268 prefixEnd_1919268 985506988793502088823453 := by
  unfold tailWord_1919268
  simp only [CollatzResearch.WordTrace]
  refine ⟨35000727405413647861611229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46667636540551530482148305 35000727405413647861611229)
  ·
    refine ⟨13125272777030117948104211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35000727405413647861611229 13125272777030117948104211)
    ·
      refine ⟨19687909165545176922156317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13125272777030117948104211 19687909165545176922156317)
      ·
        refine ⟨7382965937079441345808619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19687909165545176922156317 7382965937079441345808619)
        ·
          refine ⟨11074448905619162018712929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7382965937079441345808619 11074448905619162018712929)
          ·
            refine ⟨8305836679214371514034697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11074448905619162018712929 8305836679214371514034697)
            ·
              refine ⟨6229377509410778635526023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8305836679214371514034697 6229377509410778635526023)
              ·
                refine ⟨9344066264116167953289035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6229377509410778635526023 9344066264116167953289035)
                ·
                  refine ⟨14016099396174251929933553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9344066264116167953289035 14016099396174251929933553)
                  ·
                    refine ⟨10512074547130688947450165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14016099396174251929933553 10512074547130688947450165)
                    ·
                      refine ⟨985506988793502088823453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10512074547130688947450165 985506988793502088823453)
                      ·
                        rfl

theorem cell23_1919268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_1919268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919268 prefixEnd_1919268 := by exact prefixLift 1919268
  have htrace : WordTrace (prefixWord ++ tailWord_1919268) baseStart_1919268 baseEnd_1919268 := by
    simpa [prefixWord, tailWord_1919268, baseEnd_1919268] using wordTrace_append hprefix tailTrace_1919268
  have hstable : (prefixWord ++ tailWord_1919268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919268).length < 2 ^ (prefixWord ++ tailWord_1919268).sum := by decide
  have hdescent : baseEnd_1919268 < baseStart_1919268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919288 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 5, 4]
def baseStart_1919288 : Nat := 118140960795 + 1919288 * 2 ^ 59
def prefixEnd_1919288 : Nat := 4983230072969 + 3 ^ 40 * 1919288 * 2
def baseEnd_1919288 : Nat := 328505752802197336857787

theorem tailTrace_1919288 : CollatzResearch.WordTrace tailWord_1919288 prefixEnd_1919288 328505752802197336857787 := by
  unfold tailWord_1919288
  simp only [CollatzResearch.WordTrace]
  refine ⟨35001092135377419569475259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46668122847169892759300345 35001092135377419569475259)
  ·
    refine ⟨52501638203066129354212889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35001092135377419569475259 52501638203066129354212889)
    ·
      refine ⟨39376228652299597015659667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52501638203066129354212889 39376228652299597015659667)
      ·
        refine ⟨59064342978449395523489501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39376228652299597015659667 59064342978449395523489501)
        ·
          refine ⟨22149128616918523321308563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59064342978449395523489501 22149128616918523321308563)
          ·
            refine ⟨33223692925377784981962845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22149128616918523321308563 33223692925377784981962845)
            ·
              refine ⟨12458884847016669368236067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33223692925377784981962845 12458884847016669368236067)
              ·
                refine ⟨18688327270525004052354101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12458884847016669368236067 18688327270525004052354101)
                ·
                  refine ⟨1752030681611719129908197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18688327270525004052354101 1752030681611719129908197)
                  ·
                    refine ⟨328505752802197336857787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1752030681611719129908197 328505752802197336857787)
                    ·
                      rfl

theorem cell23_1919288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 5, 4].length) (baseStart_1919288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919288 prefixEnd_1919288 := by exact prefixLift 1919288
  have htrace : WordTrace (prefixWord ++ tailWord_1919288) baseStart_1919288 baseEnd_1919288 := by
    simpa [prefixWord, tailWord_1919288, baseEnd_1919288] using wordTrace_append hprefix tailTrace_1919288
  have hstable : (prefixWord ++ tailWord_1919288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919288).length < 2 ^ (prefixWord ++ tailWord_1919288).sum := by decide
  have hdescent : baseEnd_1919288 < baseStart_1919288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919355 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 1, 5, 2]
def baseStart_1919355 : Nat := 118140960795 + 1919355 * 2 ^ 59
def prefixEnd_1919355 : Nat := 4983230072969 + 3 ^ 40 * 1919355 * 2
def baseEnd_1919355 : Nat := 985551661610443248435553

theorem tailTrace_1919355 : CollatzResearch.WordTrace tailWord_1919355 prefixEnd_1919355 985551661610443248435553 := by
  unfold tailWord_1919355
  simp only [CollatzResearch.WordTrace]
  refine ⟨70004627961512109581639519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46669751974341406387759679 70004627961512109581639519)
  ·
    refine ⟨105006941942268164372459279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70004627961512109581639519 105006941942268164372459279)
    ·
      refine ⟨157510412913402246558688919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105006941942268164372459279 157510412913402246558688919)
      ·
        refine ⟨236265619370103369838033379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157510412913402246558688919 236265619370103369838033379)
        ·
          refine ⟨354398429055155054757050069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236265619370103369838033379 354398429055155054757050069)
          ·
            refine ⟨8306213180980196595868361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 354398429055155054757050069 8306213180980196595868361)
            ·
              refine ⟨6229659885735147446901271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8306213180980196595868361 6229659885735147446901271)
              ·
                refine ⟨9344489828602721170351907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6229659885735147446901271 9344489828602721170351907)
                ·
                  refine ⟨14016734742904081755527861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9344489828602721170351907 14016734742904081755527861)
                  ·
                    refine ⟨1314068882147257664580737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14016734742904081755527861 1314068882147257664580737)
                    ·
                      refine ⟨985551661610443248435553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1314068882147257664580737 985551661610443248435553)
                      ·
                        rfl

theorem cell23_1919355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 5, 2].length) (baseStart_1919355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919355 prefixEnd_1919355 := by exact prefixLift 1919355
  have htrace : WordTrace (prefixWord ++ tailWord_1919355) baseStart_1919355 baseEnd_1919355 := by
    simpa [prefixWord, tailWord_1919355, baseEnd_1919355] using wordTrace_append hprefix tailTrace_1919355
  have hstable : (prefixWord ++ tailWord_1919355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919355).length < 2 ^ (prefixWord ++ tailWord_1919355).sum := by decide
  have hdescent : baseEnd_1919355 < baseStart_1919355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919372 : List Nat := [2, 2, 1, 2, 1, 5, 1, 2, 2, 3, 2]
def baseStart_1919372 : Nat := 118140960795 + 1919372 * 2 ^ 59
def prefixEnd_1919372 : Nat := 4983230072969 + 3 ^ 40 * 1919372 * 2
def baseEnd_1919372 : Nat := 985560390781569681922975

theorem tailTrace_1919372 : CollatzResearch.WordTrace tailWord_1919372 prefixEnd_1919372 985560390781569681922975 := by
  unfold tailWord_1919372
  simp only [CollatzResearch.WordTrace]
  refine ⟨35002624001225260742504185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46670165334967014323338913 35002624001225260742504185)
  ·
    refine ⟨26251968000918945556878139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35002624001225260742504185 26251968000918945556878139)
    ·
      refine ⟨39377952001378418335317209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26251968000918945556878139 39377952001378418335317209)
      ·
        refine ⟨29533464001033813751487907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39377952001378418335317209 29533464001033813751487907)
        ·
          refine ⟨44300196001550720627231861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29533464001033813751487907 44300196001550720627231861)
          ·
            refine ⟨4153143375145380058802987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44300196001550720627231861 4153143375145380058802987)
            ·
              refine ⟨6229715062718070088204481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4153143375145380058802987 6229715062718070088204481)
              ·
                refine ⟨4672286297038552566153361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6229715062718070088204481 4672286297038552566153361)
                ·
                  refine ⟨3504214722778914424615021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4672286297038552566153361 3504214722778914424615021)
                  ·
                    refine ⟨1314080521042092909230633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3504214722778914424615021 1314080521042092909230633)
                    ·
                      refine ⟨985560390781569681922975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1314080521042092909230633 985560390781569681922975)
                      ·
                        rfl

theorem cell23_1919372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_1919372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919372 prefixEnd_1919372 := by exact prefixLift 1919372
  have htrace : WordTrace (prefixWord ++ tailWord_1919372) baseStart_1919372 baseEnd_1919372 := by
    simpa [prefixWord, tailWord_1919372, baseEnd_1919372] using wordTrace_append hprefix tailTrace_1919372
  have hstable : (prefixWord ++ tailWord_1919372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919372).length < 2 ^ (prefixWord ++ tailWord_1919372).sum := by decide
  have hdescent : baseEnd_1919372 < baseStart_1919372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919415 : List Nat := [1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 4]
def baseStart_1919415 : Nat := 118140960795 + 1919415 * 2 ^ 59
def prefixEnd_1919415 : Nat := 4983230072969 + 3 ^ 40 * 1919415 * 2
def baseEnd_1919415 : Nat := 985582470449713013685277

theorem tailTrace_1919415 : CollatzResearch.WordTrace tailWord_1919415 prefixEnd_1919415 985582470449713013685277 := by
  unfold tailWord_1919415
  simp only [CollatzResearch.WordTrace]
  refine ⟨70006816341294739828823699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46671210894196493219215799 70006816341294739828823699)
  ·
    refine ⟨105010224511942109743235549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70006816341294739828823699 105010224511942109743235549)
    ·
      refine ⟨39378834191978291153713331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105010224511942109743235549 39378834191978291153713331)
      ·
        refine ⟨59068251287967436730569997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39378834191978291153713331 59068251287967436730569997)
        ·
          refine ⟨22150594232987788773963749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59068251287967436730569997 22150594232987788773963749)
          ·
            refine ⟨4153236418685210395118203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22150594232987788773963749 4153236418685210395118203)
            ·
              refine ⟨6229854628027815592677305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4153236418685210395118203 6229854628027815592677305)
              ·
                refine ⟨4672390971020861694507979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6229854628027815592677305 4672390971020861694507979)
                ·
                  refine ⟨7008586456531292541761969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4672390971020861694507979 7008586456531292541761969)
                  ·
                    refine ⟨5256439842398469406321477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7008586456531292541761969 5256439842398469406321477)
                    ·
                      refine ⟨985582470449713013685277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5256439842398469406321477 985582470449713013685277)
                      ·
                        rfl

theorem cell23_1919415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_1919415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919415 prefixEnd_1919415 := by exact prefixLift 1919415
  have htrace : WordTrace (prefixWord ++ tailWord_1919415) baseStart_1919415 baseEnd_1919415 := by
    simpa [prefixWord, tailWord_1919415, baseEnd_1919415] using wordTrace_append hprefix tailTrace_1919415
  have hstable : (prefixWord ++ tailWord_1919415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919415).length < 2 ^ (prefixWord ++ tailWord_1919415).sum := by decide
  have hdescent : baseEnd_1919415 < baseStart_1919415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919422 : List Nat := [4, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3]
def baseStart_1919422 : Nat := 118140960795 + 1919422 * 2 ^ 59
def prefixEnd_1919422 : Nat := 4983230072969 + 3 ^ 40 * 1919422 * 2
def baseEnd_1919422 : Nat := 985586064814294486297745

theorem tailTrace_1919422 : CollatzResearch.WordTrace tailWord_1919422 prefixEnd_1919422 985586064814294486297745 := by
  unfold tailWord_1919422
  simp only [CollatzResearch.WordTrace]
  refine ⟨8750883956533672503041065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46671381101512920016219013 8750883956533672503041065)
  ·
    refine ⟨6563162967400254377280799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8750883956533672503041065 6563162967400254377280799)
    ·
      refine ⟨9844744451100381565921199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6563162967400254377280799 9844744451100381565921199)
      ·
        refine ⟨14767116676650572348881799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9844744451100381565921199 14767116676650572348881799)
        ·
          refine ⟨22150675014975858523322699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14767116676650572348881799 22150675014975858523322699)
          ·
            refine ⟨33226012522463787784984049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22150675014975858523322699 33226012522463787784984049)
            ·
              refine ⟨24919509391847840838738037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33226012522463787784984049 24919509391847840838738037)
              ·
                refine ⟨2336204005485735078631691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24919509391847840838738037 2336204005485735078631691)
                ·
                  refine ⟨3504306008228602617947537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2336204005485735078631691 3504306008228602617947537)
                  ·
                    refine ⟨2628229506171451963460653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3504306008228602617947537 2628229506171451963460653)
                    ·
                      refine ⟨985586064814294486297745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2628229506171451963460653 985586064814294486297745)
                      ·
                        rfl

theorem cell23_1919422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_1919422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919422 prefixEnd_1919422 := by exact prefixLift 1919422
  have htrace : WordTrace (prefixWord ++ tailWord_1919422) baseStart_1919422 baseEnd_1919422 := by
    simpa [prefixWord, tailWord_1919422, baseEnd_1919422] using wordTrace_append hprefix tailTrace_1919422
  have hstable : (prefixWord ++ tailWord_1919422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919422).length < 2 ^ (prefixWord ++ tailWord_1919422).sum := by decide
  have hdescent : baseEnd_1919422 < baseStart_1919422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919448 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 1, 4, 5]
def baseStart_1919448 : Nat := 118140960795 + 1919448 * 2 ^ 59
def prefixEnd_1919448 : Nat := 4983230072969 + 3 ^ 40 * 1919448 * 2
def baseEnd_1919448 : Nat := 985599415311311384572625

theorem tailTrace_1919448 : CollatzResearch.WordTrace tailWord_1919448 prefixEnd_1919448 985599415311311384572625 := by
  unfold tailWord_1919448
  simp only [CollatzResearch.WordTrace]
  refine ⟨35004009975087593232387499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46672013300116790976516665 35004009975087593232387499)
  ·
    refine ⟨52506014962631389848581249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35004009975087593232387499 52506014962631389848581249)
    ·
      refine ⟨39379511221973542386435937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52506014962631389848581249 39379511221973542386435937)
      ·
        refine ⟨29534633416480156789826953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39379511221973542386435937 29534633416480156789826953)
        ·
          refine ⟨22150975062360117592370215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29534633416480156789826953 22150975062360117592370215)
          ·
            refine ⟨33226462593540176388555323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22150975062360117592370215 33226462593540176388555323)
            ·
              refine ⟨49839693890310264582832985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33226462593540176388555323 49839693890310264582832985)
              ·
                refine ⟨37379770417732698437124739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49839693890310264582832985 37379770417732698437124739)
                ·
                  refine ⟨56069655626599047655687109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37379770417732698437124739 56069655626599047655687109)
                  ·
                    refine ⟨10513060429987321435441333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56069655626599047655687109 10513060429987321435441333)
                    ·
                      refine ⟨985599415311311384572625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10513060429987321435441333 985599415311311384572625)
                      ·
                        rfl

theorem cell23_1919448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_1919448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919448 prefixEnd_1919448 := by exact prefixLift 1919448
  have htrace : WordTrace (prefixWord ++ tailWord_1919448) baseStart_1919448 baseEnd_1919448 := by
    simpa [prefixWord, tailWord_1919448, baseEnd_1919448] using wordTrace_append hprefix tailTrace_1919448
  have hstable : (prefixWord ++ tailWord_1919448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919448).length < 2 ^ (prefixWord ++ tailWord_1919448).sum := by decide
  have hdescent : baseEnd_1919448 < baseStart_1919448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919468 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 1, 8]
def baseStart_1919468 : Nat := 118140960795 + 1919468 * 2 ^ 59
def prefixEnd_1919468 : Nat := 4983230072969 + 3 ^ 40 * 1919468 * 2
def baseEnd_1919468 : Nat := 328536561641467102107511

theorem tailTrace_1919468 : CollatzResearch.WordTrace tailWord_1919468 prefixEnd_1919468 328536561641467102107511 := by
  unfold tailWord_1919468
  simp only [CollatzResearch.WordTrace]
  refine ⟨35004374705051364940251529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46672499606735153253668705 35004374705051364940251529)
  ·
    refine ⟨26253281028788523705188647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35004374705051364940251529 26253281028788523705188647)
    ·
      refine ⟨39379921543182785557782971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26253281028788523705188647 39379921543182785557782971)
      ·
        refine ⟨59069882314774178336674457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39379921543182785557782971 59069882314774178336674457)
        ·
          refine ⟨44302411736080633752505843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59069882314774178336674457 44302411736080633752505843)
          ·
            refine ⟨66453617604120950628758765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44302411736080633752505843 66453617604120950628758765)
            ·
              refine ⟨24920106601545356485784537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66453617604120950628758765 24920106601545356485784537)
              ·
                refine ⟨18690079951159017364338403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24920106601545356485784537 18690079951159017364338403)
                ·
                  refine ⟨28035119926738526046507605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18690079951159017364338403 28035119926738526046507605)
                  ·
                    refine ⟨328536561641467102107511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28035119926738526046507605 328536561641467102107511)
                    ·
                      rfl

theorem cell23_1919468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_1919468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919468 prefixEnd_1919468 := by exact prefixLift 1919468
  have htrace : WordTrace (prefixWord ++ tailWord_1919468) baseStart_1919468 baseEnd_1919468 := by
    simpa [prefixWord, tailWord_1919468, baseEnd_1919468] using wordTrace_append hprefix tailTrace_1919468
  have hstable : (prefixWord ++ tailWord_1919468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919468).length < 2 ^ (prefixWord ++ tailWord_1919468).sum := by decide
  have hdescent : baseEnd_1919468 < baseStart_1919468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919525 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 1, 5, 3]
def baseStart_1919525 : Nat := 118140960795 + 1919525 * 2 ^ 59
def prefixEnd_1919525 : Nat := 4983230072969 + 3 ^ 40 * 1919525 * 2
def baseEnd_1919525 : Nat := 985638953321707583309771

theorem tailTrace_1919525 : CollatzResearch.WordTrace tailWord_1919525 prefixEnd_1919525 985638953321707583309771 := by
  unfold tailWord_1919525
  simp only [CollatzResearch.WordTrace]
  refine ⟨70010828370896228615328029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46673885580597485743552019 70010828370896228615328029)
  ·
    refine ⟨26254060639086085730748011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70010828370896228615328029 26254060639086085730748011)
    ·
      refine ⟨39381090958629128596122017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26254060639086085730748011 39381090958629128596122017)
      ·
        refine ⟨29535818218971846447091513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39381090958629128596122017 29535818218971846447091513)
        ·
          refine ⟨22151863664228884835318635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29535818218971846447091513 22151863664228884835318635)
          ·
            refine ⟨33227795496343327252977953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22151863664228884835318635 33227795496343327252977953)
            ·
              refine ⟨24920846622257495439733465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33227795496343327252977953 24920846622257495439733465)
              ·
                refine ⟨18690634966693121579800099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24920846622257495439733465 18690634966693121579800099)
                ·
                  refine ⟨28035952450039682369700149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18690634966693121579800099 28035952450039682369700149)
                  ·
                    refine ⟨2628370542191220222159389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28035952450039682369700149 2628370542191220222159389)
                    ·
                      refine ⟨985638953321707583309771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2628370542191220222159389 985638953321707583309771)
                      ·
                        rfl

theorem cell23_1919525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_1919525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919525 prefixEnd_1919525 := by exact prefixLift 1919525
  have htrace : WordTrace (prefixWord ++ tailWord_1919525) baseStart_1919525 baseEnd_1919525 := by
    simpa [prefixWord, tailWord_1919525, baseEnd_1919525] using wordTrace_append hprefix tailTrace_1919525
  have hstable : (prefixWord ++ tailWord_1919525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919525).length < 2 ^ (prefixWord ++ tailWord_1919525).sum := by decide
  have hdescent : baseEnd_1919525 < baseStart_1919525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919636 : List Nat := [2, 4, 2, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_1919636 : Nat := 118140960795 + 1919636 * 2 ^ 59
def prefixEnd_1919636 : Nat := 4983230072969 + 3 ^ 40 * 1919636 * 2
def baseEnd_1919636 : Nat := 985695949674356649021761

theorem tailTrace_1919636 : CollatzResearch.WordTrace tailWord_1919636 prefixEnd_1919636 985695949674356649021761 := by
  unfold tailWord_1919636
  simp only [CollatzResearch.WordTrace]
  refine ⟨35007438436747047286309381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46676584582329396381745841 35007438436747047286309381)
  ·
    refine ⟨6563894706890071366183009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35007438436747047286309381 6563894706890071366183009)
    ·
      refine ⟨4922921030167553524637257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6563894706890071366183009 4922921030167553524637257)
      ·
        refine ⟨3692190772625665143477943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4922921030167553524637257 3692190772625665143477943)
        ·
          refine ⟨5538286158938497715216915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3692190772625665143477943 5538286158938497715216915)
          ·
            refine ⟨8307429238407746572825373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5538286158938497715216915 8307429238407746572825373)
            ·
              refine ⟨3115285964402904964809515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8307429238407746572825373 3115285964402904964809515)
              ·
                refine ⟨4672928946604357447214273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3115285964402904964809515 4672928946604357447214273)
                ·
                  refine ⟨3504696709953268085410705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4672928946604357447214273 3504696709953268085410705)
                  ·
                    refine ⟨2628522532464951064058029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3504696709953268085410705 2628522532464951064058029)
                    ·
                      refine ⟨985695949674356649021761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2628522532464951064058029 985695949674356649021761)
                      ·
                        rfl

theorem cell23_1919636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_1919636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919636 prefixEnd_1919636 := by exact prefixLift 1919636
  have htrace : WordTrace (prefixWord ++ tailWord_1919636) baseStart_1919636 baseEnd_1919636 := by
    simpa [prefixWord, tailWord_1919636, baseEnd_1919636] using wordTrace_append hprefix tailTrace_1919636
  have hstable : (prefixWord ++ tailWord_1919636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919636).length < 2 ^ (prefixWord ++ tailWord_1919636).sum := by decide
  have hdescent : baseEnd_1919636 < baseStart_1919636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919779 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 5, 4, 2]
def baseStart_1919779 : Nat := 118140960795 + 1919779 * 2 ^ 59
def prefixEnd_1919779 : Nat := 4983230072969 + 3 ^ 40 * 1919779 * 2
def baseEnd_1919779 : Nat := 985769377407949589533603

theorem tailTrace_1919779 : CollatzResearch.WordTrace tailWord_1919779 prefixEnd_1919779 985769377407949589533603 := by
  unfold tailWord_1919779
  simp only [CollatzResearch.WordTrace]
  refine ⟨70020092511976029995074391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46680061674650686663382927 70020092511976029995074391)
  ·
    refine ⟨105030138767964044992611587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70020092511976029995074391 105030138767964044992611587)
    ·
      refine ⟨157545208151946067488917381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105030138767964044992611587 157545208151946067488917381)
      ·
        refine ⟨29539726528489887654172009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157545208151946067488917381 29539726528489887654172009)
        ·
          refine ⟨22154794896367415740629007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29539726528489887654172009 22154794896367415740629007)
          ·
            refine ⟨33232192344551123610943511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22154794896367415740629007 33232192344551123610943511)
            ·
              refine ⟨49848288516826685416415267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33232192344551123610943511 49848288516826685416415267)
              ·
                refine ⟨74772432775240028124622901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49848288516826685416415267 74772432775240028124622901)
                ·
                  refine ⟨7009915572678752636683397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74772432775240028124622901 7009915572678752636683397)
                  ·
                    refine ⟨1314359169877266119378137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7009915572678752636683397 1314359169877266119378137)
                    ·
                      refine ⟨985769377407949589533603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1314359169877266119378137 985769377407949589533603)
                      ·
                        rfl

theorem cell23_1919779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 4, 2].length) (baseStart_1919779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919779 prefixEnd_1919779 := by exact prefixLift 1919779
  have htrace : WordTrace (prefixWord ++ tailWord_1919779) baseStart_1919779 baseEnd_1919779 := by
    simpa [prefixWord, tailWord_1919779, baseEnd_1919779] using wordTrace_append hprefix tailTrace_1919779
  have hstable : (prefixWord ++ tailWord_1919779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919779).length < 2 ^ (prefixWord ++ tailWord_1919779).sum := by decide
  have hdescent : baseEnd_1919779 < baseStart_1919779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919829 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 4, 3, 3]
def baseStart_1919829 : Nat := 118140960795 + 1919829 * 2 ^ 59
def prefixEnd_1919829 : Nat := 4983230072969 + 3 ^ 40 * 1919829 * 2
def baseEnd_1919829 : Nat := 985795051440674393908373

theorem tailTrace_1919829 : CollatzResearch.WordTrace tailWord_1919829 prefixEnd_1919829 985795051440674393908373 := by
  unfold tailWord_1919829
  simp only [CollatzResearch.WordTrace]
  refine ⟨70021916161794888534394541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46681277441196592356263027 70021916161794888534394541)
  ·
    refine ⟨26258218560673083200397953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70021916161794888534394541 26258218560673083200397953)
    ·
      refine ⟨19693663920504812400298465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26258218560673083200397953 19693663920504812400298465)
      ·
        refine ⟨14770247940378609300223849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19693663920504812400298465 14770247940378609300223849)
        ·
          refine ⟨11077685955283956975167887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14770247940378609300223849 11077685955283956975167887)
          ·
            refine ⟨16616528932925935462751831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11077685955283956975167887 16616528932925935462751831)
            ·
              refine ⟨24924793399388903194127747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16616528932925935462751831 24924793399388903194127747)
              ·
                refine ⟨37387190099083354791191621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24924793399388903194127747 37387190099083354791191621)
                ·
                  refine ⟨7010098143578129023348429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37387190099083354791191621 7010098143578129023348429)
                  ·
                    refine ⟨2628786803841798383755661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7010098143578129023348429 2628786803841798383755661)
                    ·
                      refine ⟨985795051440674393908373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2628786803841798383755661 985795051440674393908373)
                      ·
                        rfl

theorem cell23_1919829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_1919829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919829 prefixEnd_1919829 := by exact prefixLift 1919829
  have htrace : WordTrace (prefixWord ++ tailWord_1919829) baseStart_1919829 baseEnd_1919829 := by
    simpa [prefixWord, tailWord_1919829, baseEnd_1919829] using wordTrace_append hprefix tailTrace_1919829
  have hstable : (prefixWord ++ tailWord_1919829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919829).length < 2 ^ (prefixWord ++ tailWord_1919829).sum := by decide
  have hdescent : baseEnd_1919829 < baseStart_1919829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919836 : List Nat := [2, 2, 4, 2, 1, 2, 2, 1, 7]
def baseStart_1919836 : Nat := 118140960795 + 1919836 * 2 ^ 59
def prefixEnd_1919836 : Nat := 4983230072969 + 3 ^ 40 * 1919836 * 2
def baseEnd_1919836 : Nat := 109533182867250651835649

theorem tailTrace_1919836 : CollatzResearch.WordTrace tailWord_1919836 prefixEnd_1919836 109533182867250651835649 := by
  unfold tailWord_1919836
  simp only [CollatzResearch.WordTrace]
  refine ⟨35011085736384764364949681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46681447648513019153266241 35011085736384764364949681)
  ·
    refine ⟨26258314302288573273712261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35011085736384764364949681 26258314302288573273712261)
    ·
      refine ⟨4923433931679107488821049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26258314302288573273712261 4923433931679107488821049)
      ·
        refine ⟨3692575448759330616615787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4923433931679107488821049 3692575448759330616615787)
        ·
          refine ⟨5538863173138995924923681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3692575448759330616615787 5538863173138995924923681)
          ·
            refine ⟨4154147379854246943692761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5538863173138995924923681 4154147379854246943692761)
            ·
              refine ⟨3115610534890685207769571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4154147379854246943692761 3115610534890685207769571)
              ·
                refine ⟨4673415802336027811654357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3115610534890685207769571 4673415802336027811654357)
                ·
                  refine ⟨109533182867250651835649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4673415802336027811654357 109533182867250651835649)
                  ·
                    rfl

theorem cell23_1919836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 7].length) (baseStart_1919836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919836 prefixEnd_1919836 := by exact prefixLift 1919836
  have htrace : WordTrace (prefixWord ++ tailWord_1919836) baseStart_1919836 baseEnd_1919836 := by
    simpa [prefixWord, tailWord_1919836, baseEnd_1919836] using wordTrace_append hprefix tailTrace_1919836
  have hstable : (prefixWord ++ tailWord_1919836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919836).length < 2 ^ (prefixWord ++ tailWord_1919836).sum := by decide
  have hdescent : baseEnd_1919836 < baseStart_1919836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919869 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_1919869 : Nat := 118140960795 + 1919869 * 2 ^ 59
def prefixEnd_1919869 : Nat := 4983230072969 + 3 ^ 40 * 1919869 * 2
def baseEnd_1919869 : Nat := 985815590666854237408189

theorem tailTrace_1919869 : CollatzResearch.WordTrace tailWord_1919869 prefixEnd_1919869 985815590666854237408189 := by
  unfold tailWord_1919869
  simp only [CollatzResearch.WordTrace]
  refine ⟨70023375081649975365850661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46682250054433316910567107 70023375081649975365850661)
  ·
    refine ⟨13129382827809370381096999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70023375081649975365850661 13129382827809370381096999)
    ·
      refine ⟨19694074241714055571645499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13129382827809370381096999 19694074241714055571645499)
      ·
        refine ⟨29541111362571083357468249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19694074241714055571645499 29541111362571083357468249)
        ·
          refine ⟨22155833521928312518101187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29541111362571083357468249 22155833521928312518101187)
          ·
            refine ⟨33233750282892468777151781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22155833521928312518101187 33233750282892468777151781)
            ·
              refine ⟨6231328178042337895715959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33233750282892468777151781 6231328178042337895715959)
              ·
                refine ⟨9346992267063506843573939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6231328178042337895715959 9346992267063506843573939)
                ·
                  refine ⟨14020488400595260265360909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9346992267063506843573939 14020488400595260265360909)
                  ·
                    refine ⟨5257683150223222599510341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14020488400595260265360909 5257683150223222599510341)
                    ·
                      refine ⟨985815590666854237408189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5257683150223222599510341 985815590666854237408189)
                      ·
                        rfl

theorem cell23_1919869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_1919869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919869 prefixEnd_1919869 := by exact prefixLift 1919869
  have htrace : WordTrace (prefixWord ++ tailWord_1919869) baseStart_1919869 baseEnd_1919869 := by
    simpa [prefixWord, tailWord_1919869, baseEnd_1919869] using wordTrace_append hprefix tailTrace_1919869
  have hstable : (prefixWord ++ tailWord_1919869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919869).length < 2 ^ (prefixWord ++ tailWord_1919869).sum := by decide
  have hdescent : baseEnd_1919869 < baseStart_1919869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919946 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 3, 5, 2]
def baseStart_1919946 : Nat := 118140960795 + 1919946 * 2 ^ 59
def prefixEnd_1919946 : Nat := 4983230072969 + 3 ^ 40 * 1919946 * 2
def baseEnd_1919946 : Nat := 985855128677250436145335

theorem tailTrace_1919946 : CollatzResearch.WordTrace tailWord_1919946 prefixEnd_1919946 985855128677250436145335 := by
  unfold tailWord_1919946
  simp only [CollatzResearch.WordTrace]
  refine ⟨17506545875592754379100923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46684122334914011677602461 17506545875592754379100923)
  ·
    refine ⟨26259818813389131568651385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17506545875592754379100923 26259818813389131568651385)
    ·
      refine ⟨19694864110041848676488539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26259818813389131568651385 19694864110041848676488539)
      ·
        refine ⟨29542296165062773014732809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19694864110041848676488539 29542296165062773014732809)
        ·
          refine ⟨22156722123797079761049607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29542296165062773014732809 22156722123797079761049607)
          ·
            refine ⟨33235083185695619641574411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22156722123797079761049607 33235083185695619641574411)
            ·
              refine ⟨49852624778543429462361617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33235083185695619641574411 49852624778543429462361617)
              ·
                refine ⟨37389468583907572096771213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49852624778543429462361617 37389468583907572096771213)
                ·
                  refine ⟨14021050718965339536289205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37389468583907572096771213 14021050718965339536289205)
                  ·
                    refine ⟨1314473504903000581527113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14021050718965339536289205 1314473504903000581527113)
                    ·
                      refine ⟨985855128677250436145335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1314473504903000581527113 985855128677250436145335)
                      ·
                        rfl

theorem cell23_1919946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_1919946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919946 prefixEnd_1919946 := by exact prefixLift 1919946
  have htrace : WordTrace (prefixWord ++ tailWord_1919946) baseStart_1919946 baseEnd_1919946 := by
    simpa [prefixWord, tailWord_1919946, baseEnd_1919946] using wordTrace_append hprefix tailTrace_1919946
  have hstable : (prefixWord ++ tailWord_1919946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919946).length < 2 ^ (prefixWord ++ tailWord_1919946).sum := by decide
  have hdescent : baseEnd_1919946 < baseStart_1919946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919956 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_1919956 : Nat := 118140960795 + 1919956 * 2 ^ 59
def prefixEnd_1919956 : Nat := 4983230072969 + 3 ^ 40 * 1919956 * 2
def baseEnd_1919956 : Nat := 328620087827931799006763

theorem tailTrace_1919956 : CollatzResearch.WordTrace tailWord_1919956 prefixEnd_1919956 328620087827931799006763 := by
  unfold tailWord_1919956
  simp only [CollatzResearch.WordTrace]
  refine ⟨35013274116167394612133861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46684365488223192816178481 35013274116167394612133861)
  ·
    refine ⟨6564988896781386489775099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35013274116167394612133861 6564988896781386489775099)
    ·
      refine ⟨9847483345172079734662649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6564988896781386489775099 9847483345172079734662649)
      ·
        refine ⟨7385612508879059800996987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9847483345172079734662649 7385612508879059800996987)
        ·
          refine ⟨11078418763318589701495481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7385612508879059800996987 11078418763318589701495481)
          ·
            refine ⟨8308814072488942276121611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11078418763318589701495481 8308814072488942276121611)
            ·
              refine ⟨12463221108733413414182417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8308814072488942276121611 12463221108733413414182417)
              ·
                refine ⟨9347415831550060060636813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12463221108733413414182417 9347415831550060060636813)
                ·
                  refine ⟨3505280936831272522738805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9347415831550060060636813 3505280936831272522738805)
                  ·
                    refine ⟨328620087827931799006763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3505280936831272522738805 328620087827931799006763)
                    ·
                      rfl

theorem cell23_1919956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_1919956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919956 prefixEnd_1919956 := by exact prefixLift 1919956
  have htrace : WordTrace (prefixWord ++ tailWord_1919956) baseStart_1919956 baseEnd_1919956 := by
    simpa [prefixWord, tailWord_1919956, baseEnd_1919956] using wordTrace_append hprefix tailTrace_1919956
  have hstable : (prefixWord ++ tailWord_1919956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919956).length < 2 ^ (prefixWord ++ tailWord_1919956).sum := by decide
  have hdescent : baseEnd_1919956 < baseStart_1919956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919970 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_1919970 : Nat := 118140960795 + 1919970 * 2 ^ 59
def prefixEnd_1919970 : Nat := 4983230072969 + 3 ^ 40 * 1919970 * 2
def baseEnd_1919970 : Nat := 985867452212958342245225

theorem tailTrace_1919970 : CollatzResearch.WordTrace tailWord_1919970 prefixEnd_1919970 985867452212958342245225 := by
  unfold tailWord_1919970
  simp only [CollatzResearch.WordTrace]
  refine ⟨17506764713571017403819341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46684705902856046410184909 17506764713571017403819341)
  ·
    refine ⟨6565036767589131526432253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17506764713571017403819341 6565036767589131526432253)
    ·
      refine ⟨2461888787845924322412095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6565036767589131526432253 2461888787845924322412095)
      ·
        refine ⟨3692833181768886483618143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2461888787845924322412095 3692833181768886483618143)
        ·
          refine ⟨5539249772653329725427215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3692833181768886483618143 5539249772653329725427215)
          ·
            refine ⟨8308874658979994588140823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5539249772653329725427215 8308874658979994588140823)
            ·
              refine ⟨12463311988469991882211235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8308874658979994588140823 12463311988469991882211235)
              ·
                refine ⟨18694967982704987823316853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12463311988469991882211235 18694967982704987823316853)
                ·
                  refine ⟨1752653248378592608435955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18694967982704987823316853 1752653248378592608435955)
                  ·
                    refine ⟨2628979872567888912653933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1752653248378592608435955 2628979872567888912653933)
                    ·
                      refine ⟨985867452212958342245225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2628979872567888912653933 985867452212958342245225)
                      ·
                        rfl

theorem cell23_1919970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_1919970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919970 prefixEnd_1919970 := by exact prefixLift 1919970
  have htrace : WordTrace (prefixWord ++ tailWord_1919970) baseStart_1919970 baseEnd_1919970 := by
    simpa [prefixWord, tailWord_1919970, baseEnd_1919970] using wordTrace_append hprefix tailTrace_1919970
  have hstable : (prefixWord ++ tailWord_1919970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919970).length < 2 ^ (prefixWord ++ tailWord_1919970).sum := by decide
  have hdescent : baseEnd_1919970 < baseStart_1919970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919976 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_1919976 : Nat := 118140960795 + 1919976 * 2 ^ 59
def prefixEnd_1919976 : Nat := 4983230072969 + 3 ^ 40 * 1919976 * 2
def baseEnd_1919976 : Nat := 985870533096885318770197

theorem tailTrace_1919976 : CollatzResearch.WordTrace tailWord_1919976 prefixEnd_1919976 985870533096885318770197 := by
  unfold tailWord_1919976
  simp only [CollatzResearch.WordTrace]
  refine ⟨35013638846131166319997891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46684851794841555093330521 35013638846131166319997891)
  ·
    refine ⟨52520458269196749479996837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35013638846131166319997891 52520458269196749479996837)
    ·
      refine ⟨9847585925474390527499407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52520458269196749479996837 9847585925474390527499407)
      ·
        refine ⟨14771378888211585791249111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9847585925474390527499407 14771378888211585791249111)
        ·
          refine ⟨22157068332317378686873667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14771378888211585791249111 22157068332317378686873667)
          ·
            refine ⟨33235602498476068030310501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22157068332317378686873667 33235602498476068030310501)
            ·
              refine ⟨6231675468464262755683219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33235602498476068030310501 6231675468464262755683219)
              ·
                refine ⟨9347513202696394133524829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6231675468464262755683219 9347513202696394133524829)
                ·
                  refine ⟨3505317451011147800071811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9347513202696394133524829 3505317451011147800071811)
                  ·
                    refine ⟨5257976176516721700107717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3505317451011147800071811 5257976176516721700107717)
                    ·
                      refine ⟨985870533096885318770197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5257976176516721700107717 985870533096885318770197)
                      ·
                        rfl

theorem cell23_1919976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_1919976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919976 prefixEnd_1919976 := by exact prefixLift 1919976
  have htrace : WordTrace (prefixWord ++ tailWord_1919976) baseStart_1919976 baseEnd_1919976 := by
    simpa [prefixWord, tailWord_1919976, baseEnd_1919976] using wordTrace_append hprefix tailTrace_1919976
  have hstable : (prefixWord ++ tailWord_1919976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919976).length < 2 ^ (prefixWord ++ tailWord_1919976).sum := by decide
  have hdescent : baseEnd_1919976 < baseStart_1919976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919990 : List Nat := [5, 1, 1, 1, 3, 1, 4, 1, 1, 5]
def baseStart_1919990 : Nat := 118140960795 + 1919990 * 2 ^ 59
def prefixEnd_1919990 : Nat := 4983230072969 + 3 ^ 40 * 1919990 * 2
def baseEnd_1919990 : Nat := 328625907275349421331711

theorem tailTrace_1919990 : CollatzResearch.WordTrace tailWord_1919990 prefixEnd_1919990 328625907275349421331711 := by
  unfold tailWord_1919990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4376736769638225814437839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46685192209474408687336949 4376736769638225814437839)
  ·
    refine ⟨6565105154457338721656759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4376736769638225814437839 6565105154457338721656759)
    ·
      refine ⟨9847657731686008082485139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6565105154457338721656759 9847657731686008082485139)
      ·
        refine ⟨14771486597529012123727709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9847657731686008082485139 14771486597529012123727709)
        ·
          refine ⟨5539307474073379546397891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14771486597529012123727709 5539307474073379546397891)
          ·
            refine ⟨8308961211110069319596837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5539307474073379546397891 8308961211110069319596837)
            ·
              refine ⟨1557930227083137997424407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8308961211110069319596837 1557930227083137997424407)
              ·
                refine ⟨2336895340624706996136611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1557930227083137997424407 2336895340624706996136611)
                ·
                  refine ⟨3505343010937060494204917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2336895340624706996136611 3505343010937060494204917)
                  ·
                    refine ⟨328625907275349421331711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3505343010937060494204917 328625907275349421331711)
                    ·
                      rfl

theorem cell23_1919990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_1919990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919990 prefixEnd_1919990 := by exact prefixLift 1919990
  have htrace : WordTrace (prefixWord ++ tailWord_1919990) baseStart_1919990 baseEnd_1919990 := by
    simpa [prefixWord, tailWord_1919990, baseEnd_1919990] using wordTrace_append hprefix tailTrace_1919990
  have hstable : (prefixWord ++ tailWord_1919990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919990).length < 2 ^ (prefixWord ++ tailWord_1919990).sum := by decide
  have hdescent : baseEnd_1919990 < baseStart_1919990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1919993 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 5, 2, 2]
def baseStart_1919993 : Nat := 118140960795 + 1919993 * 2 ^ 59
def prefixEnd_1919993 : Nat := 4983230072969 + 3 ^ 40 * 1919993 * 2
def baseEnd_1919993 : Nat := 985879262268011752257619

theorem tailTrace_1919993 : CollatzResearch.WordTrace tailWord_1919993 prefixEnd_1919993 985879262268011752257619 := by
  unfold tailWord_1919993
  simp only [CollatzResearch.WordTrace]
  refine ⟨70027897733200744543364633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46685265155467163028909755 70027897733200744543364633)
  ·
    refine ⟨52520923299900558407523475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70027897733200744543364633 52520923299900558407523475)
    ·
      refine ⟨78781384949850837611285213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52520923299900558407523475 78781384949850837611285213)
      ·
        refine ⟨29543019356194064104231955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78781384949850837611285213 29543019356194064104231955)
        ·
          refine ⟨44314529034291096156347933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29543019356194064104231955 44314529034291096156347933)
          ·
            refine ⟨16617948387859161058630475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44314529034291096156347933 16617948387859161058630475)
            ·
              refine ⟨24926922581788741587945713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16617948387859161058630475 24926922581788741587945713)
              ·
                refine ⟨18695191936341556190959285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24926922581788741587945713 18695191936341556190959285)
                ·
                  refine ⟨1752674244032020892902433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18695191936341556190959285 1752674244032020892902433)
                  ·
                    refine ⟨1314505683024015669676825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1752674244032020892902433 1314505683024015669676825)
                    ·
                      refine ⟨985879262268011752257619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1314505683024015669676825 985879262268011752257619)
                      ·
                        rfl

theorem cell23_1919993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_1919993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1919993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1919993 prefixEnd_1919993 := by exact prefixLift 1919993
  have htrace : WordTrace (prefixWord ++ tailWord_1919993) baseStart_1919993 baseEnd_1919993 := by
    simpa [prefixWord, tailWord_1919993, baseEnd_1919993] using wordTrace_append hprefix tailTrace_1919993
  have hstable : (prefixWord ++ tailWord_1919993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1919993).length < 2 ^ (prefixWord ++ tailWord_1919993).sum := by decide
  have hdescent : baseEnd_1919993 < baseStart_1919993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1919993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920010 : List Nat := [3, 1, 2, 2, 3, 1, 1, 3, 3, 2, 2]
def baseStart_1920010 : Nat := 118140960795 + 1920010 * 2 ^ 59
def prefixEnd_1920010 : Nat := 4983230072969 + 3 ^ 40 * 1920010 * 2
def baseEnd_1920010 : Nat := 985887991439138185745041

theorem tailTrace_1920010 : CollatzResearch.WordTrace tailWord_1920010 prefixEnd_1920010 985887991439138185745041 := by
  unfold tailWord_1920010
  simp only [CollatzResearch.WordTrace]
  refine ⟨17507129443534789111683371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46685678516092770964488989 17507129443534789111683371)
  ·
    refine ⟨26260694165302183667525057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17507129443534789111683371 26260694165302183667525057)
    ·
      refine ⟨19695520623976637750643793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26260694165302183667525057 19695520623976637750643793)
      ·
        refine ⟨14771640467982478312982845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19695520623976637750643793 14771640467982478312982845)
        ·
          refine ⟨5539365175493429367368567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14771640467982478312982845 5539365175493429367368567)
          ·
            refine ⟨8309047763240144051052851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5539365175493429367368567 8309047763240144051052851)
            ·
              refine ⟨12463571644860216076579277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8309047763240144051052851 12463571644860216076579277)
              ·
                refine ⟨4673839366822581028717229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12463571644860216076579277 4673839366822581028717229)
                ·
                  refine ⟨1752689762558467885768961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4673839366822581028717229 1752689762558467885768961)
                  ·
                    refine ⟨1314517321918850914326721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1752689762558467885768961 1314517321918850914326721)
                    ·
                      refine ⟨985887991439138185745041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1314517321918850914326721 985887991439138185745041)
                      ·
                        rfl

theorem cell23_1920010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_1920010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920010 prefixEnd_1920010 := by exact prefixLift 1920010
  have htrace : WordTrace (prefixWord ++ tailWord_1920010) baseStart_1920010 baseEnd_1920010 := by
    simpa [prefixWord, tailWord_1920010, baseEnd_1920010] using wordTrace_append hprefix tailTrace_1920010
  have hstable : (prefixWord ++ tailWord_1920010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920010).length < 2 ^ (prefixWord ++ tailWord_1920010).sum := by decide
  have hdescent : baseEnd_1920010 < baseStart_1920010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920023 : List Nat := [1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1920023 : Nat := 118140960795 + 1920023 * 2 ^ 59
def prefixEnd_1920023 : Nat := 4983230072969 + 3 ^ 40 * 1920023 * 2
def baseEnd_1920023 : Nat := 985894666687646634882481

theorem tailTrace_1920023 : CollatzResearch.WordTrace tailWord_1920023 prefixEnd_1920023 985894666687646634882481 := by
  unfold tailWord_1920023
  simp only [CollatzResearch.WordTrace]
  refine ⟨70028991923092059666956723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46685994615394706444637815 70028991923092059666956723)
  ·
    refine ⟨105043487884638089500435085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70028991923092059666956723 105043487884638089500435085)
    ·
      refine ⟨39391307956739283562663157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105043487884638089500435085 39391307956739283562663157)
      ·
        refine ⟨3692935120944307833999671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39391307956739283562663157 3692935120944307833999671)
        ·
          refine ⟨5539402681416461750999507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3692935120944307833999671 5539402681416461750999507)
          ·
            refine ⟨8309104022124692626499261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5539402681416461750999507 8309104022124692626499261)
            ·
              refine ⟨3115914008296759734937223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8309104022124692626499261 3115914008296759734937223)
              ·
                refine ⟨4673871012445139602405835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3115914008296759734937223 4673871012445139602405835)
                ·
                  refine ⟨7010806518667709403608753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4673871012445139602405835 7010806518667709403608753)
                  ·
                    refine ⟨5258104889000782052706565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7010806518667709403608753 5258104889000782052706565)
                    ·
                      refine ⟨985894666687646634882481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5258104889000782052706565 985894666687646634882481)
                      ·
                        rfl

theorem cell23_1920023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1920023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920023 prefixEnd_1920023 := by exact prefixLift 1920023
  have htrace : WordTrace (prefixWord ++ tailWord_1920023) baseStart_1920023 baseEnd_1920023 := by
    simpa [prefixWord, tailWord_1920023, baseEnd_1920023] using wordTrace_append hprefix tailTrace_1920023
  have hstable : (prefixWord ++ tailWord_1920023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920023).length < 2 ^ (prefixWord ++ tailWord_1920023).sum := by decide
  have hdescent : baseEnd_1920023 < baseStart_1920023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920033 : List Nat := [1, 2, 3, 2, 3, 3, 2, 7]
def baseStart_1920033 : Nat := 118140960795 + 1920033 * 2 ^ 59
def prefixEnd_1920033 : Nat := 4983230072969 + 3 ^ 40 * 1920033 * 2
def baseEnd_1920033 : Nat := 36514807462747836879905

theorem tailTrace_1920033 : CollatzResearch.WordTrace tailWord_1920033 prefixEnd_1920033 36514807462747836879905 := by
  unfold tailWord_1920033
  simp only [CollatzResearch.WordTrace]
  refine ⟨70029356653055831374820753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46686237768703887583213835 70029356653055831374820753)
  ·
    refine ⟨52522017489791873531115565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70029356653055831374820753 52522017489791873531115565)
    ·
      refine ⟨19695756558671952574168337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52522017489791873531115565 19695756558671952574168337)
      ·
        refine ⟨14771817419003964430626253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19695756558671952574168337 14771817419003964430626253)
        ·
          refine ⟨5539431532126486661484845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14771817419003964430626253 5539431532126486661484845)
          ·
            refine ⟨2077286824547432498056817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5539431532126486661484845 2077286824547432498056817)
            ·
              refine ⟨1557965118410574373542613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2077286824547432498056817 1557965118410574373542613)
              ·
                refine ⟨36514807462747836879905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1557965118410574373542613 36514807462747836879905)
                ·
                  rfl

theorem cell23_1920033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 7].length) (baseStart_1920033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920033 prefixEnd_1920033 := by exact prefixLift 1920033
  have htrace : WordTrace (prefixWord ++ tailWord_1920033) baseStart_1920033 baseEnd_1920033 := by
    simpa [prefixWord, tailWord_1920033, baseEnd_1920033] using wordTrace_append hprefix tailTrace_1920033
  have hstable : (prefixWord ++ tailWord_1920033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920033).length < 2 ^ (prefixWord ++ tailWord_1920033).sum := by decide
  have hdescent : baseEnd_1920033 < baseStart_1920033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920053 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 5, 3, 2]
def baseStart_1920053 : Nat := 118140960795 + 1920053 * 2 ^ 59
def prefixEnd_1920053 : Nat := 4983230072969 + 3 ^ 40 * 1920053 * 2
def baseEnd_1920053 : Nat := 985910071107281517507343

theorem tailTrace_1920053 : CollatzResearch.WordTrace tailWord_1920053 prefixEnd_1920053 985910071107281517507343 := by
  unfold tailWord_1920053
  simp only [CollatzResearch.WordTrace]
  refine ⟨70030086112983374790548813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46686724075322249860365875 70030086112983374790548813)
  ·
    refine ⟨26261282292368765546455805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70030086112983374790548813 26261282292368765546455805)
    ·
      refine ⟨9847980859638287079920927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26261282292368765546455805 9847980859638287079920927)
      ·
        refine ⟨14771971289457430619881391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9847980859638287079920927 14771971289457430619881391)
        ·
          refine ⟨22157956934186145929822087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14771971289457430619881391 22157956934186145929822087)
          ·
            refine ⟨33236935401279218894733131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22157956934186145929822087 33236935401279218894733131)
            ·
              refine ⟨49855403101918828342099697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33236935401279218894733131 49855403101918828342099697)
              ·
                refine ⟨37391552326439121256574773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49855403101918828342099697 37391552326439121256574773)
                ·
                  refine ⟨3505458030603667617803885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37391552326439121256574773 3505458030603667617803885)
                  ·
                    refine ⟨1314546761476375356676457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3505458030603667617803885 1314546761476375356676457)
                    ·
                      refine ⟨985910071107281517507343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1314546761476375356676457 985910071107281517507343)
                      ·
                        rfl

theorem cell23_1920053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_1920053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920053 prefixEnd_1920053 := by exact prefixLift 1920053
  have htrace : WordTrace (prefixWord ++ tailWord_1920053) baseStart_1920053 baseEnd_1920053 := by
    simpa [prefixWord, tailWord_1920053, baseEnd_1920053] using wordTrace_append hprefix tailTrace_1920053
  have hstable : (prefixWord ++ tailWord_1920053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920053).length < 2 ^ (prefixWord ++ tailWord_1920053).sum := by decide
  have hdescent : baseEnd_1920053 < baseStart_1920053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920077 : List Nat := [1, 6, 1, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_1920077 : Nat := 118140960795 + 1920077 * 2 ^ 59
def prefixEnd_1920077 : Nat := 4983230072969 + 3 ^ 40 * 1920077 * 2
def baseEnd_1920077 : Nat := 985922394642989423607233

theorem tailTrace_1920077 : CollatzResearch.WordTrace tailWord_1920077 prefixEnd_1920077 985922394642989423607233 := by
  unfold tailWord_1920077
  simp only [CollatzResearch.WordTrace]
  refine ⟨70030961464896426889422485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46687307643264284592948323 70030961464896426889422485)
  ·
    refine ⟨3282701318667020010441679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70030961464896426889422485 3282701318667020010441679)
    ·
      refine ⟨4924051978000530015662519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3282701318667020010441679 4924051978000530015662519)
      ·
        refine ⟨7386077967000795023493779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4924051978000530015662519 7386077967000795023493779)
        ·
          refine ⟨11079116950501192535240669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7386077967000795023493779 11079116950501192535240669)
          ·
            refine ⟨4154668856437947200715251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11079116950501192535240669 4154668856437947200715251)
            ·
              refine ⟨6232003284656920801072877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4154668856437947200715251 6232003284656920801072877)
              ·
                refine ⟨2337001231746345300402329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6232003284656920801072877 2337001231746345300402329)
                ·
                  refine ⟨1752750923809758975301747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2337001231746345300402329 1752750923809758975301747)
                  ·
                    refine ⟨2629126385714638462952621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1752750923809758975301747 2629126385714638462952621)
                    ·
                      refine ⟨985922394642989423607233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2629126385714638462952621 985922394642989423607233)
                      ·
                        rfl

theorem cell23_1920077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_1920077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920077 prefixEnd_1920077 := by exact prefixLift 1920077
  have htrace : WordTrace (prefixWord ++ tailWord_1920077) baseStart_1920077 baseEnd_1920077 := by
    simpa [prefixWord, tailWord_1920077, baseEnd_1920077] using wordTrace_append hprefix tailTrace_1920077
  have hstable : (prefixWord ++ tailWord_1920077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920077).length < 2 ^ (prefixWord ++ tailWord_1920077).sum := by decide
  have hdescent : baseEnd_1920077 < baseStart_1920077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920186 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6]
def baseStart_1920186 : Nat := 118140960795 + 1920186 * 2 ^ 59
def prefixEnd_1920186 : Nat := 4983230072969 + 3 ^ 40 * 1920186 * 2
def baseEnd_1920186 : Nat := 985978364034329497144231

theorem tailTrace_1920186 : CollatzResearch.WordTrace tailWord_1920186 prefixEnd_1920186 985978364034329497144231 := by
  unfold tailWord_1920186
  simp only [CollatzResearch.WordTrace]
  refine ⟨17508734255375384626285103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46689958014334359003426941 17508734255375384626285103)
  ·
    refine ⟨26263101383063076939427655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17508734255375384626285103 26263101383063076939427655)
    ·
      refine ⟨39394652074594615409141483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26263101383063076939427655 39394652074594615409141483)
      ·
        refine ⟨59091978111891923113712225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39394652074594615409141483 59091978111891923113712225)
        ·
          refine ⟨44318983583918942335284169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59091978111891923113712225 44318983583918942335284169)
          ·
            refine ⟨33239237687939206751463127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44318983583918942335284169 33239237687939206751463127)
            ·
              refine ⟨49858856531908810127194691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33239237687939206751463127 49858856531908810127194691)
              ·
                refine ⟨74788284797863215190792037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49858856531908810127194691 74788284797863215190792037)
                ·
                  refine ⟨14022803399599352848273507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74788284797863215190792037 14022803399599352848273507)
                  ·
                    refine ⟨21034205099399029272410261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14022803399599352848273507 21034205099399029272410261)
                    ·
                      refine ⟨985978364034329497144231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21034205099399029272410261 985978364034329497144231)
                      ·
                        rfl

theorem cell23_1920186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_1920186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920186 prefixEnd_1920186 := by exact prefixLift 1920186
  have htrace : WordTrace (prefixWord ++ tailWord_1920186) baseStart_1920186 baseEnd_1920186 := by
    simpa [prefixWord, tailWord_1920186, baseEnd_1920186] using wordTrace_append hprefix tailTrace_1920186
  have hstable : (prefixWord ++ tailWord_1920186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920186).length < 2 ^ (prefixWord ++ tailWord_1920186).sum := by decide
  have hdescent : baseEnd_1920186 < baseStart_1920186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920210 : List Nat := [3, 2, 2, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_1920210 : Nat := 118140960795 + 1920210 * 2 ^ 59
def prefixEnd_1920210 : Nat := 4983230072969 + 3 ^ 40 * 1920210 * 2
def baseEnd_1920210 : Nat := 985990687570037403244121

theorem tailTrace_1920210 : CollatzResearch.WordTrace tailWord_1920210 prefixEnd_1920210 985990687570037403244121 := by
  unfold tailWord_1920210
  simp only [CollatzResearch.WordTrace]
  refine ⟨17508953093353647651003521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46690541582276393736009389 17508953093353647651003521)
  ·
    refine ⟨13131714820015235738252641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17508953093353647651003521 13131714820015235738252641)
    ·
      refine ⟨9848786115011426803689481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13131714820015235738252641 9848786115011426803689481)
      ·
        refine ⟨7386589586258570102767111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9848786115011426803689481 7386589586258570102767111)
        ·
          refine ⟨11079884379387855154150667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7386589586258570102767111 11079884379387855154150667)
          ·
            refine ⟨16619826569081782731226001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11079884379387855154150667 16619826569081782731226001)
            ·
              refine ⟨12464869926811337048419501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16619826569081782731226001 12464869926811337048419501)
              ·
                refine ⟨4674326222554251393157313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12464869926811337048419501 4674326222554251393157313)
                ·
                  refine ⟨3505744666915688544867985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4674326222554251393157313 3505744666915688544867985)
                  ·
                    refine ⟨2629308500186766408650989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3505744666915688544867985 2629308500186766408650989)
                    ·
                      refine ⟨985990687570037403244121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2629308500186766408650989 985990687570037403244121)
                      ·
                        rfl

theorem cell23_1920210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_1920210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920210 prefixEnd_1920210 := by exact prefixLift 1920210
  have htrace : WordTrace (prefixWord ++ tailWord_1920210) baseStart_1920210 baseEnd_1920210 := by
    simpa [prefixWord, tailWord_1920210, baseEnd_1920210] using wordTrace_append hprefix tailTrace_1920210
  have hstable : (prefixWord ++ tailWord_1920210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920210).length < 2 ^ (prefixWord ++ tailWord_1920210).sum := by decide
  have hdescent : baseEnd_1920210 < baseStart_1920210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920213 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 8]
def baseStart_1920213 : Nat := 118140960795 + 1920213 * 2 ^ 59
def prefixEnd_1920213 : Nat := 4983230072969 + 3 ^ 40 * 1920213 * 2
def baseEnd_1920213 : Nat := 109554692001333432389623

theorem tailTrace_1920213 : CollatzResearch.WordTrace tailWord_1920213 prefixEnd_1920213 109554692001333432389623 := by
  unfold tailWord_1920213
  simp only [CollatzResearch.WordTrace]
  refine ⟨70035921792403722116373293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46690614528269148077582195 70035921792403722116373293)
  ·
    refine ⟨26263470672151395793639985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70035921792403722116373293 26263470672151395793639985)
    ·
      refine ⟨19697603004113546845229989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26263470672151395793639985 19697603004113546845229989)
      ·
        refine ⟨3693300563271290033480623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19697603004113546845229989 3693300563271290033480623)
        ·
          refine ⟨5539950844906935050220935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3693300563271290033480623 5539950844906935050220935)
          ·
            refine ⟨8309926267360402575331403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5539950844906935050220935 8309926267360402575331403)
            ·
              refine ⟨12464889401040603862997105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8309926267360402575331403 12464889401040603862997105)
              ·
                refine ⟨9348667050780452897247829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12464889401040603862997105 9348667050780452897247829)
                ·
                  refine ⟨109554692001333432389623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9348667050780452897247829 109554692001333432389623)
                  ·
                    rfl

theorem cell23_1920213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 8].length) (baseStart_1920213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920213 prefixEnd_1920213 := by exact prefixLift 1920213
  have htrace : WordTrace (prefixWord ++ tailWord_1920213) baseStart_1920213 baseEnd_1920213 := by
    simpa [prefixWord, tailWord_1920213, baseEnd_1920213] using wordTrace_append hprefix tailTrace_1920213
  have hstable : (prefixWord ++ tailWord_1920213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920213).length < 2 ^ (prefixWord ++ tailWord_1920213).sum := by decide
  have hdescent : baseEnd_1920213 < baseStart_1920213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920234 : List Nat := [3, 1, 3, 1, 1, 4, 3, 2, 1, 4]
def baseStart_1920234 : Nat := 118140960795 + 1920234 * 2 ^ 59
def prefixEnd_1920234 : Nat := 4983230072969 + 3 ^ 40 * 1920234 * 2
def baseEnd_1920234 : Nat := 328667670368581769781337

theorem tailTrace_1920234 : CollatzResearch.WordTrace tailWord_1920234 prefixEnd_1920234 328667670368581769781337 := by
  unfold tailWord_1920234
  simp only [CollatzResearch.WordTrace]
  refine ⟨17509171931331910675721939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46691125150218428468591837 17509171931331910675721939)
  ·
    refine ⟨26263757896997866013582909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17509171931331910675721939 26263757896997866013582909)
    ·
      refine ⟨9848909211374199755093591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26263757896997866013582909 9848909211374199755093591)
      ·
        refine ⟨14773363817061299632640387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9848909211374199755093591 14773363817061299632640387)
        ·
          refine ⟨22160045725591949448960581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14773363817061299632640387 22160045725591949448960581)
          ·
            refine ⟨4155008573548490521680109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22160045725591949448960581 4155008573548490521680109)
            ·
              refine ⟨1558128215080683945630041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4155008573548490521680109 1558128215080683945630041)
              ·
                refine ⟨1168596161310512959222531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1558128215080683945630041 1168596161310512959222531)
                ·
                  refine ⟨1752894241965769438833797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1168596161310512959222531 1752894241965769438833797)
                  ·
                    refine ⟨328667670368581769781337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1752894241965769438833797 328667670368581769781337)
                    ·
                      rfl

theorem cell23_1920234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_1920234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920234 prefixEnd_1920234 := by exact prefixLift 1920234
  have htrace : WordTrace (prefixWord ++ tailWord_1920234) baseStart_1920234 baseEnd_1920234 := by
    simpa [prefixWord, tailWord_1920234, baseEnd_1920234] using wordTrace_append hprefix tailTrace_1920234
  have hstable : (prefixWord ++ tailWord_1920234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920234).length < 2 ^ (prefixWord ++ tailWord_1920234).sum := by decide
  have hdescent : baseEnd_1920234 < baseStart_1920234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920250 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2]
def baseStart_1920250 : Nat := 118140960795 + 1920250 * 2 ^ 59
def prefixEnd_1920250 : Nat := 4983230072969 + 3 ^ 40 * 1920250 * 2
def baseEnd_1920250 : Nat := 986011226796217246743937

theorem tailTrace_1920250 : CollatzResearch.WordTrace tailWord_1920250 prefixEnd_1920250 986011226796217246743937 := by
  unfold tailWord_1920250
  simp only [CollatzResearch.WordTrace]
  refine ⟨17509317823317419358867551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46691514195513118290313469 17509317823317419358867551)
  ·
    refine ⟨26263976734976129038301327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17509317823317419358867551 26263976734976129038301327)
    ·
      refine ⟨39395965102464193557451991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26263976734976129038301327 39395965102464193557451991)
      ·
        refine ⟨59093947653696290336177987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39395965102464193557451991 59093947653696290336177987)
        ·
          refine ⟨88640921480544435504266981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59093947653696290336177987 88640921480544435504266981)
          ·
            refine ⟨16620172777602081657050059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88640921480544435504266981 16620172777602081657050059)
            ·
              refine ⟨24930259166403122485575089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16620172777602081657050059 24930259166403122485575089)
              ·
                refine ⟨18697694374802341864181317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24930259166403122485575089 18697694374802341864181317)
                ·
                  refine ⟨3505817695275439099533997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18697694374802341864181317 3505817695275439099533997)
                  ·
                    refine ⟨1314681635728289662325249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3505817695275439099533997 1314681635728289662325249)
                    ·
                      refine ⟨986011226796217246743937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1314681635728289662325249 986011226796217246743937)
                      ·
                        rfl

theorem cell23_1920250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 4, 3, 2].length) (baseStart_1920250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920250 prefixEnd_1920250 := by exact prefixLift 1920250
  have htrace : WordTrace (prefixWord ++ tailWord_1920250) baseStart_1920250 baseEnd_1920250 := by
    simpa [prefixWord, tailWord_1920250, baseEnd_1920250] using wordTrace_append hprefix tailTrace_1920250
  have hstable : (prefixWord ++ tailWord_1920250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920250).length < 2 ^ (prefixWord ++ tailWord_1920250).sum := by decide
  have hdescent : baseEnd_1920250 < baseStart_1920250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920260 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 3, 5]
def baseStart_1920260 : Nat := 118140960795 + 1920260 * 2 ^ 59
def prefixEnd_1920260 : Nat := 4983230072969 + 3 ^ 40 * 1920260 * 2
def baseEnd_1920260 : Nat := 328672120534254069206297

theorem tailTrace_1920260 : CollatzResearch.WordTrace tailWord_1920260 prefixEnd_1920260 328672120534254069206297 := by
  unfold tailWord_1920260
  simp only [CollatzResearch.WordTrace]
  refine ⟨35018818011616724571667117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46691757348822299428889489 35018818011616724571667117)
  ·
    refine ⟨13132056754356271714375169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35018818011616724571667117 13132056754356271714375169)
    ·
      refine ⟨9849042565767203785781377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13132056754356271714375169 9849042565767203785781377)
      ·
        refine ⟨7386781924325402839336033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9849042565767203785781377 7386781924325402839336033)
        ·
          refine ⟨5540086443244052129502025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7386781924325402839336033 5540086443244052129502025)
          ·
            refine ⟨4155064832433039097126519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5540086443244052129502025 4155064832433039097126519)
            ·
              refine ⟨6232597248649558645689779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4155064832433039097126519 6232597248649558645689779)
              ·
                refine ⟨9348895872974337968534669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6232597248649558645689779 9348895872974337968534669)
                ·
                  refine ⟨3505835952365376738200501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9348895872974337968534669 3505835952365376738200501)
                  ·
                    refine ⟨328672120534254069206297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3505835952365376738200501 328672120534254069206297)
                    ·
                      rfl

theorem cell23_1920260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_1920260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920260 prefixEnd_1920260 := by exact prefixLift 1920260
  have htrace : WordTrace (prefixWord ++ tailWord_1920260) baseStart_1920260 baseEnd_1920260 := by
    simpa [prefixWord, tailWord_1920260, baseEnd_1920260] using wordTrace_append hprefix tailTrace_1920260
  have hstable : (prefixWord ++ tailWord_1920260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920260).length < 2 ^ (prefixWord ++ tailWord_1920260).sum := by decide
  have hdescent : baseEnd_1920260 < baseStart_1920260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920267 : List Nat := [1, 1, 1, 1, 5, 4, 2, 1, 2, 3, 2]
def baseStart_1920267 : Nat := 118140960795 + 1920267 * 2 ^ 59
def prefixEnd_1920267 : Nat := 4983230072969 + 3 ^ 40 * 1920267 * 2
def baseEnd_1920267 : Nat := 986019955967343680231359

theorem tailTrace_1920267 : CollatzResearch.WordTrace tailWord_1920267 prefixEnd_1920267 986019955967343680231359 := by
  unfold tailWord_1920267
  simp only [CollatzResearch.WordTrace]
  refine ⟨70037891334208089338839055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46691927556138726225892703 70037891334208089338839055)
  ·
    refine ⟨105056837001312134008258583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70037891334208089338839055 105056837001312134008258583)
    ·
      refine ⟨157585255501968201012387875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105056837001312134008258583 157585255501968201012387875)
      ·
        refine ⟨236377883252952301518581813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157585255501968201012387875 236377883252952301518581813)
        ·
          refine ⟨22160426554964278267367045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 236377883252952301518581813 22160426554964278267367045)
          ·
            refine ⟨4155079979055802175131321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22160426554964278267367045 4155079979055802175131321)
            ·
              refine ⟨3116309984291851631348491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4155079979055802175131321 3116309984291851631348491)
              ·
                refine ⟨4674464976437777447022737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3116309984291851631348491 4674464976437777447022737)
                ·
                  refine ⟨3505848732328333085267053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4674464976437777447022737 3505848732328333085267053)
                  ·
                    refine ⟨1314693274623124906975145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3505848732328333085267053 1314693274623124906975145)
                    ·
                      refine ⟨986019955967343680231359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1314693274623124906975145 986019955967343680231359)
                      ·
                        rfl

theorem cell23_1920267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 3, 2].length) (baseStart_1920267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920267 prefixEnd_1920267 := by exact prefixLift 1920267
  have htrace : WordTrace (prefixWord ++ tailWord_1920267) baseStart_1920267 baseEnd_1920267 := by
    simpa [prefixWord, tailWord_1920267, baseEnd_1920267] using wordTrace_append hprefix tailTrace_1920267
  have hstable : (prefixWord ++ tailWord_1920267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920267).length < 2 ^ (prefixWord ++ tailWord_1920267).sum := by decide
  have hdescent : baseEnd_1920267 < baseStart_1920267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920273 : List Nat := [1, 2, 2, 1, 1, 4, 3, 2, 1, 6]
def baseStart_1920273 : Nat := 118140960795 + 1920273 * 2 ^ 59
def prefixEnd_1920273 : Nat := 4983230072969 + 3 ^ 40 * 1920273 * 2
def baseEnd_1920273 : Nat := 328674345617090218918777

theorem tailTrace_1920273 : CollatzResearch.WordTrace tailWord_1920273 prefixEnd_1920273 328674345617090218918777 := by
  unfold tailWord_1920273
  simp only [CollatzResearch.WordTrace]
  refine ⟨70038110172186352363557473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46692073448124234909038315 70038110172186352363557473)
  ·
    refine ⟨52528582629139764272668105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70038110172186352363557473 52528582629139764272668105)
    ·
      refine ⟨39396436971854823204501079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52528582629139764272668105 39396436971854823204501079)
      ·
        refine ⟨59094655457782234806751619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39396436971854823204501079 59094655457782234806751619)
        ·
          refine ⟨88641983186673352210127429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59094655457782234806751619 88641983186673352210127429)
          ·
            refine ⟨16620371847501253539398893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88641983186673352210127429 16620371847501253539398893)
            ·
              refine ⟨6232639442812970077274585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16620371847501253539398893 6232639442812970077274585)
              ·
                refine ⟨4674479582109727557955939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6232639442812970077274585 4674479582109727557955939)
                ·
                  refine ⟨7011719373164591336933909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4674479582109727557955939 7011719373164591336933909)
                  ·
                    refine ⟨328674345617090218918777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7011719373164591336933909 328674345617090218918777)
                    ·
                      rfl

theorem cell23_1920273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_1920273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920273 prefixEnd_1920273 := by exact prefixLift 1920273
  have htrace : WordTrace (prefixWord ++ tailWord_1920273) baseStart_1920273 baseEnd_1920273 := by
    simpa [prefixWord, tailWord_1920273, baseEnd_1920273] using wordTrace_append hprefix tailTrace_1920273
  have hstable : (prefixWord ++ tailWord_1920273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920273).length < 2 ^ (prefixWord ++ tailWord_1920273).sum := by decide
  have hdescent : baseEnd_1920273 < baseStart_1920273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920291 : List Nat := [1, 1, 1, 4, 2, 5, 2, 2, 1, 1, 3]
def baseStart_1920291 : Nat := 118140960795 + 1920291 * 2 ^ 59
def prefixEnd_1920291 : Nat := 4983230072969 + 3 ^ 40 * 1920291 * 2
def baseEnd_1920291 : Nat := 986032279503051586331249

theorem tailTrace_1920291 : CollatzResearch.WordTrace tailWord_1920291 prefixEnd_1920291 986032279503051586331249 := by
  unfold tailWord_1920291
  simp only [CollatzResearch.WordTrace]
  refine ⟨70038766686121141437712727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46692511124080760958475151 70038766686121141437712727)
  ·
    refine ⟨105058150029181712156569091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70038766686121141437712727 105058150029181712156569091)
    ·
      refine ⟨157587225043772568234853637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105058150029181712156569091 157587225043772568234853637)
      ·
        refine ⟨29547604695707356544035057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157587225043772568234853637 29547604695707356544035057)
        ·
          refine ⟨22160703521780517408026293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29547604695707356544035057 22160703521780517408026293)
          ·
            refine ⟨2077565955166923507002465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22160703521780517408026293 2077565955166923507002465)
            ·
              refine ⟨1558174466375192630251849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2077565955166923507002465 1558174466375192630251849)
              ·
                refine ⟨1168630849781394472688887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1558174466375192630251849 1168630849781394472688887)
                ·
                  refine ⟨1752946274672091709033331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1168630849781394472688887 1752946274672091709033331)
                  ·
                    refine ⟨2629419412008137563549997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1752946274672091709033331 2629419412008137563549997)
                    ·
                      refine ⟨986032279503051586331249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2629419412008137563549997 986032279503051586331249)
                      ·
                        rfl

theorem cell23_1920291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 1, 1, 3].length) (baseStart_1920291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920291 prefixEnd_1920291 := by exact prefixLift 1920291
  have htrace : WordTrace (prefixWord ++ tailWord_1920291) baseStart_1920291 baseEnd_1920291 := by
    simpa [prefixWord, tailWord_1920291, baseEnd_1920291] using wordTrace_append hprefix tailTrace_1920291
  have hstable : (prefixWord ++ tailWord_1920291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920291).length < 2 ^ (prefixWord ++ tailWord_1920291).sum := by decide
  have hdescent : baseEnd_1920291 < baseStart_1920291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920353 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_1920353 : Nat := 118140960795 + 1920353 * 2 ^ 59
def prefixEnd_1920353 : Nat := 4983230072969 + 3 ^ 40 * 1920353 * 2
def baseEnd_1920353 : Nat := 986064115303630343755963

theorem tailTrace_1920353 : CollatzResearch.WordTrace tailWord_1920353 prefixEnd_1920353 986064115303630343755963 := by
  unfold tailWord_1920353
  simp only [CollatzResearch.WordTrace]
  refine ⟨70041028011896526026469713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46694018674597684017646475 70041028011896526026469713)
  ·
    refine ⟨52530771008922394519852285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70041028011896526026469713 52530771008922394519852285)
    ·
      refine ⟨19699039128345897944944607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52530771008922394519852285 19699039128345897944944607)
      ·
        refine ⟨29548558692518846917416911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19699039128345897944944607 29548558692518846917416911)
        ·
          refine ⟨44322838038778270376125367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29548558692518846917416911 44322838038778270376125367)
          ·
            refine ⟨66484257058167405564188051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44322838038778270376125367 66484257058167405564188051)
            ·
              refine ⟨99726385587251108346282077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66484257058167405564188051 99726385587251108346282077)
              ·
                refine ⟨37397394595219165629855779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99726385587251108346282077 37397394595219165629855779)
                ·
                  refine ⟨56096091892828748444783669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37397394595219165629855779 56096091892828748444783669)
                  ·
                    refine ⟨5259008614952695166698469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56096091892828748444783669 5259008614952695166698469)
                    ·
                      refine ⟨986064115303630343755963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5259008614952695166698469 986064115303630343755963)
                      ·
                        rfl

theorem cell23_1920353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_1920353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920353 prefixEnd_1920353 := by exact prefixLift 1920353
  have htrace : WordTrace (prefixWord ++ tailWord_1920353) baseStart_1920353 baseEnd_1920353 := by
    simpa [prefixWord, tailWord_1920353, baseEnd_1920353] using wordTrace_append hprefix tailTrace_1920353
  have hstable : (prefixWord ++ tailWord_1920353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920353).length < 2 ^ (prefixWord ++ tailWord_1920353).sum := by decide
  have hdescent : baseEnd_1920353 < baseStart_1920353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920382 : List Nat := [4, 2, 3, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_1920382 : Nat := 118140960795 + 1920382 * 2 ^ 59
def prefixEnd_1920382 : Nat := 4983230072969 + 3 ^ 40 * 1920382 * 2
def baseEnd_1920382 : Nat := 986079006242610730293331

theorem tailTrace_1920382 : CollatzResearch.WordTrace tailWord_1920382 prefixEnd_1920382 986079006242610730293331 := by
  unfold tailWord_1920382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8755260716098932997409425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 46694723819194309319516933 8755260716098932997409425)
  ·
    refine ⟨6566445537074199748057069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8755260716098932997409425 6566445537074199748057069)
    ·
      refine ⟨2462417076402824905521401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6566445537074199748057069 2462417076402824905521401)
      ·
        refine ⟨1846812807302118679141051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2462417076402824905521401 1846812807302118679141051)
        ·
          refine ⟨2770219210953178018711577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1846812807302118679141051 2770219210953178018711577)
          ·
            refine ⟨2077664408214883514033683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2770219210953178018711577 2077664408214883514033683)
            ·
              refine ⟨3116496612322325271050525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2077664408214883514033683 3116496612322325271050525)
              ·
                refine ⟨1168686229620871976643947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3116496612322325271050525 1168686229620871976643947)
                ·
                  refine ⟨1753029344431307964965921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1168686229620871976643947 1753029344431307964965921)
                  ·
                    refine ⟨1314772008323480973724441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1753029344431307964965921 1314772008323480973724441)
                    ·
                      refine ⟨986079006242610730293331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1314772008323480973724441 986079006242610730293331)
                      ·
                        rfl

theorem cell23_1920382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_1920382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920382 prefixEnd_1920382 := by exact prefixLift 1920382
  have htrace : WordTrace (prefixWord ++ tailWord_1920382) baseStart_1920382 baseEnd_1920382 := by
    simpa [prefixWord, tailWord_1920382, baseEnd_1920382] using wordTrace_append hprefix tailTrace_1920382
  have hstable : (prefixWord ++ tailWord_1920382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920382).length < 2 ^ (prefixWord ++ tailWord_1920382).sum := by decide
  have hdescent : baseEnd_1920382 < baseStart_1920382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920420 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 1, 5, 3]
def baseStart_1920420 : Nat := 118140960795 + 1920420 * 2 ^ 59
def prefixEnd_1920420 : Nat := 4983230072969 + 3 ^ 40 * 1920420 * 2
def baseEnd_1920420 : Nat := 986098518507481581618155

theorem tailTrace_1920420 : CollatzResearch.WordTrace tailWord_1920420 prefixEnd_1920420 986098518507481581618155 := by
  unfold tailWord_1920420
  simp only [CollatzResearch.WordTrace]
  refine ⟨35021735851326898234579357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46695647801769197646105809 35021735851326898234579357)
  ·
    refine ⟨13133150944247586837967259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35021735851326898234579357 13133150944247586837967259)
    ·
      refine ⟨19699726416371380256950889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13133150944247586837967259 19699726416371380256950889)
      ·
        refine ⟨14774794812278535192713167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19699726416371380256950889 14774794812278535192713167)
        ·
          refine ⟨22162192218417802789069751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14774794812278535192713167 22162192218417802789069751)
          ·
            refine ⟨33243288327626704183604627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22162192218417802789069751 33243288327626704183604627)
            ·
              refine ⟨49864932491440056275406941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33243288327626704183604627 49864932491440056275406941)
              ·
                refine ⟨18699349684290021103277603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49864932491440056275406941 18699349684290021103277603)
                ·
                  refine ⟨28049024526435031654916405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18699349684290021103277603 28049024526435031654916405)
                  ·
                    refine ⟨2629596049353284217648413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28049024526435031654916405 2629596049353284217648413)
                    ·
                      refine ⟨986098518507481581618155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2629596049353284217648413 986098518507481581618155)
                      ·
                        rfl

theorem cell23_1920420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_1920420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920420 prefixEnd_1920420 := by exact prefixLift 1920420
  have htrace : WordTrace (prefixWord ++ tailWord_1920420) baseStart_1920420 baseEnd_1920420 := by
    simpa [prefixWord, tailWord_1920420, baseEnd_1920420] using wordTrace_append hprefix tailTrace_1920420
  have hstable : (prefixWord ++ tailWord_1920420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920420).length < 2 ^ (prefixWord ++ tailWord_1920420).sum := by decide
  have hdescent : baseEnd_1920420 < baseStart_1920420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920440 : List Nat := [2, 1, 2, 1, 2, 2, 3, 3, 2, 5]
def baseStart_1920440 : Nat := 118140960795 + 1920440 * 2 ^ 59
def prefixEnd_1920440 : Nat := 4983230072969 + 3 ^ 40 * 1920440 * 2
def baseEnd_1920440 : Nat := 328702929373523834456021

theorem tailTrace_1920440 : CollatzResearch.WordTrace tailWord_1920440 prefixEnd_1920440 328702929373523834456021 := by
  unfold tailWord_1920440
  simp only [CollatzResearch.WordTrace]
  refine ⟨35022100581290669942443387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46696134108387559923257849 35022100581290669942443387)
  ·
    refine ⟨52533150871936004913665081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35022100581290669942443387 52533150871936004913665081)
    ·
      refine ⟨39399863153952003685248811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52533150871936004913665081 39399863153952003685248811)
      ·
        refine ⟨59099794730928005527873217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39399863153952003685248811 59099794730928005527873217)
        ·
          refine ⟨44324846048196004145904913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59099794730928005527873217 44324846048196004145904913)
          ·
            refine ⟨33243634536147003109428685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44324846048196004145904913 33243634536147003109428685)
            ·
              refine ⟨12466362951055126166035757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33243634536147003109428685 12466362951055126166035757)
              ·
                refine ⟨4674886106645672312263409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12466362951055126166035757 4674886106645672312263409)
                ·
                  refine ⟨3506164579984254234197557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4674886106645672312263409 3506164579984254234197557)
                  ·
                    refine ⟨328702929373523834456021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3506164579984254234197557 328702929373523834456021)
                    ·
                      rfl

theorem cell23_1920440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_1920440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920440 prefixEnd_1920440 := by exact prefixLift 1920440
  have htrace : WordTrace (prefixWord ++ tailWord_1920440) baseStart_1920440 baseEnd_1920440 := by
    simpa [prefixWord, tailWord_1920440, baseEnd_1920440] using wordTrace_append hprefix tailTrace_1920440
  have hstable : (prefixWord ++ tailWord_1920440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920440).length < 2 ^ (prefixWord ++ tailWord_1920440).sum := by decide
  have hdescent : baseEnd_1920440 < baseStart_1920440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920487 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 5, 4]
def baseStart_1920487 : Nat := 118140960795 + 1920487 * 2 ^ 59
def prefixEnd_1920487 : Nat := 4983230072969 + 3 ^ 40 * 1920487 * 2
def baseEnd_1920487 : Nat := 328710973903777606493449

theorem tailTrace_1920487 : CollatzResearch.WordTrace tailWord_1920487 prefixEnd_1920487 328710973903777606493449 := by
  unfold tailWord_1920487
  simp only [CollatzResearch.WordTrace]
  refine ⟨70045915393411066911847715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46697276928940711274565143 70045915393411066911847715)
  ·
    refine ⟨105068873090116600367771573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70045915393411066911847715 105068873090116600367771573)
    ·
      refine ⟨9850206852198431284478585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105068873090116600367771573 9850206852198431284478585)
      ·
        refine ⟨7387655139148823463358939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9850206852198431284478585 7387655139148823463358939)
        ·
          refine ⟨11081482708723235195038409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7387655139148823463358939 11081482708723235195038409)
          ·
            refine ⟨8311112031542426396278807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11081482708723235195038409 8311112031542426396278807)
            ·
              refine ⟨12466668047313639594418211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8311112031542426396278807 12466668047313639594418211)
              ·
                refine ⟨18700002070970459391627317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12466668047313639594418211 18700002070970459391627317)
                ·
                  refine ⟨1753125194153480567965061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18700002070970459391627317 1753125194153480567965061)
                  ·
                    refine ⟨328710973903777606493449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1753125194153480567965061 328710973903777606493449)
                    ·
                      rfl

theorem cell23_1920487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_1920487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920487 prefixEnd_1920487 := by exact prefixLift 1920487
  have htrace : WordTrace (prefixWord ++ tailWord_1920487) baseStart_1920487 baseEnd_1920487 := by
    simpa [prefixWord, tailWord_1920487, baseEnd_1920487] using wordTrace_append hprefix tailTrace_1920487
  have hstable : (prefixWord ++ tailWord_1920487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920487).length < 2 ^ (prefixWord ++ tailWord_1920487).sum := by decide
  have hdescent : baseEnd_1920487 < baseStart_1920487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920497 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 1, 4, 3]
def baseStart_1920497 : Nat := 118140960795 + 1920497 * 2 ^ 59
def prefixEnd_1920497 : Nat := 4983230072969 + 3 ^ 40 * 1920497 * 2
def baseEnd_1920497 : Nat := 986138056517877780355301

theorem tailTrace_1920497 : CollatzResearch.WordTrace tailWord_1920497 prefixEnd_1920497 986138056517877780355301 := by
  unfold tailWord_1920497
  simp only [CollatzResearch.WordTrace]
  refine ⟨70046280123374838619711745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46697520082249892413141163 70046280123374838619711745)
  ·
    refine ⟨52534710092531128964783809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70046280123374838619711745 52534710092531128964783809)
    ·
      refine ⟨39401032569398346723587857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52534710092531128964783809 39401032569398346723587857)
      ·
        refine ⟨29550774427048760042690893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39401032569398346723587857 29550774427048760042690893)
        ·
          refine ⟨11081540410143285016009085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29550774427048760042690893 11081540410143285016009085)
          ·
            refine ⟨4155577653803731881003407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11081540410143285016009085 4155577653803731881003407)
            ·
              refine ⟨6233366480705597821505111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4155577653803731881003407 6233366480705597821505111)
              ·
                refine ⟨9350049721058396732257667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6233366480705597821505111 9350049721058396732257667)
                ·
                  refine ⟨14025074581587595098386501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9350049721058396732257667 14025074581587595098386501)
                  ·
                    refine ⟨2629701484047674080947469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14025074581587595098386501 2629701484047674080947469)
                    ·
                      refine ⟨986138056517877780355301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2629701484047674080947469 986138056517877780355301)
                      ·
                        rfl

theorem cell23_1920497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_1920497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920497 prefixEnd_1920497 := by exact prefixLift 1920497
  have htrace : WordTrace (prefixWord ++ tailWord_1920497) baseStart_1920497 baseEnd_1920497 := by
    simpa [prefixWord, tailWord_1920497, baseEnd_1920497] using wordTrace_append hprefix tailTrace_1920497
  have hstable : (prefixWord ++ tailWord_1920497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920497).length < 2 ^ (prefixWord ++ tailWord_1920497).sum := by decide
  have hdescent : baseEnd_1920497 < baseStart_1920497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920504 : List Nat := [2, 1, 2, 1, 1, 5, 1, 5, 1, 4]
def baseStart_1920504 : Nat := 118140960795 + 1920504 * 2 ^ 59
def prefixEnd_1920504 : Nat := 4983230072969 + 3 ^ 40 * 1920504 * 2
def baseEnd_1920504 : Nat := 328713883627486417655923

theorem tailTrace_1920504 : CollatzResearch.WordTrace tailWord_1920504 prefixEnd_1920504 328713883627486417655923 := by
  unfold tailWord_1920504
  simp only [CollatzResearch.WordTrace]
  refine ⟨35023267717174739407608283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46697690289566319210144377 35023267717174739407608283)
  ·
    refine ⟨52534901575762109111412425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35023267717174739407608283 52534901575762109111412425)
    ·
      refine ⟨39401176181821581833559319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52534901575762109111412425 39401176181821581833559319)
      ·
        refine ⟨59101764272732372750338979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39401176181821581833559319 59101764272732372750338979)
        ·
          refine ⟨88652646409098559125508469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59101764272732372750338979 88652646409098559125508469)
          ·
            refine ⟨8311185600852989918016419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88652646409098559125508469 8311185600852989918016419)
            ·
              refine ⟨12466778401279484877024629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8311185600852989918016419 12466778401279484877024629)
              ·
                refine ⟨1168760475119951707221059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12466778401279484877024629 1168760475119951707221059)
                ·
                  refine ⟨1753140712679927560831589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1168760475119951707221059 1753140712679927560831589)
                  ·
                    refine ⟨328713883627486417655923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1753140712679927560831589 328713883627486417655923)
                    ·
                      rfl

theorem cell23_1920504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 1, 4].length) (baseStart_1920504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920504 prefixEnd_1920504 := by exact prefixLift 1920504
  have htrace : WordTrace (prefixWord ++ tailWord_1920504) baseStart_1920504 baseEnd_1920504 := by
    simpa [prefixWord, tailWord_1920504, baseEnd_1920504] using wordTrace_append hprefix tailTrace_1920504
  have hstable : (prefixWord ++ tailWord_1920504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920504).length < 2 ^ (prefixWord ++ tailWord_1920504).sum := by decide
  have hdescent : baseEnd_1920504 < baseStart_1920504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920520 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_1920520 : Nat := 118140960795 + 1920520 * 2 ^ 59
def prefixEnd_1920520 : Nat := 4983230072969 + 3 ^ 40 * 1920520 * 2
def baseEnd_1920520 : Nat := 986149866572931190367695

theorem tailTrace_1920520 : CollatzResearch.WordTrace tailWord_1920520 prefixEnd_1920520 986149866572931190367695 := by
  unfold tailWord_1920520
  simp only [CollatzResearch.WordTrace]
  refine ⟨35023559501145756773899507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46698079334861009031866009 35023559501145756773899507)
  ·
    refine ⟨52535339251718635160849261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35023559501145756773899507 52535339251718635160849261)
    ·
      refine ⟨19700752219394488185318473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52535339251718635160849261 19700752219394488185318473)
      ·
        refine ⟨14775564164545866138988855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19700752219394488185318473 14775564164545866138988855)
        ·
          refine ⟨22163346246818799208483283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14775564164545866138988855 22163346246818799208483283)
          ·
            refine ⟨33245019370228198812724925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22163346246818799208483283 33245019370228198812724925)
            ·
              refine ⟨12466882263835574554771847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33245019370228198812724925 12466882263835574554771847)
              ·
                refine ⟨18700323395753361832157771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12466882263835574554771847 18700323395753361832157771)
                ·
                  refine ⟨28050485093630042748236657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18700323395753361832157771 28050485093630042748236657)
                  ·
                    refine ⟨21037863820222532061177493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28050485093630042748236657 21037863820222532061177493)
                    ·
                      refine ⟨986149866572931190367695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21037863820222532061177493 986149866572931190367695)
                      ·
                        rfl

theorem cell23_1920520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_1920520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920520 prefixEnd_1920520 := by exact prefixLift 1920520
  have htrace : WordTrace (prefixWord ++ tailWord_1920520) baseStart_1920520 baseEnd_1920520 := by
    simpa [prefixWord, tailWord_1920520, baseEnd_1920520] using wordTrace_append hprefix tailTrace_1920520
  have hstable : (prefixWord ++ tailWord_1920520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920520).length < 2 ^ (prefixWord ++ tailWord_1920520).sum := by decide
  have hdescent : baseEnd_1920520 < baseStart_1920520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920554 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_1920554 : Nat := 118140960795 + 1920554 * 2 ^ 59
def prefixEnd_1920554 : Nat := 4983230072969 + 3 ^ 40 * 1920554 * 2
def baseEnd_1920554 : Nat := 986167324915184057342539

theorem tailTrace_1920554 : CollatzResearch.WordTrace tailWord_1920554 prefixEnd_1920554 986167324915184057342539 := by
  unfold tailWord_1920554
  simp only [CollatzResearch.WordTrace]
  refine ⟨17512089771042084338634179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46698906056112224903024477 17512089771042084338634179)
  ·
    refine ⟨26268134656563126507951269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17512089771042084338634179 26268134656563126507951269)
    ·
      refine ⟨4925275248105586220240863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26268134656563126507951269 4925275248105586220240863)
      ·
        refine ⟨7387912872158379330361295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4925275248105586220240863 7387912872158379330361295)
        ·
          refine ⟨11081869308237568995541943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7387912872158379330361295 11081869308237568995541943)
          ·
            refine ⟨16622803962356353493312915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11081869308237568995541943 16622803962356353493312915)
            ·
              refine ⟨24934205943534530239969373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16622803962356353493312915 24934205943534530239969373)
              ·
                refine ⟨9350327228825448839988515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24934205943534530239969373 9350327228825448839988515)
                ·
                  refine ⟨14025490843238173259982773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9350327228825448839988515 14025490843238173259982773)
                  ·
                    refine ⟨1314889766553578743123385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14025490843238173259982773 1314889766553578743123385)
                    ·
                      refine ⟨986167324915184057342539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1314889766553578743123385 986167324915184057342539)
                      ·
                        rfl

theorem cell23_1920554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_1920554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920554 prefixEnd_1920554 := by exact prefixLift 1920554
  have htrace : WordTrace (prefixWord ++ tailWord_1920554) baseStart_1920554 baseEnd_1920554 := by
    simpa [prefixWord, tailWord_1920554, baseEnd_1920554] using wordTrace_append hprefix tailTrace_1920554
  have hstable : (prefixWord ++ tailWord_1920554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920554).length < 2 ^ (prefixWord ++ tailWord_1920554).sum := by decide
  have hdescent : baseEnd_1920554 < baseStart_1920554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920560 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 3, 6]
def baseStart_1920560 : Nat := 118140960795 + 1920560 * 2 ^ 59
def prefixEnd_1920560 : Nat := 4983230072969 + 3 ^ 40 * 1920560 * 2
def baseEnd_1920560 : Nat := 328723468599703677955837

theorem tailTrace_1920560 : CollatzResearch.WordTrace tailWord_1920560 prefixEnd_1920560 328723468599703677955837 := by
  unfold tailWord_1920560
  simp only [CollatzResearch.WordTrace]
  refine ⟨35024288961073300189627567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46699051948097733586170089 35024288961073300189627567)
  ·
    refine ⟨52536433441609950284441351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35024288961073300189627567 52536433441609950284441351)
    ·
      refine ⟨78804650162414925426662027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52536433441609950284441351 78804650162414925426662027)
      ·
        refine ⟨118206975243622388139993041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78804650162414925426662027 118206975243622388139993041)
        ·
          refine ⟨88655231432716791104994781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118206975243622388139993041 88655231432716791104994781)
          ·
            refine ⟨33245711787268796664373043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88655231432716791104994781 33245711787268796664373043)
            ·
              refine ⟨49868567680903194996559565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33245711787268796664373043 49868567680903194996559565)
              ·
                refine ⟨18700712880338698123709837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49868567680903194996559565 18700712880338698123709837)
                ·
                  refine ⟨7012767330127011796391189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18700712880338698123709837 7012767330127011796391189)
                  ·
                    refine ⟨328723468599703677955837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7012767330127011796391189 328723468599703677955837)
                    ·
                      rfl

theorem cell23_1920560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 3, 6].length) (baseStart_1920560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920560 prefixEnd_1920560 := by exact prefixLift 1920560
  have htrace : WordTrace (prefixWord ++ tailWord_1920560) baseStart_1920560 baseEnd_1920560 := by
    simpa [prefixWord, tailWord_1920560, baseEnd_1920560] using wordTrace_append hprefix tailTrace_1920560
  have hstable : (prefixWord ++ tailWord_1920560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920560).length < 2 ^ (prefixWord ++ tailWord_1920560).sum := by decide
  have hdescent : baseEnd_1920560 < baseStart_1920560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920587 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 3]
def baseStart_1920587 : Nat := 118140960795 + 1920587 * 2 ^ 59
def prefixEnd_1920587 : Nat := 4983230072969 + 3 ^ 40 * 1920587 * 2
def baseEnd_1920587 : Nat := 986184269776782428229887

theorem tailTrace_1920587 : CollatzResearch.WordTrace tailWord_1920587 prefixEnd_1920587 986184269776782428229887 := by
  unfold tailWord_1920587
  simp only [CollatzResearch.WordTrace]
  refine ⟨70049562693048783990488015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46699708462032522660325343 70049562693048783990488015)
  ·
    refine ⟨105074344039573175985732023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70049562693048783990488015 105074344039573175985732023)
    ·
      refine ⟨157611516059359763978598035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105074344039573175985732023 157611516059359763978598035)
      ·
        refine ⟨236417274089039645967897053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157611516059359763978598035 236417274089039645967897053)
        ·
          refine ⟨88656477783389867237961395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236417274089039645967897053 88656477783389867237961395)
          ·
            refine ⟨132984716675084800856942093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88656477783389867237961395 132984716675084800856942093)
            ·
              refine ⟨49869268753156800321353285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132984716675084800856942093 49869268753156800321353285)
              ·
                refine ⟨9350487891216900060253741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49869268753156800321353285 9350487891216900060253741)
                ·
                  refine ⟨3506432959206337522595153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9350487891216900060253741 3506432959206337522595153)
                  ·
                    refine ⟨2629824719404753141946365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3506432959206337522595153 2629824719404753141946365)
                    ·
                      refine ⟨986184269776782428229887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2629824719404753141946365 986184269776782428229887)
                      ·
                        rfl

theorem cell23_1920587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 2, 3].length) (baseStart_1920587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920587 prefixEnd_1920587 := by exact prefixLift 1920587
  have htrace : WordTrace (prefixWord ++ tailWord_1920587) baseStart_1920587 baseEnd_1920587 := by
    simpa [prefixWord, tailWord_1920587, baseEnd_1920587] using wordTrace_append hprefix tailTrace_1920587
  have hstable : (prefixWord ++ tailWord_1920587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920587).length < 2 ^ (prefixWord ++ tailWord_1920587).sum := by decide
  have hdescent : baseEnd_1920587 < baseStart_1920587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920597 : List Nat := [1, 3, 2, 2, 1, 1, 1, 5, 1, 2, 4]
def baseStart_1920597 : Nat := 118140960795 + 1920597 * 2 ^ 59
def prefixEnd_1920597 : Nat := 4983230072969 + 3 ^ 40 * 1920597 * 2
def baseEnd_1920597 : Nat := 986189404583327389104841

theorem tailTrace_1920597 : CollatzResearch.WordTrace tailWord_1920597 prefixEnd_1920597 986189404583327389104841 := by
  unfold tailWord_1920597
  simp only [CollatzResearch.WordTrace]
  refine ⟨70049927423012555698352045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46699951615341703798901363 70049927423012555698352045)
  ·
    refine ⟨26268722783629708386882017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70049927423012555698352045 26268722783629708386882017)
    ·
      refine ⟨19701542087722281290161513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26268722783629708386882017 19701542087722281290161513)
      ·
        refine ⟨14776156565791710967621135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19701542087722281290161513 14776156565791710967621135)
        ·
          refine ⟨22164234848687566451431703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14776156565791710967621135 22164234848687566451431703)
          ·
            refine ⟨33246352273031349677147555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22164234848687566451431703 33246352273031349677147555)
            ·
              refine ⟨49869528409547024515721333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33246352273031349677147555 49869528409547024515721333)
              ·
                refine ⟨4675268288395033548348875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49869528409547024515721333 4675268288395033548348875)
                ·
                  refine ⟨7012902432592550322523313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4675268288395033548348875 7012902432592550322523313)
                  ·
                    refine ⟨5259676824444412741892485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7012902432592550322523313 5259676824444412741892485)
                    ·
                      refine ⟨986189404583327389104841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5259676824444412741892485 986189404583327389104841)
                      ·
                        rfl

theorem cell23_1920597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_1920597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920597 prefixEnd_1920597 := by exact prefixLift 1920597
  have htrace : WordTrace (prefixWord ++ tailWord_1920597) baseStart_1920597 baseEnd_1920597 := by
    simpa [prefixWord, tailWord_1920597, baseEnd_1920597] using wordTrace_append hprefix tailTrace_1920597
  have hstable : (prefixWord ++ tailWord_1920597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920597).length < 2 ^ (prefixWord ++ tailWord_1920597).sum := by decide
  have hdescent : baseEnd_1920597 < baseStart_1920597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920598 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_1920598 : Nat := 118140960795 + 1920598 * 2 ^ 59
def prefixEnd_1920598 : Nat := 4983230072969 + 3 ^ 40 * 1920598 * 2
def baseEnd_1920598 : Nat := 328729972687993961730779

theorem tailTrace_1920598 : CollatzResearch.WordTrace tailWord_1920598 prefixEnd_1920598 328729972687993961730779 := by
  unfold tailWord_1920598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4378122743500558304321153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 46699975930672621912758965 4378122743500558304321153)
  ·
    refine ⟨3283592057625418728240865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4378122743500558304321153 3283592057625418728240865)
    ·
      refine ⟨2462694043219064046180649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3283592057625418728240865 2462694043219064046180649)
      ·
        refine ⟨1847020532414298034635487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2462694043219064046180649 1847020532414298034635487)
        ·
          refine ⟨2770530798621447051953231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1847020532414298034635487 2770530798621447051953231)
          ·
            refine ⟨4155796197932170577929847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770530798621447051953231 4155796197932170577929847)
            ·
              refine ⟨6233694296898255866894771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4155796197932170577929847 6233694296898255866894771)
              ·
                refine ⟨9350541445347383800342157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6233694296898255866894771 9350541445347383800342157)
                ·
                  refine ⟨3506453042005268925128309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9350541445347383800342157 3506453042005268925128309)
                  ·
                    refine ⟨328729972687993961730779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3506453042005268925128309 328729972687993961730779)
                    ·
                      rfl

theorem cell23_1920598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_1920598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920598 prefixEnd_1920598 := by exact prefixLift 1920598
  have htrace : WordTrace (prefixWord ++ tailWord_1920598) baseStart_1920598 baseEnd_1920598 := by
    simpa [prefixWord, tailWord_1920598, baseEnd_1920598] using wordTrace_append hprefix tailTrace_1920598
  have hstable : (prefixWord ++ tailWord_1920598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920598).length < 2 ^ (prefixWord ++ tailWord_1920598).sum := by decide
  have hdescent : baseEnd_1920598 < baseStart_1920598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920605 : List Nat := [1, 4, 4, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_1920605 : Nat := 118140960795 + 1920605 * 2 ^ 59
def prefixEnd_1920605 : Nat := 4983230072969 + 3 ^ 40 * 1920605 * 2
def baseEnd_1920605 : Nat := 986193512428563357804805

theorem tailTrace_1920605 : CollatzResearch.WordTrace tailWord_1920605 prefixEnd_1920605 986193512428563357804805 := by
  unfold tailWord_1920605
  simp only [CollatzResearch.WordTrace]
  refine ⟨70050219206983573064643269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46700146137989048709762179 70050219206983573064643269)
  ·
    refine ⟨13134416101309419949620613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70050219206983573064643269 13134416101309419949620613)
    ·
      refine ⟨2462703018995516240553865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13134416101309419949620613 2462703018995516240553865)
      ·
        refine ⟨1847027264246637180415399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2462703018995516240553865 1847027264246637180415399)
        ·
          refine ⟨2770540896369955770623099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1847027264246637180415399 2770540896369955770623099)
          ·
            refine ⟨4155811344554933655934649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2770540896369955770623099 4155811344554933655934649)
            ·
              refine ⟨3116858508416200241950987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4155811344554933655934649 3116858508416200241950987)
              ·
                refine ⟨4675287762624300362926481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3116858508416200241950987 4675287762624300362926481)
                ·
                  refine ⟨3506465821968225272194861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4675287762624300362926481 3506465821968225272194861)
                  ·
                    refine ⟨1314924683238084477073073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3506465821968225272194861 1314924683238084477073073)
                    ·
                      refine ⟨986193512428563357804805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1314924683238084477073073 986193512428563357804805)
                      ·
                        rfl

theorem cell23_1920605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_1920605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920605 prefixEnd_1920605 := by exact prefixLift 1920605
  have htrace : WordTrace (prefixWord ++ tailWord_1920605) baseStart_1920605 baseEnd_1920605 := by
    simpa [prefixWord, tailWord_1920605, baseEnd_1920605] using wordTrace_append hprefix tailTrace_1920605
  have hstable : (prefixWord ++ tailWord_1920605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920605).length < 2 ^ (prefixWord ++ tailWord_1920605).sum := by decide
  have hdescent : baseEnd_1920605 < baseStart_1920605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920617 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 3, 3, 3]
def baseStart_1920617 : Nat := 118140960795 + 1920617 * 2 ^ 59
def prefixEnd_1920617 : Nat := 4983230072969 + 3 ^ 40 * 1920617 * 2
def baseEnd_1920617 : Nat := 986199674196417310854749

theorem tailTrace_1920617 : CollatzResearch.WordTrace tailWord_1920617 prefixEnd_1920617 986199674196417310854749 := by
  unfold tailWord_1920617
  simp only [CollatzResearch.WordTrace]
  refine ⟨70050656882940099114080105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46700437921960066076053403 70050656882940099114080105)
  ·
    refine ⟨52537992662205074335560079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70050656882940099114080105 52537992662205074335560079)
    ·
      refine ⟨78806988993307611503340119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52537992662205074335560079 78806988993307611503340119)
      ·
        refine ⟨118210483489961417255010179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78806988993307611503340119 118210483489961417255010179)
        ·
          refine ⟨177315725234942125882515269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118210483489961417255010179 177315725234942125882515269)
          ·
            refine ⟨33246698481551648602971613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177315725234942125882515269 33246698481551648602971613)
            ·
              refine ⟨12467511930581868226114355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33246698481551648602971613 12467511930581868226114355)
              ·
                refine ⟨18701267895872802339171533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12467511930581868226114355 18701267895872802339171533)
                ·
                  refine ⟨7012975460952300877189325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18701267895872802339171533 7012975460952300877189325)
                  ·
                    refine ⟨2629865797857112828945997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7012975460952300877189325 2629865797857112828945997)
                    ·
                      refine ⟨986199674196417310854749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2629865797857112828945997 986199674196417310854749)
                      ·
                        rfl

theorem cell23_1920617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 3, 3].length) (baseStart_1920617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920617 prefixEnd_1920617 := by exact prefixLift 1920617
  have htrace : WordTrace (prefixWord ++ tailWord_1920617) baseStart_1920617 baseEnd_1920617 := by
    simpa [prefixWord, tailWord_1920617, baseEnd_1920617] using wordTrace_append hprefix tailTrace_1920617
  have hstable : (prefixWord ++ tailWord_1920617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920617).length < 2 ^ (prefixWord ++ tailWord_1920617).sum := by decide
  have hdescent : baseEnd_1920617 < baseStart_1920617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920621 : List Nat := [1, 5, 1, 1, 4, 2, 1, 1, 1, 1, 5]
def baseStart_1920621 : Nat := 118140960795 + 1920621 * 2 ^ 59
def prefixEnd_1920621 : Nat := 4983230072969 + 3 ^ 40 * 1920621 * 2
def baseEnd_1920621 : Nat := 986201728119035295204731

theorem tailTrace_1920621 : CollatzResearch.WordTrace tailWord_1920621 prefixEnd_1920621 986201728119035295204731 := by
  unfold tailWord_1920621
  simp only [CollatzResearch.WordTrace]
  refine ⟨70050802774925607797225717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46700535183283738531483811 70050802774925607797225717)
  ·
    refine ⟨6567262760149275730989911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70050802774925607797225717 6567262760149275730989911)
    ·
      refine ⟨9850894140223913596484867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6567262760149275730989911 9850894140223913596484867)
      ·
        refine ⟨14776341210335870394727301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9850894140223913596484867 14776341210335870394727301)
        ·
          refine ⟨2770563976937975699011369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14776341210335870394727301 2770563976937975699011369)
          ·
            refine ⟨2077922982703481774258527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2770563976937975699011369 2077922982703481774258527)
            ·
              refine ⟨3116884474055222661387791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2077922982703481774258527 3116884474055222661387791)
              ·
                refine ⟨4675326711082833992081687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3116884474055222661387791 4675326711082833992081687)
                ·
                  refine ⟨7012990066624250988122531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4675326711082833992081687 7012990066624250988122531)
                  ·
                    refine ⟨10519485099936376482183797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7012990066624250988122531 10519485099936376482183797)
                    ·
                      refine ⟨986201728119035295204731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10519485099936376482183797 986201728119035295204731)
                      ·
                        rfl

theorem cell23_1920621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_1920621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920621 prefixEnd_1920621 := by exact prefixLift 1920621
  have htrace : WordTrace (prefixWord ++ tailWord_1920621) baseStart_1920621 baseEnd_1920621 := by
    simpa [prefixWord, tailWord_1920621, baseEnd_1920621] using wordTrace_append hprefix tailTrace_1920621
  have hstable : (prefixWord ++ tailWord_1920621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920621).length < 2 ^ (prefixWord ++ tailWord_1920621).sum := by decide
  have hdescent : baseEnd_1920621 < baseStart_1920621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920637 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 2, 7]
def baseStart_1920637 : Nat := 118140960795 + 1920637 * 2 ^ 59
def prefixEnd_1920637 : Nat := 4983230072969 + 3 ^ 40 * 1920637 * 2
def baseEnd_1920637 : Nat := 328736647936502410868219

theorem tailTrace_1920637 : CollatzResearch.WordTrace tailWord_1920637 prefixEnd_1920637 328736647936502410868219 := by
  unfold tailWord_1920637
  simp only [CollatzResearch.WordTrace]
  refine ⟨70051386342867642529808165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46700924228578428353205443 70051386342867642529808165)
  ·
    refine ⟨13134634939287682974339031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70051386342867642529808165 13134634939287682974339031)
    ·
      refine ⟨19701952408931524461508547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13134634939287682974339031 19701952408931524461508547)
      ·
        refine ⟨29552928613397286692262821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19701952408931524461508547 29552928613397286692262821)
        ·
          refine ⟨5541174115011991254799279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29552928613397286692262821 5541174115011991254799279)
          ·
            refine ⟨8311761172517986882198919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5541174115011991254799279 8311761172517986882198919)
            ·
              refine ⟨12467641758776980323298379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8311761172517986882198919 12467641758776980323298379)
              ·
                refine ⟨18701462638165470484947569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12467641758776980323298379 18701462638165470484947569)
                ·
                  refine ⟨14026096978624102863710677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18701462638165470484947569 14026096978624102863710677)
                  ·
                    refine ⟨328736647936502410868219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14026096978624102863710677 328736647936502410868219)
                    ·
                      rfl

theorem cell23_1920637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_1920637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920637 prefixEnd_1920637 := by exact prefixLift 1920637
  have htrace : WordTrace (prefixWord ++ tailWord_1920637) baseStart_1920637 baseEnd_1920637 := by
    simpa [prefixWord, tailWord_1920637, baseEnd_1920637] using wordTrace_append hprefix tailTrace_1920637
  have hstable : (prefixWord ++ tailWord_1920637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920637).length < 2 ^ (prefixWord ++ tailWord_1920637).sum := by decide
  have hdescent : baseEnd_1920637 < baseStart_1920637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920677 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 2, 1, 5]
def baseStart_1920677 : Nat := 118140960795 + 1920677 * 2 ^ 59
def prefixEnd_1920677 : Nat := 4983230072969 + 3 ^ 40 * 1920677 * 2
def baseEnd_1920677 : Nat := 986230483035687076104473

theorem tailTrace_1920677 : CollatzResearch.WordTrace tailWord_1920677 prefixEnd_1920677 986230483035687076104473 := by
  unfold tailWord_1920677
  simp only [CollatzResearch.WordTrace]
  refine ⟨70052845262722729361264285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46701896841815152907509523 70052845262722729361264285)
  ·
    refine ⟨26269816973521023510474107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70052845262722729361264285 26269816973521023510474107)
    ·
      refine ⟨39404725460281535265711161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26269816973521023510474107 39404725460281535265711161)
      ·
        refine ⟨29553544095211151449283371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39404725460281535265711161 29553544095211151449283371)
        ·
          refine ⟨44330316142816727173925057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29553544095211151449283371 44330316142816727173925057)
          ·
            refine ⟨33247737107112545380443793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44330316142816727173925057 33247737107112545380443793)
            ·
              refine ⟨24935802830334409035332845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33247737107112545380443793 24935802830334409035332845)
              ·
                refine ⟨9350926061375403388249817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24935802830334409035332845 9350926061375403388249817)
                ·
                  refine ⟨7013194546031552541187363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9350926061375403388249817 7013194546031552541187363)
                  ·
                    refine ⟨10519791819047328811781045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7013194546031552541187363 10519791819047328811781045)
                    ·
                      refine ⟨986230483035687076104473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10519791819047328811781045 986230483035687076104473)
                      ·
                        rfl

theorem cell23_1920677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_1920677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920677 prefixEnd_1920677 := by exact prefixLift 1920677
  have htrace : WordTrace (prefixWord ++ tailWord_1920677) baseStart_1920677 baseEnd_1920677 := by
    simpa [prefixWord, tailWord_1920677, baseEnd_1920677] using wordTrace_append hprefix tailTrace_1920677
  have hstable : (prefixWord ++ tailWord_1920677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920677).length < 2 ^ (prefixWord ++ tailWord_1920677).sum := by decide
  have hdescent : baseEnd_1920677 < baseStart_1920677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920687 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 4]
def baseStart_1920687 : Nat := 118140960795 + 1920687 * 2 ^ 59
def prefixEnd_1920687 : Nat := 4983230072969 + 3 ^ 40 * 1920687 * 2
def baseEnd_1920687 : Nat := 986235617842232036979427

theorem tailTrace_1920687 : CollatzResearch.WordTrace tailWord_1920687 prefixEnd_1920687 986235617842232036979427 := by
  unfold tailWord_1920687
  simp only [CollatzResearch.WordTrace]
  refine ⟨70053209992686501069128315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46702139995124334046085543 70053209992686501069128315)
  ·
    refine ⟨105079814989029751603692473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70053209992686501069128315 105079814989029751603692473)
    ·
      refine ⟨78809861241772313702769355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105079814989029751603692473 78809861241772313702769355)
      ·
        refine ⟨118214791862658470554154033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78809861241772313702769355 118214791862658470554154033)
        ·
          refine ⟨88661093896993852915615525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118214791862658470554154033 88661093896993852915615525)
          ·
            refine ⟨16623955105686347421677911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88661093896993852915615525 16623955105686347421677911)
            ·
              refine ⟨24935932658529521132516867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16623955105686347421677911 24935932658529521132516867)
              ·
                refine ⟨37403898987794281698775301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24935932658529521132516867 37403898987794281698775301)
                ·
                  refine ⟨7013231060211427818520369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37403898987794281698775301 7013231060211427818520369)
                  ·
                    refine ⟨5259923295158570863890277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7013231060211427818520369 5259923295158570863890277)
                    ·
                      refine ⟨986235617842232036979427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5259923295158570863890277 986235617842232036979427)
                      ·
                        rfl

theorem cell23_1920687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 4].length) (baseStart_1920687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920687 prefixEnd_1920687 := by exact prefixLift 1920687
  have htrace : WordTrace (prefixWord ++ tailWord_1920687) baseStart_1920687 baseEnd_1920687 := by
    simpa [prefixWord, tailWord_1920687, baseEnd_1920687] using wordTrace_append hprefix tailTrace_1920687
  have hstable : (prefixWord ++ tailWord_1920687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920687).length < 2 ^ (prefixWord ++ tailWord_1920687).sum := by decide
  have hdescent : baseEnd_1920687 < baseStart_1920687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920691 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 4, 2, 2]
def baseStart_1920691 : Nat := 118140960795 + 1920691 * 2 ^ 59
def prefixEnd_1920691 : Nat := 4983230072969 + 3 ^ 40 * 1920691 * 2
def baseEnd_1920691 : Nat := 986237671764850021329409

theorem tailTrace_1920691 : CollatzResearch.WordTrace tailWord_1920691 prefixEnd_1920691 986237671764850021329409 := by
  unfold tailWord_1920691
  simp only [CollatzResearch.WordTrace]
  refine ⟨70053355884672009752273927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46702237256448006501515951 70053355884672009752273927)
  ·
    refine ⟨105080033827008014628410891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70053355884672009752273927 105080033827008014628410891)
    ·
      refine ⟨157620050740512021942616337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105080033827008014628410891 157620050740512021942616337)
      ·
        refine ⟨118215038055384016456962253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157620050740512021942616337 118215038055384016456962253)
        ·
          refine ⟨44330639270769006171360845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118215038055384016456962253 44330639270769006171360845)
          ·
            refine ⟨16623989726538377314260317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44330639270769006171360845 16623989726538377314260317)
            ·
              refine ⟨6233996147451891492847619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16623989726538377314260317 6233996147451891492847619)
              ·
                refine ⟨9350994221177837239271429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6233996147451891492847619 9350994221177837239271429)
                ·
                  refine ⟨1753311416470844482363393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9350994221177837239271429 1753311416470844482363393)
                  ·
                    refine ⟨1314983562353133361772545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1753311416470844482363393 1314983562353133361772545)
                    ·
                      refine ⟨986237671764850021329409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1314983562353133361772545 986237671764850021329409)
                      ·
                        rfl

theorem cell23_1920691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 2, 2].length) (baseStart_1920691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920691 prefixEnd_1920691 := by exact prefixLift 1920691
  have htrace : WordTrace (prefixWord ++ tailWord_1920691) baseStart_1920691 baseEnd_1920691 := by
    simpa [prefixWord, tailWord_1920691, baseEnd_1920691] using wordTrace_append hprefix tailTrace_1920691
  have hstable : (prefixWord ++ tailWord_1920691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920691).length < 2 ^ (prefixWord ++ tailWord_1920691).sum := by decide
  have hdescent : baseEnd_1920691 < baseStart_1920691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920697 : List Nat := [1, 2, 1, 4, 1, 1, 3, 3, 7]
def baseStart_1920697 : Nat := 118140960795 + 1920697 * 2 ^ 59
def prefixEnd_1920697 : Nat := 4983230072969 + 3 ^ 40 * 1920697 * 2
def baseEnd_1920697 : Nat := 109582305849864110872709

theorem tailTrace_1920697 : CollatzResearch.WordTrace tailWord_1920697 prefixEnd_1920697 109582305849864110872709 := by
  unfold tailWord_1920697
  simp only [CollatzResearch.WordTrace]
  refine ⟨70053574722650272776992345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46702383148433515184661563 70053574722650272776992345)
  ·
    refine ⟨52540181041987704582744259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70053574722650272776992345 52540181041987704582744259)
    ·
      refine ⟨78810271562981556874116389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52540181041987704582744259 78810271562981556874116389)
      ·
        refine ⟨14776925918059041913896823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78810271562981556874116389 14776925918059041913896823)
        ·
          refine ⟨22165388877088562870845235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14776925918059041913896823 22165388877088562870845235)
          ·
            refine ⟨33248083315632844306267853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22165388877088562870845235 33248083315632844306267853)
            ·
              refine ⟨12468031243362316614850445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33248083315632844306267853 12468031243362316614850445)
              ·
                refine ⟨4675511716260868730568917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12468031243362316614850445 4675511716260868730568917)
                ·
                  refine ⟨109582305849864110872709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4675511716260868730568917 109582305849864110872709)
                  ·
                    rfl

theorem cell23_1920697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 7].length) (baseStart_1920697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920697 prefixEnd_1920697 := by exact prefixLift 1920697
  have htrace : WordTrace (prefixWord ++ tailWord_1920697) baseStart_1920697 baseEnd_1920697 := by
    simpa [prefixWord, tailWord_1920697, baseEnd_1920697] using wordTrace_append hprefix tailTrace_1920697
  have hstable : (prefixWord ++ tailWord_1920697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920697).length < 2 ^ (prefixWord ++ tailWord_1920697).sum := by decide
  have hdescent : baseEnd_1920697 < baseStart_1920697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920727 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 1, 7]
def baseStart_1920727 : Nat := 118140960795 + 1920727 * 2 ^ 59
def prefixEnd_1920727 : Nat := 4983230072969 + 3 ^ 40 * 1920727 * 2
def baseEnd_1920727 : Nat := 328752052356137293493081

theorem tailTrace_1920727 : CollatzResearch.WordTrace tailWord_1920727 prefixEnd_1920727 328752052356137293493081 := by
  unfold tailWord_1920727
  simp only [CollatzResearch.WordTrace]
  refine ⟨70054668912541587900584435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46703112608361058600389623 70054668912541587900584435)
  ·
    refine ⟨105082003368812381850876653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70054668912541587900584435 105082003368812381850876653)
    ·
      refine ⟨39405751263304643194078745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105082003368812381850876653 39405751263304643194078745)
      ·
        refine ⟨29554313447478482395559059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39405751263304643194078745 29554313447478482395559059)
        ·
          refine ⟨44331470171217723593338589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29554313447478482395559059 44331470171217723593338589)
          ·
            refine ⟨16624301314206646347501971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44331470171217723593338589 16624301314206646347501971)
            ·
              refine ⟨24936451971309969521252957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16624301314206646347501971 24936451971309969521252957)
              ·
                refine ⟨9351169489241238570469859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24936451971309969521252957 9351169489241238570469859)
                ·
                  refine ⟨14026754233861857855704789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9351169489241238570469859 14026754233861857855704789)
                  ·
                    refine ⟨328752052356137293493081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14026754233861857855704789 328752052356137293493081)
                    ·
                      rfl

theorem cell23_1920727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_1920727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920727 prefixEnd_1920727 := by exact prefixLift 1920727
  have htrace : WordTrace (prefixWord ++ tailWord_1920727) baseStart_1920727 baseEnd_1920727 := by
    simpa [prefixWord, tailWord_1920727, baseEnd_1920727] using wordTrace_append hprefix tailTrace_1920727
  have hstable : (prefixWord ++ tailWord_1920727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920727).length < 2 ^ (prefixWord ++ tailWord_1920727).sum := by decide
  have hdescent : baseEnd_1920727 < baseStart_1920727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920744 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 4, 5]
def baseStart_1920744 : Nat := 118140960795 + 1920744 * 2 ^ 59
def prefixEnd_1920744 : Nat := 4983230072969 + 3 ^ 40 * 1920744 * 2
def baseEnd_1920744 : Nat := 328754962079846104655555

theorem tailTrace_1920744 : CollatzResearch.WordTrace tailWord_1920744 prefixEnd_1920744 328754962079846104655555 := by
  unfold tailWord_1920744
  simp only [CollatzResearch.WordTrace]
  refine ⟨35027644476739999901976643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46703525968986666535968857 35027644476739999901976643)
  ·
    refine ⟨52541466715109999852964965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35027644476739999901976643 52541466715109999852964965)
    ·
      refine ⟨9851525009083124972430931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52541466715109999852964965 9851525009083124972430931)
      ·
        refine ⟨14777287513624687458646397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9851525009083124972430931 14777287513624687458646397)
        ·
          refine ⟨5541482817609257796992399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14777287513624687458646397 5541482817609257796992399)
          ·
            refine ⟨8312224226413886695488599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5541482817609257796992399 8312224226413886695488599)
            ·
              refine ⟨12468336339620830043232899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8312224226413886695488599 12468336339620830043232899)
              ·
                refine ⟨18702504509431245064849349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12468336339620830043232899 18702504509431245064849349)
                ·
                  refine ⟨3506719595518358449659253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18702504509431245064849349 3506719595518358449659253)
                  ·
                    refine ⟨328754962079846104655555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3506719595518358449659253 328754962079846104655555)
                    ·
                      rfl

theorem cell23_1920744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_1920744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920744 prefixEnd_1920744 := by exact prefixLift 1920744
  have htrace : WordTrace (prefixWord ++ tailWord_1920744) baseStart_1920744 baseEnd_1920744 := by
    simpa [prefixWord, tailWord_1920744, baseEnd_1920744] using wordTrace_append hprefix tailTrace_1920744
  have hstable : (prefixWord ++ tailWord_1920744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920744).length < 2 ^ (prefixWord ++ tailWord_1920744).sum := by decide
  have hdescent : baseEnd_1920744 < baseStart_1920744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920754 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1920754 : Nat := 118140960795 + 1920754 * 2 ^ 59
def prefixEnd_1920754 : Nat := 4983230072969 + 3 ^ 40 * 1920754 * 2
def baseEnd_1920754 : Nat := 986270021046083274841619

theorem tailTrace_1920754 : CollatzResearch.WordTrace tailWord_1920754 prefixEnd_1920754 986270021046083274841619 := by
  unfold tailWord_1920754
  simp only [CollatzResearch.WordTrace]
  refine ⟨17513913420860942877954329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46703769122295847674544877 17513913420860942877954329)
  ·
    refine ⟨13135435065645707158465747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17513913420860942877954329 13135435065645707158465747)
    ·
      refine ⟨19703152598468560737698621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13135435065645707158465747 19703152598468560737698621)
      ·
        refine ⟨7388682224425710276636983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19703152598468560737698621 7388682224425710276636983)
        ·
          refine ⟨11083023336638565414955475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7388682224425710276636983 11083023336638565414955475)
          ·
            refine ⟨16624535004957848122433213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11083023336638565414955475 16624535004957848122433213)
            ·
              refine ⟨6234200626859193045912455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16624535004957848122433213 6234200626859193045912455)
              ·
                refine ⟨9351300940288789568868683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6234200626859193045912455 9351300940288789568868683)
                ·
                  refine ⟨14026951410433184353303025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9351300940288789568868683 14026951410433184353303025)
                  ·
                    refine ⟨10520213557824888264977269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14026951410433184353303025 10520213557824888264977269)
                    ·
                      refine ⟨986270021046083274841619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10520213557824888264977269 986270021046083274841619)
                      ·
                        rfl

theorem cell23_1920754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1920754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920754 prefixEnd_1920754 := by exact prefixLift 1920754
  have htrace : WordTrace (prefixWord ++ tailWord_1920754) baseStart_1920754 baseEnd_1920754 := by
    simpa [prefixWord, tailWord_1920754, baseEnd_1920754] using wordTrace_append hprefix tailTrace_1920754
  have hstable : (prefixWord ++ tailWord_1920754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920754).length < 2 ^ (prefixWord ++ tailWord_1920754).sum := by decide
  have hdescent : baseEnd_1920754 < baseStart_1920754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920764 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 4, 1, 4]
def baseStart_1920764 : Nat := 118140960795 + 1920764 * 2 ^ 59
def prefixEnd_1920764 : Nat := 4983230072969 + 3 ^ 40 * 1920764 * 2
def baseEnd_1920764 : Nat := 986275155852628235716573

theorem tailTrace_1920764 : CollatzResearch.WordTrace tailWord_1920764 prefixEnd_1920764 986275155852628235716573 := by
  unfold tailWord_1920764
  simp only [CollatzResearch.WordTrace]
  refine ⟨35028009206703771609840673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46704012275605028813120897 35028009206703771609840673)
  ·
    refine ⟨26271006905027828707380505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35028009206703771609840673 26271006905027828707380505)
    ·
      refine ⟨19703255178770871530535379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26271006905027828707380505 19703255178770871530535379)
      ·
        refine ⟨29554882768156307295803069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19703255178770871530535379 29554882768156307295803069)
        ·
          refine ⟨11083081038058615235926151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29554882768156307295803069 11083081038058615235926151)
          ·
            refine ⟨16624621557087922853889227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11083081038058615235926151 16624621557087922853889227)
            ·
              refine ⟨24936932335631884280833841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16624621557087922853889227 24936932335631884280833841)
              ·
                refine ⟨18702699251723913210625381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24936932335631884280833841 18702699251723913210625381)
                ·
                  refine ⟨3506756109698233726992259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18702699251723913210625381 3506756109698233726992259)
                  ·
                    refine ⟨5260134164547350590488389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3506756109698233726992259 5260134164547350590488389)
                    ·
                      refine ⟨986275155852628235716573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5260134164547350590488389 986275155852628235716573)
                      ·
                        rfl

theorem cell23_1920764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_1920764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920764 prefixEnd_1920764 := by exact prefixLift 1920764
  have htrace : WordTrace (prefixWord ++ tailWord_1920764) baseStart_1920764 baseEnd_1920764 := by
    simpa [prefixWord, tailWord_1920764, baseEnd_1920764] using wordTrace_append hprefix tailTrace_1920764
  have hstable : (prefixWord ++ tailWord_1920764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920764).length < 2 ^ (prefixWord ++ tailWord_1920764).sum := by decide
  have hdescent : baseEnd_1920764 < baseStart_1920764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920777 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 1, 3, 6]
def baseStart_1920777 : Nat := 118140960795 + 1920777 * 2 ^ 59
def prefixEnd_1920777 : Nat := 4983230072969 + 3 ^ 40 * 1920777 * 2
def baseEnd_1920777 : Nat := 986281831101136684854013

theorem tailTrace_1920777 : CollatzResearch.WordTrace tailWord_1920777 prefixEnd_1920777 986281831101136684854013 := by
  unfold tailWord_1920777
  simp only [CollatzResearch.WordTrace]
  refine ⟨70056492562360446439904585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46704328374906964293269723 70056492562360446439904585)
  ·
    refine ⟨52542369421770334829928439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70056492562360446439904585 52542369421770334829928439)
    ·
      refine ⟨78813554132655502244892659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52542369421770334829928439 78813554132655502244892659)
      ·
        refine ⟨118220331198983253367338989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78813554132655502244892659 118220331198983253367338989)
        ·
          refine ⟨44332624199618720012752121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118220331198983253367338989 44332624199618720012752121)
          ·
            refine ⟨33249468149714040009564091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44332624199618720012752121 33249468149714040009564091)
            ·
              refine ⟨49874202224571060014346137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33249468149714040009564091 49874202224571060014346137)
              ·
                refine ⟨37405651668428295010759603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49874202224571060014346137 37405651668428295010759603)
                ·
                  refine ⟨56108477502642442516139405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37405651668428295010759603 56108477502642442516139405)
                  ·
                    refine ⟨21040679063490915943552277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56108477502642442516139405 21040679063490915943552277)
                    ·
                      refine ⟨986281831101136684854013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21040679063490915943552277 986281831101136684854013)
                      ·
                        rfl

theorem cell23_1920777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_1920777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920777 prefixEnd_1920777 := by exact prefixLift 1920777
  have htrace : WordTrace (prefixWord ++ tailWord_1920777) baseStart_1920777 baseEnd_1920777 := by
    simpa [prefixWord, tailWord_1920777, baseEnd_1920777] using wordTrace_append hprefix tailTrace_1920777
  have hstable : (prefixWord ++ tailWord_1920777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920777).length < 2 ^ (prefixWord ++ tailWord_1920777).sum := by decide
  have hdescent : baseEnd_1920777 < baseStart_1920777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920787 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 8]
def baseStart_1920787 : Nat := 118140960795 + 1920787 * 2 ^ 59
def prefixEnd_1920787 : Nat := 4983230072969 + 3 ^ 40 * 1920787 * 2
def baseEnd_1920787 : Nat := 109587440656409071747663

theorem tailTrace_1920787 : CollatzResearch.WordTrace tailWord_1920787 prefixEnd_1920787 109587440656409071747663 := by
  unfold tailWord_1920787
  simp only [CollatzResearch.WordTrace]
  refine ⟨70056857292324218147768615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46704571528216145431845743 70056857292324218147768615)
  ·
    refine ⟨105085285938486327221652923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70056857292324218147768615 105085285938486327221652923)
    ·
      refine ⟨157627928907729490832479385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105085285938486327221652923 157627928907729490832479385)
      ·
        refine ⟨118220946680797118124359539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157627928907729490832479385 118220946680797118124359539)
        ·
          refine ⟨177331420021195677186539309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118220946680797118124359539 177331420021195677186539309)
          ·
            refine ⟨66499282507948378944952241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177331420021195677186539309 66499282507948378944952241)
            ·
              refine ⟨49874461880961284208714181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66499282507948378944952241 49874461880961284208714181)
              ·
                refine ⟨9351461602680240789133909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49874461880961284208714181 9351461602680240789133909)
                ·
                  refine ⟨109587440656409071747663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9351461602680240789133909 109587440656409071747663)
                  ·
                    rfl

theorem cell23_1920787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 8].length) (baseStart_1920787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920787 prefixEnd_1920787 := by exact prefixLift 1920787
  have htrace : WordTrace (prefixWord ++ tailWord_1920787) baseStart_1920787 baseEnd_1920787 := by
    simpa [prefixWord, tailWord_1920787, baseEnd_1920787] using wordTrace_append hprefix tailTrace_1920787
  have hstable : (prefixWord ++ tailWord_1920787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920787).length < 2 ^ (prefixWord ++ tailWord_1920787).sum := by decide
  have hdescent : baseEnd_1920787 < baseStart_1920787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920801 : List Nat := [1, 2, 3, 2, 1, 3, 2, 2, 2, 2, 3]
def baseStart_1920801 : Nat := 118140960795 + 1920801 * 2 ^ 59
def prefixEnd_1920801 : Nat := 4983230072969 + 3 ^ 40 * 1920801 * 2
def baseEnd_1920801 : Nat := 986294154636844590953903

theorem tailTrace_1920801 : CollatzResearch.WordTrace tailWord_1920801 prefixEnd_1920801 986294154636844590953903 := by
  unfold tailWord_1920801
  simp only [CollatzResearch.WordTrace]
  refine ⟨70057367914273498538778257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46704911942848999025852171 70057367914273498538778257)
  ·
    refine ⟨52543025935705123904083693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70057367914273498538778257 52543025935705123904083693)
    ·
      refine ⟨19703634725889421464031385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52543025935705123904083693 19703634725889421464031385)
      ·
        refine ⟨14777726044417066098023539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19703634725889421464031385 14777726044417066098023539)
        ·
          refine ⟨22166589066625599147035309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14777726044417066098023539 22166589066625599147035309)
          ·
            refine ⟨8312470899984599680138241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22166589066625599147035309 8312470899984599680138241)
            ·
              refine ⟨6234353174988449760103681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8312470899984599680138241 6234353174988449760103681)
              ·
                refine ⟨4675764881241337320077761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6234353174988449760103681 4675764881241337320077761)
                ·
                  refine ⟨3506823660931002990058321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4675764881241337320077761 3506823660931002990058321)
                  ·
                    refine ⟨2630117745698252242543741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3506823660931002990058321 2630117745698252242543741)
                    ·
                      refine ⟨986294154636844590953903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2630117745698252242543741 986294154636844590953903)
                      ·
                        rfl

theorem cell23_1920801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_1920801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920801 prefixEnd_1920801 := by exact prefixLift 1920801
  have htrace : WordTrace (prefixWord ++ tailWord_1920801) baseStart_1920801 baseEnd_1920801 := by
    simpa [prefixWord, tailWord_1920801, baseEnd_1920801] using wordTrace_append hprefix tailTrace_1920801
  have hstable : (prefixWord ++ tailWord_1920801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920801).length < 2 ^ (prefixWord ++ tailWord_1920801).sum := by decide
  have hdescent : baseEnd_1920801 < baseStart_1920801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920841 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 1, 5, 2]
def baseStart_1920841 : Nat := 118140960795 + 1920841 * 2 ^ 59
def prefixEnd_1920841 : Nat := 4983230072969 + 3 ^ 40 * 1920841 * 2
def baseEnd_1920841 : Nat := 986314693863024434453719

theorem tailTrace_1920841 : CollatzResearch.WordTrace tailWord_1920841 prefixEnd_1920841 986314693863024434453719 := by
  unfold tailWord_1920841
  simp only [CollatzResearch.WordTrace]
  refine ⟨70058826834128585370234377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46705884556085723580156251 70058826834128585370234377)
  ·
    refine ⟨52544120125596439027675783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70058826834128585370234377 52544120125596439027675783)
    ·
      refine ⟨78816180188394658541513675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52544120125596439027675783 78816180188394658541513675)
      ·
        refine ⟨118224270282591987812270513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78816180188394658541513675 118224270282591987812270513)
        ·
          refine ⟨88668202711943990859202885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118224270282591987812270513 88668202711943990859202885)
          ·
            refine ⟨16625288008489498286100541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88668202711943990859202885 16625288008489498286100541)
            ·
              refine ⟨6234483003183561857287703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16625288008489498286100541 6234483003183561857287703)
              ·
                refine ⟨9351724504775342785931555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6234483003183561857287703 9351724504775342785931555)
                ·
                  refine ⟨14027586757163014178897333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9351724504775342785931555 14027586757163014178897333)
                  ·
                    refine ⟨1315086258484032579271625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14027586757163014178897333 1315086258484032579271625)
                    ·
                      refine ⟨986314693863024434453719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1315086258484032579271625 986314693863024434453719)
                      ·
                        rfl

theorem cell23_1920841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 5, 2].length) (baseStart_1920841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920841 prefixEnd_1920841 := by exact prefixLift 1920841
  have htrace : WordTrace (prefixWord ++ tailWord_1920841) baseStart_1920841 baseEnd_1920841 := by
    simpa [prefixWord, tailWord_1920841, baseEnd_1920841] using wordTrace_append hprefix tailTrace_1920841
  have hstable : (prefixWord ++ tailWord_1920841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920841).length < 2 ^ (prefixWord ++ tailWord_1920841).sum := by decide
  have hdescent : baseEnd_1920841 < baseStart_1920841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920922 : List Nat := [3, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2]
def baseStart_1920922 : Nat := 118140960795 + 1920922 * 2 ^ 59
def prefixEnd_1920922 : Nat := 4983230072969 + 3 ^ 40 * 1920922 * 2
def baseEnd_1920922 : Nat := 986356285796038617540847

theorem tailTrace_1920922 : CollatzResearch.WordTrace tailWord_1920922 prefixEnd_1920922 986356285796038617540847 := by
  unfold tailWord_1920922
  simp only [CollatzResearch.WordTrace]
  refine ⟨17515445286708784050983255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46707854097890090802622013 17515445286708784050983255)
  ·
    refine ⟨26273167930063176076474883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17515445286708784050983255 26273167930063176076474883)
    ·
      refine ⟨39409751895094764114712325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26273167930063176076474883 39409751895094764114712325)
      ·
        refine ⟨7389328480330268271508561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39409751895094764114712325 7389328480330268271508561)
        ·
          refine ⟨5541996360247701203631421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7389328480330268271508561 5541996360247701203631421)
          ·
            refine ⟨2078248635092887951361783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5541996360247701203631421 2078248635092887951361783)
            ·
              refine ⟨3117372952639331927042675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078248635092887951361783 3117372952639331927042675)
              ·
                refine ⟨4676059428958997890564013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3117372952639331927042675 4676059428958997890564013)
                ·
                  refine ⟨1753522285859624208961505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4676059428958997890564013 1753522285859624208961505)
                  ·
                    refine ⟨1315141714394718156721129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1753522285859624208961505 1315141714394718156721129)
                    ·
                      refine ⟨986356285796038617540847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1315141714394718156721129 986356285796038617540847)
                      ·
                        rfl

theorem cell23_1920922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_1920922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920922 prefixEnd_1920922 := by exact prefixLift 1920922
  have htrace : WordTrace (prefixWord ++ tailWord_1920922) baseStart_1920922 baseEnd_1920922 := by
    simpa [prefixWord, tailWord_1920922, baseEnd_1920922] using wordTrace_append hprefix tailTrace_1920922
  have hstable : (prefixWord ++ tailWord_1920922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920922).length < 2 ^ (prefixWord ++ tailWord_1920922).sum := by decide
  have hdescent : baseEnd_1920922 < baseStart_1920922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920931 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 2, 7, 2]
def baseStart_1920931 : Nat := 118140960795 + 1920931 * 2 ^ 59
def prefixEnd_1920931 : Nat := 4983230072969 + 3 ^ 40 * 1920931 * 2
def baseEnd_1920931 : Nat := 986360907121929082328305

theorem tailTrace_1920931 : CollatzResearch.WordTrace tailWord_1920931 prefixEnd_1920931 986360907121929082328305 := by
  unfold tailWord_1920931
  simp only [CollatzResearch.WordTrace]
  refine ⟨70062109403802530741010647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46708072935868353827340431 70062109403802530741010647)
  ·
    refine ⟨105093164105703796111515971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70062109403802530741010647 105093164105703796111515971)
    ·
      refine ⟨157639746158555694167273957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105093164105703796111515971 157639746158555694167273957)
      ·
        refine ⟨29557452404729192656363867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157639746158555694167273957 29557452404729192656363867)
        ·
          refine ⟨44336178607093788984545801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29557452404729192656363867 44336178607093788984545801)
          ·
            refine ⟨33252133955320341738409351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44336178607093788984545801 33252133955320341738409351)
            ·
              refine ⟨49878200932980512607614027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33252133955320341738409351 49878200932980512607614027)
              ·
                refine ⟨74817301399470768911421041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49878200932980512607614027 74817301399470768911421041)
                ·
                  refine ⟨56112976049603076683565781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74817301399470768911421041 56112976049603076683565781)
                  ·
                    refine ⟨1315147876162572109771073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56112976049603076683565781 1315147876162572109771073)
                    ·
                      refine ⟨986360907121929082328305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1315147876162572109771073 986360907121929082328305)
                      ·
                        rfl

theorem cell23_1920931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_1920931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920931 prefixEnd_1920931 := by exact prefixLift 1920931
  have htrace : WordTrace (prefixWord ++ tailWord_1920931) baseStart_1920931 baseEnd_1920931 := by
    simpa [prefixWord, tailWord_1920931, baseEnd_1920931] using wordTrace_append hprefix tailTrace_1920931
  have hstable : (prefixWord ++ tailWord_1920931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920931).length < 2 ^ (prefixWord ++ tailWord_1920931).sum := by decide
  have hdescent : baseEnd_1920931 < baseStart_1920931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920954 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 3, 8]
def baseStart_1920954 : Nat := 118140960795 + 1920954 * 2 ^ 59
def prefixEnd_1920954 : Nat := 4983230072969 + 3 ^ 40 * 1920954 * 2
def baseEnd_1920954 : Nat := 328790905725660830780233

theorem tailTrace_1920954 : CollatzResearch.WordTrace tailWord_1920954 prefixEnd_1920954 328790905725660830780233 := by
  unfold tailWord_1920954
  simp only [CollatzResearch.WordTrace]
  refine ⟨17515737070679801417274479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46708632188479470446065277 17515737070679801417274479)
  ·
    refine ⟨26273605606019702125911719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17515737070679801417274479 26273605606019702125911719)
    ·
      refine ⟨39410408409029553188867579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26273605606019702125911719 39410408409029553188867579)
      ·
        refine ⟨59115612613544329783301369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39410408409029553188867579 59115612613544329783301369)
        ·
          refine ⟨44336709460158247337476027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59115612613544329783301369 44336709460158247337476027)
          ·
            refine ⟨66505064190237371006214041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44336709460158247337476027 66505064190237371006214041)
            ·
              refine ⟨49878798142678028254660531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66505064190237371006214041 49878798142678028254660531)
              ·
                refine ⟨74818197214017042381990797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49878798142678028254660531 74818197214017042381990797)
                ·
                  refine ⟨28056823955256390893246549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74818197214017042381990797 28056823955256390893246549)
                  ·
                    refine ⟨328790905725660830780233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 28056823955256390893246549 328790905725660830780233)
                    ·
                      rfl

theorem cell23_1920954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_1920954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920954 prefixEnd_1920954 := by exact prefixLift 1920954
  have htrace : WordTrace (prefixWord ++ tailWord_1920954) baseStart_1920954 baseEnd_1920954 := by
    simpa [prefixWord, tailWord_1920954, baseEnd_1920954] using wordTrace_append hprefix tailTrace_1920954
  have hstable : (prefixWord ++ tailWord_1920954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920954).length < 2 ^ (prefixWord ++ tailWord_1920954).sum := by decide
  have hdescent : baseEnd_1920954 < baseStart_1920954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920991 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 4]
def baseStart_1920991 : Nat := 118140960795 + 1920991 * 2 ^ 59
def prefixEnd_1920991 : Nat := 4983230072969 + 3 ^ 40 * 1920991 * 2
def baseEnd_1920991 : Nat := 986391715961198847578029

theorem tailTrace_1920991 : CollatzResearch.WordTrace tailWord_1920991 prefixEnd_1920991 986391715961198847578029 := by
  unfold tailWord_1920991
  simp only [CollatzResearch.WordTrace]
  refine ⟨70064297783585160988194827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46709531855723440658796551 70064297783585160988194827)
  ·
    refine ⟨105096446675377741482292241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70064297783585160988194827 105096446675377741482292241)
    ·
      refine ⟨78822335006533306111719181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105096446675377741482292241 78822335006533306111719181)
      ·
        refine ⟨29558375627449989791894693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78822335006533306111719181 29558375627449989791894693)
        ·
          refine ⟨5542195430146873085980255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29558375627449989791894693 5542195430146873085980255)
          ·
            refine ⟨8313293145220309628970383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5542195430146873085980255 8313293145220309628970383)
            ·
              refine ⟨12469939717830464443455575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8313293145220309628970383 12469939717830464443455575)
              ·
                refine ⟨18704909576745696665183363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12469939717830464443455575 18704909576745696665183363)
                ·
                  refine ⟨28057364365118544997775045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18704909576745696665183363 28057364365118544997775045)
                  ·
                    refine ⟨5260755818459727187082821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28057364365118544997775045 5260755818459727187082821)
                    ·
                      refine ⟨986391715961198847578029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5260755818459727187082821 986391715961198847578029)
                      ·
                        rfl

theorem cell23_1920991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_1920991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920991 prefixEnd_1920991 := by exact prefixLift 1920991
  have htrace : WordTrace (prefixWord ++ tailWord_1920991) baseStart_1920991 baseEnd_1920991 := by
    simpa [prefixWord, tailWord_1920991, baseEnd_1920991] using wordTrace_append hprefix tailTrace_1920991
  have hstable : (prefixWord ++ tailWord_1920991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920991).length < 2 ^ (prefixWord ++ tailWord_1920991).sum := by decide
  have hdescent : baseEnd_1920991 < baseStart_1920991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1920995 : List Nat := [1, 1, 1, 6, 1, 3, 2, 1, 1, 4, 2]
def baseStart_1920995 : Nat := 118140960795 + 1920995 * 2 ^ 59
def prefixEnd_1920995 : Nat := 4983230072969 + 3 ^ 40 * 1920995 * 2
def baseEnd_1920995 : Nat := 986393769883816831928011

theorem tailTrace_1920995 : CollatzResearch.WordTrace tailWord_1920995 prefixEnd_1920995 986393769883816831928011 := by
  unfold tailWord_1920995
  simp only [CollatzResearch.WordTrace]
  refine ⟨70064443675570669671340439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46709629117047113114226959 70064443675570669671340439)
  ·
    refine ⟨105096665513356004507010659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70064443675570669671340439 105096665513356004507010659)
    ·
      refine ⟨157644998270034006760515989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105096665513356004507010659 157644998270034006760515989)
      ·
        refine ⟨7389609293907844066899187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 157644998270034006760515989 7389609293907844066899187)
        ·
          refine ⟨11084413940861766100348781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7389609293907844066899187 11084413940861766100348781)
          ·
            refine ⟨4156655227823162287630793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11084413940861766100348781 4156655227823162287630793)
            ·
              refine ⟨3117491420867371715723095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4156655227823162287630793 3117491420867371715723095)
              ·
                refine ⟨4676237131301057573584643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3117491420867371715723095 4676237131301057573584643)
                ·
                  refine ⟨7014355696951586360376965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4676237131301057573584643 7014355696951586360376965)
                  ·
                    refine ⟨1315191693178422442570681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7014355696951586360376965 1315191693178422442570681)
                    ·
                      refine ⟨986393769883816831928011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1315191693178422442570681 986393769883816831928011)
                      ·
                        rfl

theorem cell23_1920995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_1920995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1920995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1920995 prefixEnd_1920995 := by exact prefixLift 1920995
  have htrace : WordTrace (prefixWord ++ tailWord_1920995) baseStart_1920995 baseEnd_1920995 := by
    simpa [prefixWord, tailWord_1920995, baseEnd_1920995] using wordTrace_append hprefix tailTrace_1920995
  have hstable : (prefixWord ++ tailWord_1920995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1920995).length < 2 ^ (prefixWord ++ tailWord_1920995).sum := by decide
  have hdescent : baseEnd_1920995 < baseStart_1920995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1920995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921051 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 4]
def baseStart_1921051 : Nat := 118140960795 + 1921051 * 2 ^ 59
def prefixEnd_1921051 : Nat := 4983230072969 + 3 ^ 40 * 1921051 * 2
def baseEnd_1921051 : Nat := 986422524800468612827753

theorem tailTrace_1921051 : CollatzResearch.WordTrace tailWord_1921051 prefixEnd_1921051 986422524800468612827753 := by
  unfold tailWord_1921051
  simp only [CollatzResearch.WordTrace]
  refine ⟨70066486163367791235379007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46710990775578527490252671 70066486163367791235379007)
  ·
    refine ⟨105099729245051686853068511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70066486163367791235379007 105099729245051686853068511)
    ·
      refine ⟨157649593867577530279602767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105099729245051686853068511 157649593867577530279602767)
      ·
        refine ⟨236474390801366295419404151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157649593867577530279602767 236474390801366295419404151)
        ·
          refine ⟨354711586202049443129106227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236474390801366295419404151 354711586202049443129106227)
          ·
            refine ⟨532067379303074164693659341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354711586202049443129106227 532067379303074164693659341)
            ·
              refine ⟨199525267238652811760122253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 532067379303074164693659341 199525267238652811760122253)
              ·
                refine ⟨74821975214494804410045845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199525267238652811760122253 74821975214494804410045845)
                ·
                  refine ⟨3507280088179443956720899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 74821975214494804410045845 3507280088179443956720899)
                  ·
                    refine ⟨5260920132269165935081349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3507280088179443956720899 5260920132269165935081349)
                    ·
                      refine ⟨986422524800468612827753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5260920132269165935081349 986422524800468612827753)
                      ·
                        rfl

theorem cell23_1921051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 4].length) (baseStart_1921051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921051 prefixEnd_1921051 := by exact prefixLift 1921051
  have htrace : WordTrace (prefixWord ++ tailWord_1921051) baseStart_1921051 baseEnd_1921051 := by
    simpa [prefixWord, tailWord_1921051, baseEnd_1921051] using wordTrace_append hprefix tailTrace_1921051
  have hstable : (prefixWord ++ tailWord_1921051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921051).length < 2 ^ (prefixWord ++ tailWord_1921051).sum := by decide
  have hdescent : baseEnd_1921051 < baseStart_1921051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921068 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 4, 4, 2]
def baseStart_1921068 : Nat := 118140960795 + 1921068 * 2 ^ 59
def prefixEnd_1921068 : Nat := 4983230072969 + 3 ^ 40 * 1921068 * 2
def baseEnd_1921068 : Nat := 986431253971595046315175

theorem tailTrace_1921068 : CollatzResearch.WordTrace tailWord_1921068 prefixEnd_1921068 986431253971595046315175 := by
  unfold tailWord_1921068
  simp only [CollatzResearch.WordTrace]
  refine ⟨35033553102153101569373929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46711404136204135425831905 35033553102153101569373929)
  ·
    refine ⟨26275164826614826177030447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35033553102153101569373929 26275164826614826177030447)
    ·
      refine ⟨39412747239922239265545671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26275164826614826177030447 39412747239922239265545671)
      ·
        refine ⟨59119120859883358898318507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39412747239922239265545671 59119120859883358898318507)
        ·
          refine ⟨88678681289825038347477761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59119120859883358898318507 88678681289825038347477761)
          ·
            refine ⟨66509010967368778760608321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88678681289825038347477761 66509010967368778760608321)
            ·
              refine ⟨49881758225526584070456241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66509010967368778760608321 49881758225526584070456241)
              ·
                refine ⟨37411318669144938052842181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49881758225526584070456241 37411318669144938052842181)
                ·
                  refine ⟨7014622250464675884907909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37411318669144938052842181 7014622250464675884907909)
                  ·
                    refine ⟨1315241671962126728420233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7014622250464675884907909 1315241671962126728420233)
                    ·
                      refine ⟨986431253971595046315175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1315241671962126728420233 986431253971595046315175)
                      ·
                        rfl

theorem cell23_1921068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 4, 2].length) (baseStart_1921068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921068 prefixEnd_1921068 := by exact prefixLift 1921068
  have htrace : WordTrace (prefixWord ++ tailWord_1921068) baseStart_1921068 baseEnd_1921068 := by
    simpa [prefixWord, tailWord_1921068, baseEnd_1921068] using wordTrace_append hprefix tailTrace_1921068
  have hstable : (prefixWord ++ tailWord_1921068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921068).length < 2 ^ (prefixWord ++ tailWord_1921068).sum := by decide
  have hdescent : baseEnd_1921068 < baseStart_1921068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921088 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 3]
def baseStart_1921088 : Nat := 118140960795 + 1921088 * 2 ^ 59
def prefixEnd_1921088 : Nat := 4983230072969 + 3 ^ 40 * 1921088 * 2
def baseEnd_1921088 : Nat := 986441523584684968065083

theorem tailTrace_1921088 : CollatzResearch.WordTrace tailWord_1921088 prefixEnd_1921088 986441523584684968065083 := by
  unfold tailWord_1921088
  simp only [CollatzResearch.WordTrace]
  refine ⟨35033917832116873277237959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46711890442822497702983945 35033917832116873277237959)
  ·
    refine ⟨52550876748175309915856939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35033917832116873277237959 52550876748175309915856939)
    ·
      refine ⟨78826315122262964873785409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52550876748175309915856939 78826315122262964873785409)
      ·
        refine ⟨59119736341697223655339057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78826315122262964873785409 59119736341697223655339057)
        ·
          refine ⟨44339802256272917741504293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59119736341697223655339057 44339802256272917741504293)
          ·
            refine ⟨8313712923051172076532055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44339802256272917741504293 8313712923051172076532055)
            ·
              refine ⟨12470569384576758114798083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8313712923051172076532055 12470569384576758114798083)
              ·
                refine ⟨18705854076865137172197125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12470569384576758114798083 18705854076865137172197125)
                ·
                  refine ⟨3507347639412213219786961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18705854076865137172197125 3507347639412213219786961)
                  ·
                    refine ⟨2630510729559159914840221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3507347639412213219786961 2630510729559159914840221)
                    ·
                      refine ⟨986441523584684968065083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2630510729559159914840221 986441523584684968065083)
                      ·
                        rfl

theorem cell23_1921088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_1921088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921088 prefixEnd_1921088 := by exact prefixLift 1921088
  have htrace : WordTrace (prefixWord ++ tailWord_1921088) baseStart_1921088 baseEnd_1921088 := by
    simpa [prefixWord, tailWord_1921088, baseEnd_1921088] using wordTrace_append hprefix tailTrace_1921088
  have hstable : (prefixWord ++ tailWord_1921088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921088).length < 2 ^ (prefixWord ++ tailWord_1921088).sum := by decide
  have hdescent : baseEnd_1921088 < baseStart_1921088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921111 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 6]
def baseStart_1921111 : Nat := 118140960795 + 1921111 * 2 ^ 59
def prefixEnd_1921111 : Nat := 4983230072969 + 3 ^ 40 * 1921111 * 2
def baseEnd_1921111 : Nat := 986453333639738378077477

theorem tailTrace_1921111 : CollatzResearch.WordTrace tailWord_1921111 prefixEnd_1921111 986453333639738378077477 := by
  unfold tailWord_1921111
  simp only [CollatzResearch.WordTrace]
  refine ⟨70068674543150421482563187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46712449695433614321708791 70068674543150421482563187)
  ·
    refine ⟨105103011814725632223844781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70068674543150421482563187 105103011814725632223844781)
    ·
      refine ⟨39413629430522112083941793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105103011814725632223844781 39413629430522112083941793)
      ·
        refine ⟨29560222072891584062956345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39413629430522112083941793 29560222072891584062956345)
        ·
          refine ⟨22170166554668688047217259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29560222072891584062956345 22170166554668688047217259)
          ·
            refine ⟨33255249832003032070825889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22170166554668688047217259 33255249832003032070825889)
            ·
              refine ⟨24941437374002274053119417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33255249832003032070825889 24941437374002274053119417)
              ·
                refine ⟨18706078030501705539839563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24941437374002274053119417 18706078030501705539839563)
                ·
                  refine ⟨28059117045752558309759345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18706078030501705539839563 28059117045752558309759345)
                  ·
                    refine ⟨21044337784314418732319509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28059117045752558309759345 21044337784314418732319509)
                    ·
                      refine ⟨986453333639738378077477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 21044337784314418732319509 986453333639738378077477)
                      ·
                        rfl

theorem cell23_1921111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_1921111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921111 prefixEnd_1921111 := by exact prefixLift 1921111
  have htrace : WordTrace (prefixWord ++ tailWord_1921111) baseStart_1921111 baseEnd_1921111 := by
    simpa [prefixWord, tailWord_1921111, baseEnd_1921111] using wordTrace_append hprefix tailTrace_1921111
  have hstable : (prefixWord ++ tailWord_1921111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921111).length < 2 ^ (prefixWord ++ tailWord_1921111).sum := by decide
  have hdescent : baseEnd_1921111 < baseStart_1921111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921168 : List Nat := [2, 1, 1, 1, 1, 1, 8, 1, 1, 6]
def baseStart_1921168 : Nat := 118140960795 + 1921168 * 2 ^ 59
def prefixEnd_1921168 : Nat := 4983230072969 + 3 ^ 40 * 1921168 * 2
def baseEnd_1921168 : Nat := 328827534012348218354905

theorem tailTrace_1921168 : CollatzResearch.WordTrace tailWord_1921168 prefixEnd_1921168 328827534012348218354905 := by
  unfold tailWord_1921168
  simp only [CollatzResearch.WordTrace]
  refine ⟨35035376751971960108694079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46713835669295946811592105 35035376751971960108694079)
  ·
    refine ⟨52553065127957940163041119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35035376751971960108694079 52553065127957940163041119)
    ·
      refine ⟨78829597691936910244561679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52553065127957940163041119 78829597691936910244561679)
      ·
        refine ⟨118244396537905365366842519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78829597691936910244561679 118244396537905365366842519)
        ·
          refine ⟨177366594806858048050263779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118244396537905365366842519 177366594806858048050263779)
          ·
            refine ⟨266049892210287072075395669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177366594806858048050263779 266049892210287072075395669)
            ·
              refine ⟨3117772174339301625883543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 266049892210287072075395669 3117772174339301625883543)
              ·
                refine ⟨4676658261508952438825315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3117772174339301625883543 4676658261508952438825315)
                ·
                  refine ⟨7014987392263428658237973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4676658261508952438825315 7014987392263428658237973)
                  ·
                    refine ⟨328827534012348218354905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7014987392263428658237973 328827534012348218354905)
                    ·
                      rfl

theorem cell23_1921168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 1, 6].length) (baseStart_1921168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921168 prefixEnd_1921168 := by exact prefixLift 1921168
  have htrace : WordTrace (prefixWord ++ tailWord_1921168) baseStart_1921168 baseEnd_1921168 := by
    simpa [prefixWord, tailWord_1921168, baseEnd_1921168] using wordTrace_append hprefix tailTrace_1921168
  have hstable : (prefixWord ++ tailWord_1921168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921168).length < 2 ^ (prefixWord ++ tailWord_1921168).sum := by decide
  have hdescent : baseEnd_1921168 < baseStart_1921168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921186 : List Nat := [3, 3, 1, 3, 1, 2, 2, 3, 1, 1, 3]
def baseStart_1921186 : Nat := 118140960795 + 1921186 * 2 ^ 59
def prefixEnd_1921186 : Nat := 4983230072969 + 3 ^ 40 * 1921186 * 2
def baseEnd_1921186 : Nat := 986491844688825584639633

theorem tailTrace_1921186 : CollatzResearch.WordTrace tailWord_1921186 prefixEnd_1921186 986491844688825584639633 := by
  unfold tailWord_1921186
  simp only [CollatzResearch.WordTrace]
  refine ⟨17517852504469677322885853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46714273345252472861028941 17517852504469677322885853)
  ·
    refine ⟨6569194689176128996082195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17517852504469677322885853 6569194689176128996082195)
    ·
      refine ⟨9853792033764193494123293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6569194689176128996082195 9853792033764193494123293)
      ·
        refine ⟨3695172012661572560296235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9853792033764193494123293 3695172012661572560296235)
        ·
          refine ⟨5542758018992358840444353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3695172012661572560296235 5542758018992358840444353)
          ·
            refine ⟨4157068514244269130333265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5542758018992358840444353 4157068514244269130333265)
            ·
              refine ⟨3117801385683201847749949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4157068514244269130333265 3117801385683201847749949)
              ·
                refine ⟨1169175519631200692906231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3117801385683201847749949 1169175519631200692906231)
                ·
                  refine ⟨1753763279446801039359347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1169175519631200692906231 1753763279446801039359347)
                  ·
                    refine ⟨2630644919170201559039021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1753763279446801039359347 2630644919170201559039021)
                    ·
                      refine ⟨986491844688825584639633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2630644919170201559039021 986491844688825584639633)
                      ·
                        rfl

theorem cell23_1921186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_1921186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921186 prefixEnd_1921186 := by exact prefixLift 1921186
  have htrace : WordTrace (prefixWord ++ tailWord_1921186) baseStart_1921186 baseEnd_1921186 := by
    simpa [prefixWord, tailWord_1921186, baseEnd_1921186] using wordTrace_append hprefix tailTrace_1921186
  have hstable : (prefixWord ++ tailWord_1921186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921186).length < 2 ^ (prefixWord ++ tailWord_1921186).sum := by decide
  have hdescent : baseEnd_1921186 < baseStart_1921186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921209 : List Nat := [1, 2, 1, 4, 1, 2, 1, 6, 1, 2, 2]
def baseStart_1921209 : Nat := 118140960795 + 1921209 * 2 ^ 59
def prefixEnd_1921209 : Nat := 4983230072969 + 3 ^ 40 * 1921209 * 2
def baseEnd_1921209 : Nat := 986503654743878994652027

theorem tailTrace_1921209 : CollatzResearch.WordTrace tailWord_1921209 prefixEnd_1921209 986503654743878994652027 := by
  unfold tailWord_1921209
  simp only [CollatzResearch.WordTrace]
  refine ⟨70072248896795384219630681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46714832597863589479753787 70072248896795384219630681)
  ·
    refine ⟨52554186672596538164723011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70072248896795384219630681 52554186672596538164723011)
    ·
      refine ⟨78831280008894807247084517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52554186672596538164723011 78831280008894807247084517)
      ·
        refine ⟨14780865001667776358828347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78831280008894807247084517 14780865001667776358828347)
        ·
          refine ⟨22171297502501664538242521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14780865001667776358828347 22171297502501664538242521)
          ·
            refine ⟨16628473126876248403681891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22171297502501664538242521 16628473126876248403681891)
            ·
              refine ⟨24942709690314372605522837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16628473126876248403681891 24942709690314372605522837)
              ·
                refine ⟨1169189516733486215883883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24942709690314372605522837 1169189516733486215883883)
                ·
                  refine ⟨1753784275100229323825825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1169189516733486215883883 1753784275100229323825825)
                  ·
                    refine ⟨1315338206325171992869369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1753784275100229323825825 1315338206325171992869369)
                    ·
                      refine ⟨986503654743878994652027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1315338206325171992869369 986503654743878994652027)
                      ·
                        rfl

theorem cell23_1921209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_1921209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921209 prefixEnd_1921209 := by exact prefixLift 1921209
  have htrace : WordTrace (prefixWord ++ tailWord_1921209) baseStart_1921209 baseEnd_1921209 := by
    simpa [prefixWord, tailWord_1921209, baseEnd_1921209] using wordTrace_append hprefix tailTrace_1921209
  have hstable : (prefixWord ++ tailWord_1921209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921209).length < 2 ^ (prefixWord ++ tailWord_1921209).sum := by decide
  have hdescent : baseEnd_1921209 < baseStart_1921209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921276 : List Nat := [2, 2, 2, 1, 4, 3, 2, 1, 2, 1, 3]
def baseStart_1921276 : Nat := 118140960795 + 1921276 * 2 ^ 59
def prefixEnd_1921276 : Nat := 4983230072969 + 3 ^ 40 * 1921276 * 2
def baseEnd_1921276 : Nat := 986538057947730232514219

theorem tailTrace_1921276 : CollatzResearch.WordTrace tailWord_1921276 prefixEnd_1921276 986538057947730232514219 := by
  unfold tailWord_1921276
  simp only [CollatzResearch.WordTrace]
  refine ⟨35037346293776327331159841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46716461725035103108213121 35037346293776327331159841)
  ·
    refine ⟨26278009720332245498369881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35037346293776327331159841 26278009720332245498369881)
    ·
      refine ⟨19708507290249184123777411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26278009720332245498369881 19708507290249184123777411)
      ·
        refine ⟨29562760935373776185666117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19708507290249184123777411 29562760935373776185666117)
        ·
          refine ⟨5543017675382583034812397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29562760935373776185666117 5543017675382583034812397)
          ·
            refine ⟨2078631628268468638054649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5543017675382583034812397 2078631628268468638054649)
            ·
              refine ⟨1558973721201351478540987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2078631628268468638054649 1558973721201351478540987)
              ·
                refine ⟨2338460581802027217811481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1558973721201351478540987 2338460581802027217811481)
                ·
                  refine ⟨1753845436351520413358611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2338460581802027217811481 1753845436351520413358611)
                  ·
                    refine ⟨2630768154527280620037917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1753845436351520413358611 2630768154527280620037917)
                    ·
                      refine ⟨986538057947730232514219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2630768154527280620037917 986538057947730232514219)
                      ·
                        rfl

theorem cell23_1921276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_1921276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921276 prefixEnd_1921276 := by exact prefixLift 1921276
  have htrace : WordTrace (prefixWord ++ tailWord_1921276) baseStart_1921276 baseEnd_1921276 := by
    simpa [prefixWord, tailWord_1921276, baseEnd_1921276] using wordTrace_append hprefix tailTrace_1921276
  have hstable : (prefixWord ++ tailWord_1921276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921276).length < 2 ^ (prefixWord ++ tailWord_1921276).sum := by decide
  have hdescent : baseEnd_1921276 < baseStart_1921276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921315 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 3]
def baseStart_1921315 : Nat := 118140960795 + 1921315 * 2 ^ 59
def prefixEnd_1921315 : Nat := 4983230072969 + 3 ^ 40 * 1921315 * 2
def baseEnd_1921315 : Nat := 986558083693255579926539

theorem tailTrace_1921315 : CollatzResearch.WordTrace tailWord_1921315 prefixEnd_1921315 986558083693255579926539 := by
  unfold tailWord_1921315
  simp only [CollatzResearch.WordTrace]
  refine ⟨70076115034411364322989399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46717410022940909548659599 70076115034411364322989399)
  ·
    refine ⟨105114172551617046484484099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70076115034411364322989399 105114172551617046484484099)
    ·
      refine ⟨157671258827425569726726149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105114172551617046484484099 157671258827425569726726149)
      ·
        refine ⟨29563361030142294323761153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157671258827425569726726149 29563361030142294323761153)
        ·
          refine ⟨22172520772606720742820865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29563361030142294323761153 22172520772606720742820865)
          ·
            refine ⟨16629390579455040557115649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22172520772606720742820865 16629390579455040557115649)
            ·
              refine ⟨12472042934591280417836737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16629390579455040557115649 12472042934591280417836737)
              ·
                refine ⟨9354032200943460313377553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12472042934591280417836737 9354032200943460313377553)
                ·
                  refine ⟨7015524150707595235033165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9354032200943460313377553 7015524150707595235033165)
                  ·
                    refine ⟨2630821556515348213137437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7015524150707595235033165 2630821556515348213137437)
                    ·
                      refine ⟨986558083693255579926539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2630821556515348213137437 986558083693255579926539)
                      ·
                        rfl

theorem cell23_1921315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_1921315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921315 prefixEnd_1921315 := by exact prefixLift 1921315
  have htrace : WordTrace (prefixWord ++ tailWord_1921315) baseStart_1921315 baseEnd_1921315 := by
    simpa [prefixWord, tailWord_1921315, baseEnd_1921315] using wordTrace_append hprefix tailTrace_1921315
  have hstable : (prefixWord ++ tailWord_1921315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921315).length < 2 ^ (prefixWord ++ tailWord_1921315).sum := by decide
  have hdescent : baseEnd_1921315 < baseStart_1921315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921316 : List Nat := [2, 3, 1, 3, 1, 3, 2, 2, 2, 2, 2]
def baseStart_1921316 : Nat := 118140960795 + 1921316 * 2 ^ 59
def prefixEnd_1921316 : Nat := 4983230072969 + 3 ^ 40 * 1921316 * 2
def baseEnd_1921316 : Nat := 986558597173910076014035

theorem tailTrace_1921316 : CollatzResearch.WordTrace tailWord_1921316 prefixEnd_1921316 986558597173910076014035 := by
  unfold tailWord_1921316
  simp only [CollatzResearch.WordTrace]
  refine ⟨35038075753703870746887901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46717434338271827662517201 35038075753703870746887901)
  ·
    refine ⟨13139278407638951530082963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35038075753703870746887901 13139278407638951530082963)
    ·
      refine ⟨19708917611458427295124445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13139278407638951530082963 19708917611458427295124445)
      ·
        refine ⟨7390844104296910235671667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19708917611458427295124445 7390844104296910235671667)
        ·
          refine ⟨11086266156445365353507501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7390844104296910235671667 11086266156445365353507501)
          ·
            refine ⟨4157349808667012007565313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11086266156445365353507501 4157349808667012007565313)
            ·
              refine ⟨3118012356500259005673985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4157349808667012007565313 3118012356500259005673985)
              ·
                refine ⟨2338509267375194254255489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3118012356500259005673985 2338509267375194254255489)
                ·
                  refine ⟨1753881950531395690691617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2338509267375194254255489 1753881950531395690691617)
                  ·
                    refine ⟨1315411462898546768018713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1753881950531395690691617 1315411462898546768018713)
                    ·
                      refine ⟨986558597173910076014035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1315411462898546768018713 986558597173910076014035)
                      ·
                        rfl

theorem cell23_1921316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_1921316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921316 prefixEnd_1921316 := by exact prefixLift 1921316
  have htrace : WordTrace (prefixWord ++ tailWord_1921316) baseStart_1921316 baseEnd_1921316 := by
    simpa [prefixWord, tailWord_1921316, baseEnd_1921316] using wordTrace_append hprefix tailTrace_1921316
  have hstable : (prefixWord ++ tailWord_1921316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921316).length < 2 ^ (prefixWord ++ tailWord_1921316).sum := by decide
  have hdescent : baseEnd_1921316 < baseStart_1921316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921328 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 7]
def baseStart_1921328 : Nat := 118140960795 + 1921328 * 2 ^ 59
def prefixEnd_1921328 : Nat := 4983230072969 + 3 ^ 40 * 1921328 * 2
def baseEnd_1921328 : Nat := 986564758941764029063979

theorem tailTrace_1921328 : CollatzResearch.WordTrace tailWord_1921328 prefixEnd_1921328 986564758941764029063979 := by
  unfold tailWord_1921328
  simp only [CollatzResearch.WordTrace]
  refine ⟨35038294591682133771606319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46717726122242845028808425 35038294591682133771606319)
  ·
    refine ⟨52557441887523200657409479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35038294591682133771606319 52557441887523200657409479)
    ·
      refine ⟨78836162831284800986114219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52557441887523200657409479 78836162831284800986114219)
      ·
        refine ⟨118254244246927201479171329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78836162831284800986114219 118254244246927201479171329)
        ·
          refine ⟨88690683185195401109378497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118254244246927201479171329 88690683185195401109378497)
          ·
            refine ⟨66518012388896550832033873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88690683185195401109378497 66518012388896550832033873)
            ·
              refine ⟨49888509291672413124025405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66518012388896550832033873 49888509291672413124025405)
              ·
                refine ⟨18708190984377154921509527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49888509291672413124025405 18708190984377154921509527)
                ·
                  refine ⟨28062286476565732382264291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18708190984377154921509527 28062286476565732382264291)
                  ·
                    refine ⟨42093429714848598573396437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28062286476565732382264291 42093429714848598573396437)
                    ·
                      refine ⟨986564758941764029063979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 42093429714848598573396437 986564758941764029063979)
                      ·
                        rfl

theorem cell23_1921328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_1921328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921328 prefixEnd_1921328 := by exact prefixLift 1921328
  have htrace : WordTrace (prefixWord ++ tailWord_1921328) baseStart_1921328 baseEnd_1921328 := by
    simpa [prefixWord, tailWord_1921328, baseEnd_1921328] using wordTrace_append hprefix tailTrace_1921328
  have hstable : (prefixWord ++ tailWord_1921328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921328).length < 2 ^ (prefixWord ++ tailWord_1921328).sum := by decide
  have hdescent : baseEnd_1921328 < baseStart_1921328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921332 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_1921332 : Nat := 118140960795 + 1921332 * 2 ^ 59
def prefixEnd_1921332 : Nat := 4983230072969 + 3 ^ 40 * 1921332 * 2
def baseEnd_1921332 : Nat := 986566812864382013413961

theorem tailTrace_1921332 : CollatzResearch.WordTrace tailWord_1921332 prefixEnd_1921332 986566812864382013413961 := by
  unfold tailWord_1921332
  simp only [CollatzResearch.WordTrace]
  refine ⟨35038367537674888113179125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46717823383566517484238833 35038367537674888113179125)
  ·
    refine ⟨3284846956657020760610543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35038367537674888113179125 3284846956657020760610543)
    ·
      refine ⟨4927270434985531140915815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3284846956657020760610543 4927270434985531140915815)
      ·
        refine ⟨7390905652478296711373723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4927270434985531140915815 7390905652478296711373723)
        ·
          refine ⟨11086358478717445067060585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7390905652478296711373723 11086358478717445067060585)
          ·
            refine ⟨8314768859038083800295439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11086358478717445067060585 8314768859038083800295439)
            ·
              refine ⟨12472153288557125700443159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8314768859038083800295439 12472153288557125700443159)
              ·
                refine ⟨18708229932835688550664739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12472153288557125700443159 18708229932835688550664739)
                ·
                  refine ⟨28062344899253532825997109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18708229932835688550664739 28062344899253532825997109)
                  ·
                    refine ⟨2630844834305018702437229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28062344899253532825997109 2630844834305018702437229)
                    ·
                      refine ⟨986566812864382013413961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2630844834305018702437229 986566812864382013413961)
                      ·
                        rfl

theorem cell23_1921332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_1921332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921332 prefixEnd_1921332 := by exact prefixLift 1921332
  have htrace : WordTrace (prefixWord ++ tailWord_1921332) baseStart_1921332 baseEnd_1921332 := by
    simpa [prefixWord, tailWord_1921332, baseEnd_1921332] using wordTrace_append hprefix tailTrace_1921332
  have hstable : (prefixWord ++ tailWord_1921332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921332).length < 2 ^ (prefixWord ++ tailWord_1921332).sum := by decide
  have hdescent : baseEnd_1921332 < baseStart_1921332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921355 : List Nat := [1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 4]
def baseStart_1921355 : Nat := 118140960795 + 1921355 * 2 ^ 59
def prefixEnd_1921355 : Nat := 4983230072969 + 3 ^ 40 * 1921355 * 2
def baseEnd_1921355 : Nat := 986578622919435423426355

theorem tailTrace_1921355 : CollatzResearch.WordTrace tailWord_1921355 prefixEnd_1921355 986578622919435423426355 := by
  unfold tailWord_1921355
  simp only [CollatzResearch.WordTrace]
  refine ⟨70077573954266451154445519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46718382636177634102963679 70077573954266451154445519)
  ·
    refine ⟨105116360931399676731668279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70077573954266451154445519 105116360931399676731668279)
    ·
      refine ⟨157674541397099515097502419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105116360931399676731668279 157674541397099515097502419)
      ·
        refine ⟨236511812095649272646253629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157674541397099515097502419 236511812095649272646253629)
        ·
          refine ⟨88691929535868477242345111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236511812095649272646253629 88691929535868477242345111)
          ·
            refine ⟨133037894303802715863517667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88691929535868477242345111 133037894303802715863517667)
            ·
              refine ⟨199556841455704073795276501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133037894303802715863517667 199556841455704073795276501)
              ·
                refine ⟨4677113471618064229576793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 199556841455704073795276501 4677113471618064229576793)
                ·
                  refine ⟨3507835103713548172182595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4677113471618064229576793 3507835103713548172182595)
                  ·
                    refine ⟨5261752655570322258273893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3507835103713548172182595 5261752655570322258273893)
                    ·
                      refine ⟨986578622919435423426355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5261752655570322258273893 986578622919435423426355)
                      ·
                        rfl

theorem cell23_1921355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 4].length) (baseStart_1921355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921355 prefixEnd_1921355 := by exact prefixLift 1921355
  have htrace : WordTrace (prefixWord ++ tailWord_1921355) baseStart_1921355 baseEnd_1921355 := by
    simpa [prefixWord, tailWord_1921355, baseEnd_1921355] using wordTrace_append hprefix tailTrace_1921355
  have hstable : (prefixWord ++ tailWord_1921355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921355).length < 2 ^ (prefixWord ++ tailWord_1921355).sum := by decide
  have hdescent : baseEnd_1921355 < baseStart_1921355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921442 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_1921442 : Nat := 118140960795 + 1921442 * 2 ^ 59
def prefixEnd_1921442 : Nat := 4983230072969 + 3 ^ 40 * 1921442 * 2
def baseEnd_1921442 : Nat := 328874431912125527679485

theorem tailTrace_1921442 : CollatzResearch.WordTrace tailWord_1921442 prefixEnd_1921442 328874431912125527679485 := by
  unfold tailWord_1921442
  simp only [CollatzResearch.WordTrace]
  refine ⟨17520186776237816253215645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46720498069967510008575053 17520186776237816253215645)
  ·
    refine ⟨6570070041089181094955867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17520186776237816253215645 6570070041089181094955867)
    ·
      refine ⟨9855105061633771642433801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6570070041089181094955867 9855105061633771642433801)
      ·
        refine ⟨7391328796225328731825351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9855105061633771642433801 7391328796225328731825351)
        ·
          refine ⟨11086993194337993097738027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7391328796225328731825351 11086993194337993097738027)
          ·
            refine ⟨16630489791506989646607041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11086993194337993097738027 16630489791506989646607041)
            ·
              refine ⟨12472867343630242234955281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16630489791506989646607041 12472867343630242234955281)
              ·
                refine ⟨9354650507722681676216461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12472867343630242234955281 9354650507722681676216461)
                ·
                  refine ⟨3507993940396005628581173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9354650507722681676216461 3507993940396005628581173)
                  ·
                    refine ⟨328874431912125527679485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3507993940396005628581173 328874431912125527679485)
                    ·
                      rfl

theorem cell23_1921442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_1921442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921442 prefixEnd_1921442 := by exact prefixLift 1921442
  have htrace : WordTrace (prefixWord ++ tailWord_1921442) baseStart_1921442 baseEnd_1921442 := by
    simpa [prefixWord, tailWord_1921442, baseEnd_1921442] using wordTrace_append hprefix tailTrace_1921442
  have hstable : (prefixWord ++ tailWord_1921442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921442).length < 2 ^ (prefixWord ++ tailWord_1921442).sum := by decide
  have hdescent : baseEnd_1921442 < baseStart_1921442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921485 : List Nat := [1, 6, 16]
def baseStart_1921485 : Nat := 118140960795 + 1921485 * 2 ^ 59
def prefixEnd_1921485 : Nat := 4983230072969 + 3 ^ 40 * 1921485 * 2
def baseEnd_1921485 : Nat := 150380334614314878037

theorem tailTrace_1921485 : CollatzResearch.WordTrace tailWord_1921485 prefixEnd_1921485 150380334614314878037 := by
  unfold tailWord_1921485
  simp only [CollatzResearch.WordTrace]
  refine ⟨70082315443795483356677909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46721543629196988904451939 70082315443795483356677909)
  ·
    refine ⟨3285108536427913282344277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70082315443795483356677909 3285108536427913282344277)
    ·
      refine ⟨150380334614314878037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 16 3285108536427913282344277 150380334614314878037)
      ·
        rfl

theorem cell23_1921485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 16].length) (baseStart_1921485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921485 prefixEnd_1921485 := by exact prefixLift 1921485
  have htrace : WordTrace (prefixWord ++ tailWord_1921485) baseStart_1921485 baseEnd_1921485 := by
    simpa [prefixWord, tailWord_1921485, baseEnd_1921485] using wordTrace_append hprefix tailTrace_1921485
  have hstable : (prefixWord ++ tailWord_1921485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921485).length < 2 ^ (prefixWord ++ tailWord_1921485).sum := by decide
  have hdescent : baseEnd_1921485 < baseStart_1921485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921490 : List Nat := [3, 2, 2, 4, 1, 1, 1, 4, 1, 1, 3]
def baseStart_1921490 : Nat := 118140960795 + 1921490 * 2 ^ 59
def prefixEnd_1921490 : Nat := 4983230072969 + 3 ^ 40 * 1921490 * 2
def baseEnd_1921490 : Nat := 986647942807792395238235

theorem tailTrace_1921490 : CollatzResearch.WordTrace tailWord_1921490 prefixEnd_1921490 986647942807792395238235 := by
  unfold tailWord_1921490
  simp only [CollatzResearch.WordTrace]
  refine ⟨17520624452194342302652481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46721665205851579473739949 17520624452194342302652481)
  ·
    refine ⟨13140468339145756726989361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17520624452194342302652481 13140468339145756726989361)
    ·
      refine ⟨9855351254359317545242021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13140468339145756726989361 9855351254359317545242021)
      ·
        refine ⟨1847878360192372039732879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9855351254359317545242021 1847878360192372039732879)
        ·
          refine ⟨2771817540288558059599319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1847878360192372039732879 2771817540288558059599319)
          ·
            refine ⟨4157726310432837089398979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2771817540288558059599319 4157726310432837089398979)
            ·
              refine ⟨6236589465649255634098469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4157726310432837089398979 6236589465649255634098469)
              ·
                refine ⟨1169360524809235431393463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6236589465649255634098469 1169360524809235431393463)
                ·
                  refine ⟨1754040787213853147090195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1169360524809235431393463 1754040787213853147090195)
                  ·
                    refine ⟨2631061180820779720635293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1754040787213853147090195 2631061180820779720635293)
                    ·
                      refine ⟨986647942807792395238235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2631061180820779720635293 986647942807792395238235)
                      ·
                        rfl

theorem cell23_1921490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_1921490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921490 prefixEnd_1921490 := by exact prefixLift 1921490
  have htrace : WordTrace (prefixWord ++ tailWord_1921490) baseStart_1921490 baseEnd_1921490 := by
    simpa [prefixWord, tailWord_1921490, baseEnd_1921490] using wordTrace_append hprefix tailTrace_1921490
  have hstable : (prefixWord ++ tailWord_1921490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921490).length < 2 ^ (prefixWord ++ tailWord_1921490).sum := by decide
  have hdescent : baseEnd_1921490 < baseStart_1921490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921515 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 2, 7]
def baseStart_1921515 : Nat := 118140960795 + 1921515 * 2 ^ 59
def prefixEnd_1921515 : Nat := 4983230072969 + 3 ^ 40 * 1921515 * 2
def baseEnd_1921515 : Nat := 328886926608051599141873

theorem tailTrace_1921515 : CollatzResearch.WordTrace tailWord_1921515 prefixEnd_1921515 328886926608051599141873 := by
  unfold tailWord_1921515
  simp only [CollatzResearch.WordTrace]
  refine ⟨70083409633686798480269999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46722273089124532320179999 70083409633686798480269999)
  ·
    refine ⟨105125114450530197720404999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70083409633686798480269999 105125114450530197720404999)
    ·
      refine ⟨157687671675795296580607499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105125114450530197720404999 157687671675795296580607499)
      ·
        refine ⟨236531507513692944870911249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157687671675795296580607499 236531507513692944870911249)
        ·
          refine ⟨177398630635269708653183437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236531507513692944870911249 177398630635269708653183437)
          ·
            refine ⟨66524486488226140744943789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177398630635269708653183437 66524486488226140744943789)
            ·
              refine ⟨24946682433084802779353921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66524486488226140744943789 24946682433084802779353921)
              ·
                refine ⟨18710011824813602084515441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24946682433084802779353921 18710011824813602084515441)
                ·
                  refine ⟨14032508868610201563386581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18710011824813602084515441 14032508868610201563386581)
                  ·
                    refine ⟨328886926608051599141873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14032508868610201563386581 328886926608051599141873)
                    ·
                      rfl

theorem cell23_1921515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 7].length) (baseStart_1921515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921515 prefixEnd_1921515 := by exact prefixLift 1921515
  have htrace : WordTrace (prefixWord ++ tailWord_1921515) baseStart_1921515 baseEnd_1921515 := by
    simpa [prefixWord, tailWord_1921515, baseEnd_1921515] using wordTrace_append hprefix tailTrace_1921515
  have hstable : (prefixWord ++ tailWord_1921515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921515).length < 2 ^ (prefixWord ++ tailWord_1921515).sum := by decide
  have hdescent : baseEnd_1921515 < baseStart_1921515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921562 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 2, 6]
def baseStart_1921562 : Nat := 118140960795 + 1921562 * 2 ^ 59
def prefixEnd_1921562 : Nat := 4983230072969 + 3 ^ 40 * 1921562 * 2
def baseEnd_1921562 : Nat := 328894971138305371179301

theorem tailTrace_1921562 : CollatzResearch.WordTrace tailWord_1921562 prefixEnd_1921562 328894971138305371179301 := by
  unfold tailWord_1921562
  simp only [CollatzResearch.WordTrace]
  refine ⟨17521280966129131376807735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46723415909677683671487293 17521280966129131376807735)
  ·
    refine ⟨26281921449193697065211603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17521280966129131376807735 26281921449193697065211603)
    ·
      refine ⟨39422882173790545597817405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26281921449193697065211603 39422882173790545597817405)
      ·
        refine ⟨14783580815171454599181527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39422882173790545597817405 14783580815171454599181527)
        ·
          refine ⟨22175371222757181898772291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14783580815171454599181527 22175371222757181898772291)
          ·
            refine ⟨33263056834135772848158437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22175371222757181898772291 33263056834135772848158437)
            ·
              refine ⟨6236823156400457409029707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33263056834135772848158437 6236823156400457409029707)
              ·
                refine ⟨9355234734600686113544561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6236823156400457409029707 9355234734600686113544561)
                ·
                  refine ⟨7016426050950514585158421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9355234734600686113544561 7016426050950514585158421)
                  ·
                    refine ⟨328894971138305371179301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7016426050950514585158421 328894971138305371179301)
                    ·
                      rfl

theorem cell23_1921562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_1921562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921562 prefixEnd_1921562 := by exact prefixLift 1921562
  have htrace : WordTrace (prefixWord ++ tailWord_1921562) baseStart_1921562 baseEnd_1921562 := by
    simpa [prefixWord, tailWord_1921562, baseEnd_1921562] using wordTrace_append hprefix tailTrace_1921562
  have hstable : (prefixWord ++ tailWord_1921562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921562).length < 2 ^ (prefixWord ++ tailWord_1921562).sum := by decide
  have hdescent : baseEnd_1921562 < baseStart_1921562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921581 : List Nat := [1, 5, 4, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_1921581 : Nat := 118140960795 + 1921581 * 2 ^ 59
def prefixEnd_1921581 : Nat := 4983230072969 + 3 ^ 40 * 1921581 * 2
def baseEnd_1921581 : Nat := 986694669547351539200317

theorem tailTrace_1921581 : CollatzResearch.WordTrace tailWord_1921581 prefixEnd_1921581 986694669547351539200317 := by
  unfold tailWord_1921581
  simp only [CollatzResearch.WordTrace]
  refine ⟨70085816851447691752172597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46723877900965127834781731 70085816851447691752172597)
  ·
    refine ⟨6570545329823221101766181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70085816851447691752172597 6570545329823221101766181)
    ·
      refine ⟨1231977249341853956581159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6570545329823221101766181 1231977249341853956581159)
      ·
        refine ⟨1847965874012780934871739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1231977249341853956581159 1847965874012780934871739)
        ·
          refine ⟨2771948811019171402307609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1847965874012780934871739 2771948811019171402307609)
          ·
            refine ⟨2078961608264378551730707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2771948811019171402307609 2078961608264378551730707)
            ·
              refine ⟨3118442412396567827596061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2078961608264378551730707 3118442412396567827596061)
              ·
                refine ⟨1169415904648712935348523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3118442412396567827596061 1169415904648712935348523)
                ·
                  refine ⟨1754123856973069403022785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1169415904648712935348523 1754123856973069403022785)
                  ·
                    refine ⟨1315592892729802052267089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1754123856973069403022785 1315592892729802052267089)
                    ·
                      refine ⟨986694669547351539200317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1315592892729802052267089 986694669547351539200317)
                      ·
                        rfl

theorem cell23_1921581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_1921581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921581 prefixEnd_1921581 := by exact prefixLift 1921581
  have htrace : WordTrace (prefixWord ++ tailWord_1921581) baseStart_1921581 baseEnd_1921581 := by
    simpa [prefixWord, tailWord_1921581, baseEnd_1921581] using wordTrace_append hprefix tailTrace_1921581
  have hstable : (prefixWord ++ tailWord_1921581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921581).length < 2 ^ (prefixWord ++ tailWord_1921581).sum := by decide
  have hdescent : baseEnd_1921581 < baseStart_1921581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921586 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2]
def baseStart_1921586 : Nat := 118140960795 + 1921586 * 2 ^ 59
def prefixEnd_1921586 : Nat := 4983230072969 + 3 ^ 40 * 1921586 * 2
def baseEnd_1921586 : Nat := 986697236950624019637793

theorem tailTrace_1921586 : CollatzResearch.WordTrace tailWord_1921586 prefixEnd_1921586 986697236950624019637793 := by
  unfold tailWord_1921586
  simp only [CollatzResearch.WordTrace]
  refine ⟨17521499804107394401526153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46723999477619718404069741 17521499804107394401526153)
  ·
    refine ⟨13141124853080545801144615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17521499804107394401526153 13141124853080545801144615)
    ·
      refine ⟨19711687279620818701716923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13141124853080545801144615 19711687279620818701716923)
      ·
        refine ⟨29567530919431228052575385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19711687279620818701716923 29567530919431228052575385)
        ·
          refine ⟨22175648189573421039431539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29567530919431228052575385 22175648189573421039431539)
          ·
            refine ⟨33263472284360131559147309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22175648189573421039431539 33263472284360131559147309)
            ·
              refine ⟨12473802106635049334680241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33263472284360131559147309 12473802106635049334680241)
              ·
                refine ⟨9355351579976287001010181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12473802106635049334680241 9355351579976287001010181)
                ·
                  refine ⟨1754128421245553812689409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9355351579976287001010181 1754128421245553812689409)
                  ·
                    refine ⟨1315596315934165359517057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1754128421245553812689409 1315596315934165359517057)
                    ·
                      refine ⟨986697236950624019637793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1315596315934165359517057 986697236950624019637793)
                      ·
                        rfl

theorem cell23_1921586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_1921586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921586 prefixEnd_1921586 := by exact prefixLift 1921586
  have htrace : WordTrace (prefixWord ++ tailWord_1921586) baseStart_1921586 baseEnd_1921586 := by
    simpa [prefixWord, tailWord_1921586, baseEnd_1921586] using wordTrace_append hprefix tailTrace_1921586
  have hstable : (prefixWord ++ tailWord_1921586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921586).length < 2 ^ (prefixWord ++ tailWord_1921586).sum := by decide
  have hdescent : baseEnd_1921586 < baseStart_1921586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921620 : List Nat := [2, 4, 1, 1, 1, 3, 4, 1, 2, 2, 2]
def baseStart_1921620 : Nat := 118140960795 + 1921620 * 2 ^ 59
def prefixEnd_1921620 : Nat := 4983230072969 + 3 ^ 40 * 1921620 * 2
def baseEnd_1921620 : Nat := 986714695292876886612637

theorem tailTrace_1921620 : CollatzResearch.WordTrace tailWord_1921620 prefixEnd_1921620 986714695292876886612637 := by
  unfold tailWord_1921620
  simp only [CollatzResearch.WordTrace]
  refine ⟨35043619649153200706421157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46724826198870934275228209 35043619649153200706421157)
  ·
    refine ⟨6570678684216225132453967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35043619649153200706421157 6570678684216225132453967)
    ·
      refine ⟨9856018026324337698680951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6570678684216225132453967 9856018026324337698680951)
      ·
        refine ⟨14784027039486506548021427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9856018026324337698680951 14784027039486506548021427)
        ·
          refine ⟨22176040559229759822032141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14784027039486506548021427 22176040559229759822032141)
          ·
            refine ⟨8316015209711159933262053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22176040559229759822032141 8316015209711159933262053)
            ·
              refine ⟨1559252851820842487486635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8316015209711159933262053 1559252851820842487486635)
              ·
                refine ⟨2338879277731263731229953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1559252851820842487486635 2338879277731263731229953)
                ·
                  refine ⟨1754159458298447798422465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2338879277731263731229953 1754159458298447798422465)
                  ·
                    refine ⟨1315619593723835848816849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1754159458298447798422465 1315619593723835848816849)
                    ·
                      refine ⟨986714695292876886612637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1315619593723835848816849 986714695292876886612637)
                      ·
                        rfl

theorem cell23_1921620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 2, 2, 2].length) (baseStart_1921620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921620 prefixEnd_1921620 := by exact prefixLift 1921620
  have htrace : WordTrace (prefixWord ++ tailWord_1921620) baseStart_1921620 baseEnd_1921620 := by
    simpa [prefixWord, tailWord_1921620, baseEnd_1921620] using wordTrace_append hprefix tailTrace_1921620
  have hstable : (prefixWord ++ tailWord_1921620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921620).length < 2 ^ (prefixWord ++ tailWord_1921620).sum := by decide
  have hdescent : baseEnd_1921620 < baseStart_1921620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921690 : List Nat := [3, 1, 1, 6, 2, 1, 1, 1, 2, 5]
def baseStart_1921690 : Nat := 118140960795 + 1921690 * 2 ^ 59
def prefixEnd_1921690 : Nat := 4983230072969 + 3 ^ 40 * 1921690 * 2
def baseEnd_1921690 : Nat := 328916879646230537579105

theorem tailTrace_1921690 : CollatzResearch.WordTrace tailWord_1921690 prefixEnd_1921690 328916879646230537579105 := by
  unfold tailWord_1921690
  simp only [CollatzResearch.WordTrace]
  refine ⟨17522448102013200841972631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46726528272035202245260349 17522448102013200841972631)
  ·
    refine ⟨26283672153019801262958947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17522448102013200841972631 26283672153019801262958947)
    ·
      refine ⟨39425508229529701894438421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26283672153019801262958947 39425508229529701894438421)
      ·
        refine ⟨1848070698259204776301801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 39425508229529701894438421 1848070698259204776301801)
        ·
          refine ⟨1386053023694403582226351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1848070698259204776301801 1386053023694403582226351)
          ·
            refine ⟨2079079535541605373339527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1386053023694403582226351 2079079535541605373339527)
            ·
              refine ⟨3118619303312408060009291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2079079535541605373339527 3118619303312408060009291)
              ·
                refine ⟨4677928954968612090013937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3118619303312408060009291 4677928954968612090013937)
                ·
                  refine ⟨3508446716226459067510453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4677928954968612090013937 3508446716226459067510453)
                  ·
                    refine ⟨328916879646230537579105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3508446716226459067510453 328916879646230537579105)
                    ·
                      rfl

theorem cell23_1921690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 2, 5].length) (baseStart_1921690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921690 prefixEnd_1921690 := by exact prefixLift 1921690
  have htrace : WordTrace (prefixWord ++ tailWord_1921690) baseStart_1921690 baseEnd_1921690 := by
    simpa [prefixWord, tailWord_1921690, baseEnd_1921690] using wordTrace_append hprefix tailTrace_1921690
  have hstable : (prefixWord ++ tailWord_1921690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921690).length < 2 ^ (prefixWord ++ tailWord_1921690).sum := by decide
  have hdescent : baseEnd_1921690 < baseStart_1921690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921696 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 3]
def baseStart_1921696 : Nat := 118140960795 + 1921696 * 2 ^ 59
def prefixEnd_1921696 : Nat := 4983230072969 + 3 ^ 40 * 1921696 * 2
def baseEnd_1921696 : Nat := 986753719822618589262287

theorem tailTrace_1921696 : CollatzResearch.WordTrace tailWord_1921696 prefixEnd_1921696 986753719822618589262287 := by
  unfold tailWord_1921696
  simp only [CollatzResearch.WordTrace]
  refine ⟨35045005623015533196304471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46726674164020710928405961 35045005623015533196304471)
  ·
    refine ⟨52567508434523299794456707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35045005623015533196304471 52567508434523299794456707)
    ·
      refine ⟨78851262651784949691685061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52567508434523299794456707 78851262651784949691685061)
      ·
        refine ⟨14784611747209678067190949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78851262651784949691685061 14784611747209678067190949)
        ·
          refine ⟨2772114702601814637598303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14784611747209678067190949 2772114702601814637598303)
          ·
            refine ⟨4158172053902721956397455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2772114702601814637598303 4158172053902721956397455)
            ·
              refine ⟨6237258080854082934596183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4158172053902721956397455 6237258080854082934596183)
              ·
                refine ⟨9355887121281124401894275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6237258080854082934596183 9355887121281124401894275)
                ·
                  refine ⟨14033830681921686602841413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9355887121281124401894275 14033830681921686602841413)
                  ·
                    refine ⟨2631343252860316238032765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14033830681921686602841413 2631343252860316238032765)
                    ·
                      refine ⟨986753719822618589262287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2631343252860316238032765 986753719822618589262287)
                      ·
                        rfl

theorem cell23_1921696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_1921696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921696 prefixEnd_1921696 := by exact prefixLift 1921696
  have htrace : WordTrace (prefixWord ++ tailWord_1921696) baseStart_1921696 baseEnd_1921696 := by
    simpa [prefixWord, tailWord_1921696, baseEnd_1921696] using wordTrace_append hprefix tailTrace_1921696
  have hstable : (prefixWord ++ tailWord_1921696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921696).length < 2 ^ (prefixWord ++ tailWord_1921696).sum := by decide
  have hdescent : baseEnd_1921696 < baseStart_1921696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921736 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 1, 5, 2]
def baseStart_1921736 : Nat := 118140960795 + 1921736 * 2 ^ 59
def prefixEnd_1921736 : Nat := 4983230072969 + 3 ^ 40 * 1921736 * 2
def baseEnd_1921736 : Nat := 986774259048798432762103

theorem tailTrace_1921736 : CollatzResearch.WordTrace tailWord_1921736 prefixEnd_1921736 986774259048798432762103 := by
  unfold tailWord_1921736
  simp only [CollatzResearch.WordTrace]
  refine ⟨35045735082943076612032531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46727646777257435482710041 35045735082943076612032531)
  ·
    refine ⟨52568602624414614918048797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35045735082943076612032531 52568602624414614918048797)
    ·
      refine ⟨19713225984155480594268299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52568602624414614918048797 19713225984155480594268299)
      ·
        refine ⟨29569838976233220891402449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19713225984155480594268299 29569838976233220891402449)
        ·
          refine ⟨22177379232174915668551837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29569838976233220891402449 22177379232174915668551837)
          ·
            refine ⟨8316517212065593375706939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22177379232174915668551837 8316517212065593375706939)
            ·
              refine ⟨12474775818098390063560409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8316517212065593375706939 12474775818098390063560409)
              ·
                refine ⟨9356081863573792547670307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12474775818098390063560409 9356081863573792547670307)
                ·
                  refine ⟨14034122795360688821505461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9356081863573792547670307 14034122795360688821505461)
                  ·
                    refine ⟨1315699012065064577016137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14034122795360688821505461 1315699012065064577016137)
                    ·
                      refine ⟨986774259048798432762103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1315699012065064577016137 986774259048798432762103)
                      ·
                        rfl

theorem cell23_1921736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_1921736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921736 prefixEnd_1921736 := by exact prefixLift 1921736
  have htrace : WordTrace (prefixWord ++ tailWord_1921736) baseStart_1921736 baseEnd_1921736 := by
    simpa [prefixWord, tailWord_1921736, baseEnd_1921736] using wordTrace_append hprefix tailTrace_1921736
  have hstable : (prefixWord ++ tailWord_1921736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921736).length < 2 ^ (prefixWord ++ tailWord_1921736).sum := by decide
  have hdescent : baseEnd_1921736 < baseStart_1921736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921769 : List Nat := [1, 2, 1, 1, 1, 2, 5, 3, 1, 1, 5]
def baseStart_1921769 : Nat := 118140960795 + 1921769 * 2 ^ 59
def prefixEnd_1921769 : Nat := 4983230072969 + 3 ^ 40 * 1921769 * 2
def baseEnd_1921769 : Nat := 986791203910396803649451

theorem tailTrace_1921769 : CollatzResearch.WordTrace tailWord_1921769 prefixEnd_1921769 986791203910396803649451 := by
  unfold tailWord_1921769
  simp only [CollatzResearch.WordTrace]
  refine ⟨70092673774766599860016361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46728449183177733240010907 70092673774766599860016361)
  ·
    refine ⟨52569505331074949895012271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70092673774766599860016361 52569505331074949895012271)
    ·
      refine ⟨78854257996612424842518407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52569505331074949895012271 78854257996612424842518407)
      ·
        refine ⟨118281386994918637263777611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78854257996612424842518407 118281386994918637263777611)
        ·
          refine ⟨177422080492377955895666417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118281386994918637263777611 177422080492377955895666417)
          ·
            refine ⟨133066560369283466921749813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177422080492377955895666417 133066560369283466921749813)
            ·
              refine ⟨12474990034620325023914045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133066560369283466921749813 12474990034620325023914045)
              ·
                refine ⟨4678121262982621883967767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12474990034620325023914045 4678121262982621883967767)
                ·
                  refine ⟨7017181894473932825951651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4678121262982621883967767 7017181894473932825951651)
                  ·
                    refine ⟨10525772841710899238927477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7017181894473932825951651 10525772841710899238927477)
                    ·
                      refine ⟨986791203910396803649451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10525772841710899238927477 986791203910396803649451)
                      ·
                        rfl

theorem cell23_1921769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 1, 5].length) (baseStart_1921769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921769 prefixEnd_1921769 := by exact prefixLift 1921769
  have htrace : WordTrace (prefixWord ++ tailWord_1921769) baseStart_1921769 baseEnd_1921769 := by
    simpa [prefixWord, tailWord_1921769, baseEnd_1921769] using wordTrace_append hprefix tailTrace_1921769
  have hstable : (prefixWord ++ tailWord_1921769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921769).length < 2 ^ (prefixWord ++ tailWord_1921769).sum := by decide
  have hdescent : baseEnd_1921769 < baseStart_1921769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921776 : List Nat := [2, 1, 1, 1, 3, 1, 4, 4, 2, 4]
def baseStart_1921776 : Nat := 118140960795 + 1921776 * 2 ^ 59
def prefixEnd_1921776 : Nat := 4983230072969 + 3 ^ 40 * 1921776 * 2
def baseEnd_1921776 : Nat := 328931599424992758753973

theorem tailTrace_1921776 : CollatzResearch.WordTrace tailWord_1921776 prefixEnd_1921776 328931599424992758753973 := by
  unfold tailWord_1921776
  simp only [CollatzResearch.WordTrace]
  refine ⟨35046464542870620027760591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46728619390494160037014121 35046464542870620027760591)
  ·
    refine ⟨52569696814305930041640887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35046464542870620027760591 52569696814305930041640887)
    ·
      refine ⟨78854545221458895062461331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52569696814305930041640887 78854545221458895062461331)
      ·
        refine ⟨118281817832188342593691997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78854545221458895062461331 118281817832188342593691997)
        ·
          refine ⟨44355681687070628472634499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118281817832188342593691997 44355681687070628472634499)
          ·
            refine ⟨66533522530605942708951749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44355681687070628472634499 66533522530605942708951749)
            ·
              refine ⟨12475035474488614257928453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66533522530605942708951749 12475035474488614257928453)
              ·
                refine ⟨2339069151466615173361585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12475035474488614257928453 2339069151466615173361585)
                ·
                  refine ⟨1754301863599961380021189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2339069151466615173361585 1754301863599961380021189)
                  ·
                    refine ⟨328931599424992758753973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1754301863599961380021189 328931599424992758753973)
                    ·
                      rfl

theorem cell23_1921776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 2, 4].length) (baseStart_1921776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921776 prefixEnd_1921776 := by exact prefixLift 1921776
  have htrace : WordTrace (prefixWord ++ tailWord_1921776) baseStart_1921776 baseEnd_1921776 := by
    simpa [prefixWord, tailWord_1921776, baseEnd_1921776] using wordTrace_append hprefix tailTrace_1921776
  have hstable : (prefixWord ++ tailWord_1921776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921776).length < 2 ^ (prefixWord ++ tailWord_1921776).sum := by decide
  have hdescent : baseEnd_1921776 < baseStart_1921776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921789 : List Nat := [1, 4, 1, 1, 1, 1, 6, 8]
def baseStart_1921789 : Nat := 118140960795 + 1921789 * 2 ^ 59
def prefixEnd_1921789 : Nat := 4983230072969 + 3 ^ 40 * 1921789 * 2
def baseEnd_1921789 : Nat := 36548202723092100940717

theorem tailTrace_1921789 : CollatzResearch.WordTrace tailWord_1921789 prefixEnd_1921789 36548202723092100940717 := by
  unfold tailWord_1921789
  simp only [CollatzResearch.WordTrace]
  refine ⟨70093403234694143275744421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46728935489796095517162947 70093403234694143275744421)
  ·
    refine ⟨13142513106505151864202079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70093403234694143275744421 13142513106505151864202079)
    ·
      refine ⟨19713769659757727796303119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13142513106505151864202079 19713769659757727796303119)
      ·
        refine ⟨29570654489636591694454679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19713769659757727796303119 29570654489636591694454679)
        ·
          refine ⟨44355981734454887541682019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29570654489636591694454679 44355981734454887541682019)
          ·
            refine ⟨66533972601682331312523029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44355981734454887541682019 66533972601682331312523029)
            ·
              refine ⟨3118779965703859280274517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 66533972601682331312523029 3118779965703859280274517)
              ·
                refine ⟨36548202723092100940717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3118779965703859280274517 36548202723092100940717)
                ·
                  rfl

theorem cell23_1921789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 8].length) (baseStart_1921789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921789 prefixEnd_1921789 := by exact prefixLift 1921789
  have htrace : WordTrace (prefixWord ++ tailWord_1921789) baseStart_1921789 baseEnd_1921789 := by
    simpa [prefixWord, tailWord_1921789, baseEnd_1921789] using wordTrace_append hprefix tailTrace_1921789
  have hstable : (prefixWord ++ tailWord_1921789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921789).length < 2 ^ (prefixWord ++ tailWord_1921789).sum := by decide
  have hdescent : baseEnd_1921789 < baseStart_1921789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921796 : List Nat := [2, 3, 2, 2, 1, 1, 2, 3, 1, 2, 4]
def baseStart_1921796 : Nat := 118140960795 + 1921796 * 2 ^ 59
def prefixEnd_1921796 : Nat := 4983230072969 + 3 ^ 40 * 1921796 * 2
def baseEnd_1921796 : Nat := 986805067888068198011827

theorem tailTrace_1921796 : CollatzResearch.WordTrace tailWord_1921796 prefixEnd_1921796 986805067888068198011827 := by
  unfold tailWord_1921796
  simp only [CollatzResearch.WordTrace]
  refine ⟨35046829272834391735624621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46729105697112522314166161 35046829272834391735624621)
  ·
    refine ⟨13142560977312896900859233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35046829272834391735624621 13142560977312896900859233)
    ·
      refine ⟨9856920732984672675644425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13142560977312896900859233 9856920732984672675644425)
      ·
        refine ⟨7392690549738504506733319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9856920732984672675644425 7392690549738504506733319)
        ·
          refine ⟨11089035824607756760099979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7392690549738504506733319 11089035824607756760099979)
          ·
            refine ⟨16633553736911635140149969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11089035824607756760099979 16633553736911635140149969)
            ·
              refine ⟨12475165302683726355112477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16633553736911635140149969 12475165302683726355112477)
              ·
                refine ⟨4678186988506397383167179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12475165302683726355112477 4678186988506397383167179)
                ·
                  refine ⟨7017280482759596074750769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4678186988506397383167179 7017280482759596074750769)
                  ·
                    refine ⟨5262960362069697056063077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7017280482759596074750769 5262960362069697056063077)
                    ·
                      refine ⟨986805067888068198011827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5262960362069697056063077 986805067888068198011827)
                      ·
                        rfl

theorem cell23_1921796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_1921796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921796 prefixEnd_1921796 := by exact prefixLift 1921796
  have htrace : WordTrace (prefixWord ++ tailWord_1921796) baseStart_1921796 baseEnd_1921796 := by
    simpa [prefixWord, tailWord_1921796, baseEnd_1921796] using wordTrace_append hprefix tailTrace_1921796
  have hstable : (prefixWord ++ tailWord_1921796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921796).length < 2 ^ (prefixWord ++ tailWord_1921796).sum := by decide
  have hdescent : baseEnd_1921796 < baseStart_1921796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921820 : List Nat := [2, 2, 3, 1, 1, 4, 3, 1, 1, 2, 3]
def baseStart_1921820 : Nat := 118140960795 + 1921820 * 2 ^ 59
def prefixEnd_1921820 : Nat := 4983230072969 + 3 ^ 40 * 1921820 * 2
def baseEnd_1921820 : Nat := 986817391423776104111717

theorem tailTrace_1921820 : CollatzResearch.WordTrace tailWord_1921820 prefixEnd_1921820 986817391423776104111717 := by
  unfold tailWord_1921820
  simp only [CollatzResearch.WordTrace]
  refine ⟨35047266948790917785061457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46729689265054557046748609 35047266948790917785061457)
  ·
    refine ⟨26285450211593188338796093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35047266948790917785061457 26285450211593188338796093)
    ·
      refine ⟨9857043829347445627048535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26285450211593188338796093 9857043829347445627048535)
      ·
        refine ⟨14785565744021168440572803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9857043829347445627048535 14785565744021168440572803)
        ·
          refine ⟨22178348616031752660859205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14785565744021168440572803 22178348616031752660859205)
          ·
            refine ⟨4158440365505953623911101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22178348616031752660859205 4158440365505953623911101)
            ·
              refine ⟨1559415137064732608966663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4158440365505953623911101 1559415137064732608966663)
              ·
                refine ⟨2339122705597098913449995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1559415137064732608966663 2339122705597098913449995)
                ·
                  refine ⟨3508684058395648370174993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2339122705597098913449995 3508684058395648370174993)
                  ·
                    refine ⟨2631513043796736277631245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3508684058395648370174993 2631513043796736277631245)
                    ·
                      refine ⟨986817391423776104111717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2631513043796736277631245 986817391423776104111717)
                      ·
                        rfl

theorem cell23_1921820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_1921820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921820 prefixEnd_1921820 := by exact prefixLift 1921820
  have htrace : WordTrace (prefixWord ++ tailWord_1921820) baseStart_1921820 baseEnd_1921820 := by
    simpa [prefixWord, tailWord_1921820, baseEnd_1921820] using wordTrace_append hprefix tailTrace_1921820
  have hstable : (prefixWord ++ tailWord_1921820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921820).length < 2 ^ (prefixWord ++ tailWord_1921820).sum := by decide
  have hdescent : baseEnd_1921820 < baseStart_1921820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921843 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 3, 3, 2]
def baseStart_1921843 : Nat := 118140960795 + 1921843 * 2 ^ 59
def prefixEnd_1921843 : Nat := 4983230072969 + 3 ^ 40 * 1921843 * 2
def baseEnd_1921843 : Nat := 986829201478829514124111

theorem tailTrace_1921843 : CollatzResearch.WordTrace tailWord_1921843 prefixEnd_1921843 986829201478829514124111 := by
  unfold tailWord_1921843
  simp only [CollatzResearch.WordTrace]
  refine ⟨70095372776498510498210183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46730248517665673665473455 70095372776498510498210183)
  ·
    refine ⟨105143059164747765747315275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70095372776498510498210183 105143059164747765747315275)
    ·
      refine ⟨157714588747121648620972913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105143059164747765747315275 157714588747121648620972913)
      ·
        refine ⟨118285941560341236465729685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157714588747121648620972913 118285941560341236465729685)
        ·
          refine ⟨5544653510640995459331079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118285941560341236465729685 5544653510640995459331079)
          ·
            refine ⟨8316980265961493188996619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5544653510640995459331079 8316980265961493188996619)
            ·
              refine ⟨12475470398942239783494929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8316980265961493188996619 12475470398942239783494929)
              ·
                refine ⟨9356602799206679837621197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12475470398942239783494929 9356602799206679837621197)
                ·
                  refine ⟨3508726049702504939107949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9356602799206679837621197 3508726049702504939107949)
                  ·
                    refine ⟨1315772268638439352165481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3508726049702504939107949 1315772268638439352165481)
                    ·
                      refine ⟨986829201478829514124111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1315772268638439352165481 986829201478829514124111)
                      ·
                        rfl

theorem cell23_1921843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 3, 2].length) (baseStart_1921843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921843 prefixEnd_1921843 := by exact prefixLift 1921843
  have htrace : WordTrace (prefixWord ++ tailWord_1921843) baseStart_1921843 baseEnd_1921843 := by
    simpa [prefixWord, tailWord_1921843, baseEnd_1921843] using wordTrace_append hprefix tailTrace_1921843
  have hstable : (prefixWord ++ tailWord_1921843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921843).length < 2 ^ (prefixWord ++ tailWord_1921843).sum := by decide
  have hdescent : baseEnd_1921843 < baseStart_1921843 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921889 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 9]
def baseStart_1921889 : Nat := 118140960795 + 1921889 * 2 ^ 59
def prefixEnd_1921889 : Nat := 4983230072969 + 3 ^ 40 * 1921889 * 2
def baseEnd_1921889 : Nat := 986852821588936334148899

theorem tailTrace_1921889 : CollatzResearch.WordTrace tailWord_1921889 prefixEnd_1921889 986852821588936334148899 := by
  unfold tailWord_1921889
  simp only [CollatzResearch.WordTrace]
  refine ⟨70097050534331860354384721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46731367022887906902923147 70097050534331860354384721)
  ·
    refine ⟨52572787900748895265788541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70097050534331860354384721 52572787900748895265788541)
    ·
      refine ⟨19714795462780835724670703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52572787900748895265788541 19714795462780835724670703)
      ·
        refine ⟨29572193194171253587006055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19714795462780835724670703 29572193194171253587006055)
        ·
          refine ⟨44358289791256880380509083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29572193194171253587006055 44358289791256880380509083)
          ·
            refine ⟨66537434686885320570763625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44358289791256880380509083 66537434686885320570763625)
            ·
              refine ⟨49903076015163990428072719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66537434686885320570763625 49903076015163990428072719)
              ·
                refine ⟨74854614022745985642109079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49903076015163990428072719 74854614022745985642109079)
                ·
                  refine ⟨112281921034118978463163619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74854614022745985642109079 112281921034118978463163619)
                  ·
                    refine ⟨168422881551178467694745429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112281921034118978463163619 168422881551178467694745429)
                    ·
                      refine ⟨986852821588936334148899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 168422881551178467694745429 986852821588936334148899)
                      ·
                        rfl

theorem cell23_1921889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_1921889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921889 prefixEnd_1921889 := by exact prefixLift 1921889
  have htrace : WordTrace (prefixWord ++ tailWord_1921889) baseStart_1921889 baseEnd_1921889 := by
    simpa [prefixWord, tailWord_1921889, baseEnd_1921889] using wordTrace_append hprefix tailTrace_1921889
  have hstable : (prefixWord ++ tailWord_1921889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921889).length < 2 ^ (prefixWord ++ tailWord_1921889).sum := by decide
  have hdescent : baseEnd_1921889 < baseStart_1921889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921896 : List Nat := [2, 1, 4, 2, 1, 2, 1, 3, 7]
def baseStart_1921896 : Nat := 118140960795 + 1921896 * 2 ^ 59
def prefixEnd_1921896 : Nat := 4983230072969 + 3 ^ 40 * 1921896 * 2
def baseEnd_1921896 : Nat := 109650712883724200751263

theorem tailTrace_1921896 : CollatzResearch.WordTrace tailWord_1921896 prefixEnd_1921896 109650712883724200751263 := by
  unfold tailWord_1921896
  simp only [CollatzResearch.WordTrace]
  refine ⟨35048652922653250274944771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 46731537230204333699926361 35048652922653250274944771)
  ·
    refine ⟨52572979383979875412417157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35048652922653250274944771 52572979383979875412417157)
    ·
      refine ⟨9857433634496226639828217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52572979383979875412417157 9857433634496226639828217)
      ·
        refine ⟨7393075225872169979871163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9857433634496226639828217 7393075225872169979871163)
        ·
          refine ⟨11089612838808254969806745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7393075225872169979871163 11089612838808254969806745)
          ·
            refine ⟨8317209629106191227355059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11089612838808254969806745 8317209629106191227355059)
            ·
              refine ⟨12475814443659286841032589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8317209629106191227355059 12475814443659286841032589)
              ·
                refine ⟨4678430416372232565387221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12475814443659286841032589 4678430416372232565387221)
                ·
                  refine ⟨109650712883724200751263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4678430416372232565387221 109650712883724200751263)
                  ·
                    rfl

theorem cell23_1921896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 7].length) (baseStart_1921896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921896 prefixEnd_1921896 := by exact prefixLift 1921896
  have htrace : WordTrace (prefixWord ++ tailWord_1921896) baseStart_1921896 baseEnd_1921896 := by
    simpa [prefixWord, tailWord_1921896, baseEnd_1921896] using wordTrace_append hprefix tailTrace_1921896
  have hstable : (prefixWord ++ tailWord_1921896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921896).length < 2 ^ (prefixWord ++ tailWord_1921896).sum := by decide
  have hdescent : baseEnd_1921896 < baseStart_1921896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921930 : List Nat := [3, 1, 2, 4, 1, 1, 3, 3, 5]
def baseStart_1921930 : Nat := 118140960795 + 1921930 * 2 ^ 59
def prefixEnd_1921930 : Nat := 4983230072969 + 3 ^ 40 * 1921930 * 2
def baseEnd_1921930 : Nat := 109652652699530074859579

theorem tailTrace_1921930 : CollatzResearch.WordTrace tailWord_1921930 prefixEnd_1921930 109652652699530074859579 := by
  unfold tailWord_1921930
  simp only [CollatzResearch.WordTrace]
  refine ⟨17524636481795831089156811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 46732363951455549571084829 17524636481795831089156811)
  ·
    refine ⟨26286954722693746633735217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17524636481795831089156811 26286954722693746633735217)
    ·
      refine ⟨19715216042020309975301413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26286954722693746633735217 19715216042020309975301413)
      ·
        refine ⟨3696603007878808120369015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19715216042020309975301413 3696603007878808120369015)
        ·
          refine ⟨5544904511818212180553523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3696603007878808120369015 5544904511818212180553523)
          ·
            refine ⟨8317356767727318270830285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5544904511818212180553523 8317356767727318270830285)
            ·
              refine ⟨3119008787897744351561357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8317356767727318270830285 3119008787897744351561357)
              ·
                refine ⟨1169628295461654131835509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3119008787897744351561357 1169628295461654131835509)
                ·
                  refine ⟨109652652699530074859579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1169628295461654131835509 109652652699530074859579)
                  ·
                    rfl

theorem cell23_1921930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 5].length) (baseStart_1921930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921930 prefixEnd_1921930 := by exact prefixLift 1921930
  have htrace : WordTrace (prefixWord ++ tailWord_1921930) baseStart_1921930 baseEnd_1921930 := by
    simpa [prefixWord, tailWord_1921930, baseEnd_1921930] using wordTrace_append hprefix tailTrace_1921930
  have hstable : (prefixWord ++ tailWord_1921930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921930).length < 2 ^ (prefixWord ++ tailWord_1921930).sum := by decide
  have hdescent : baseEnd_1921930 < baseStart_1921930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921953 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1921953 : Nat := 118140960795 + 1921953 * 2 ^ 59
def prefixEnd_1921953 : Nat := 4983230072969 + 3 ^ 40 * 1921953 * 2
def baseEnd_1921953 : Nat := 986885684350824083748605

theorem tailTrace_1921953 : CollatzResearch.WordTrace tailWord_1921953 prefixEnd_1921953 986885684350824083748605 := by
  unfold tailWord_1921953
  simp only [CollatzResearch.WordTrace]
  refine ⟨70099384806099999284714513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46732923204066666189809675 70099384806099999284714513)
  ·
    refine ⟨52574538604574999463535885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70099384806099999284714513 52574538604574999463535885)
    ·
      refine ⟨19715451976715624798825957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52574538604574999463535885 19715451976715624798825957)
      ·
        refine ⟨3696647245634179649779867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19715451976715624798825957 3696647245634179649779867)
        ·
          refine ⟨5544970868451269474669801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3696647245634179649779867 5544970868451269474669801)
          ·
            refine ⟨4158728151338452106002351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5544970868451269474669801 4158728151338452106002351)
            ·
              refine ⟨6238092227007678159003527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4158728151338452106002351 6238092227007678159003527)
              ·
                refine ⟨9357138340511517238505291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6238092227007678159003527 9357138340511517238505291)
                ·
                  refine ⟨14035707510767275857757937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9357138340511517238505291 14035707510767275857757937)
                  ·
                    refine ⟨10526780633075456893318453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14035707510767275857757937 10526780633075456893318453)
                    ·
                      refine ⟨986885684350824083748605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10526780633075456893318453 986885684350824083748605)
                      ·
                        rfl

theorem cell23_1921953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1921953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921953 prefixEnd_1921953 := by exact prefixLift 1921953
  have htrace : WordTrace (prefixWord ++ tailWord_1921953) baseStart_1921953 baseEnd_1921953 := by
    simpa [prefixWord, tailWord_1921953, baseEnd_1921953] using wordTrace_append hprefix tailTrace_1921953
  have hstable : (prefixWord ++ tailWord_1921953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921953).length < 2 ^ (prefixWord ++ tailWord_1921953).sum := by decide
  have hdescent : baseEnd_1921953 < baseStart_1921953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1921973 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 5, 4]
def baseStart_1921973 : Nat := 118140960795 + 1921973 * 2 ^ 59
def prefixEnd_1921973 : Nat := 4983230072969 + 3 ^ 40 * 1921973 * 2
def baseEnd_1921973 : Nat := 328965317987971335166171

theorem tailTrace_1921973 : CollatzResearch.WordTrace tailWord_1921973 prefixEnd_1921973 328965317987971335166171 := by
  unfold tailWord_1921973
  simp only [CollatzResearch.WordTrace]
  refine ⟨70100114266027542700442573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 46733409510685028466961715 70100114266027542700442573)
  ·
    refine ⟨26287542849760328512665965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70100114266027542700442573 26287542849760328512665965)
    ·
      refine ⟨9857828568660123192249737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26287542849760328512665965 9857828568660123192249737)
      ·
        refine ⟨7393371426495092394187303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9857828568660123192249737 7393371426495092394187303)
        ·
          refine ⟨11090057139742638591280955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7393371426495092394187303 11090057139742638591280955)
          ·
            refine ⟨16635085709613957886921433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11090057139742638591280955 16635085709613957886921433)
            ·
              refine ⟨12476314282210468415191075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16635085709613957886921433 12476314282210468415191075)
              ·
                refine ⟨18714471423315702622786613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12476314282210468415191075 18714471423315702622786613)
                ·
                  refine ⟨1754481695935847120886245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18714471423315702622786613 1754481695935847120886245)
                  ·
                    refine ⟨328965317987971335166171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1754481695935847120886245 328965317987971335166171)
                    ·
                      rfl

theorem cell23_1921973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 4].length) (baseStart_1921973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1921973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1921973 prefixEnd_1921973 := by exact prefixLift 1921973
  have htrace : WordTrace (prefixWord ++ tailWord_1921973) baseStart_1921973 baseEnd_1921973 := by
    simpa [prefixWord, tailWord_1921973, baseEnd_1921973] using wordTrace_append hprefix tailTrace_1921973
  have hstable : (prefixWord ++ tailWord_1921973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1921973).length < 2 ^ (prefixWord ++ tailWord_1921973).sum := by decide
  have hdescent : baseEnd_1921973 < baseStart_1921973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1921973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
