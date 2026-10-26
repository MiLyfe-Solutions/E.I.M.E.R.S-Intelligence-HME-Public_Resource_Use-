import V185TrunkScan23Chunk0110

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_656915 : List Nat := [1, 1, 1, 2, 1, 7, 1, 2, 3, 1, 3]
def baseStart_656915 : Nat := 118140960795 + 656915 * 2 ^ 59
def prefixEnd_656915 : Nat := 4983230072969 + 3 ^ 40 * 656915 * 2
def baseEnd_656915 : Nat := 337313144148402550741409

theorem tailTrace_656915 : CollatzResearch.WordTrace tailWord_656915 prefixEnd_656915 337313144148402550741409 := by
  unfold tailWord_656915
  simp only [CollatzResearch.WordTrace]
  refine ⟨23959658415116621995036199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15973105610077747996690799 23959658415116621995036199)
  ·
    refine ⟨35939487622674932992554299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23959658415116621995036199 35939487622674932992554299)
    ·
      refine ⟨53909231434012399488831449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35939487622674932992554299 53909231434012399488831449)
      ·
        refine ⟨40431923575509299616623587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53909231434012399488831449 40431923575509299616623587)
        ·
          refine ⟨60647885363263949424935381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40431923575509299616623587 60647885363263949424935381)
          ·
            refine ⟨1421434813201498814646923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 60647885363263949424935381 1421434813201498814646923)
            ·
              refine ⟨2132152219802248221970385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421434813201498814646923 2132152219802248221970385)
              ·
                refine ⟨1599114164851686166477789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2132152219802248221970385 1599114164851686166477789)
                ·
                  refine ⟨599667811819382312429171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1599114164851686166477789 599667811819382312429171)
                  ·
                    refine ⟨899501717729073468643757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 599667811819382312429171 899501717729073468643757)
                    ·
                      refine ⟨337313144148402550741409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 899501717729073468643757 337313144148402550741409)
                      ·
                        rfl

theorem cell23_656915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 2, 3, 1, 3].length) (baseStart_656915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656915 prefixEnd_656915 := by exact prefixLift 656915
  have htrace : WordTrace (prefixWord ++ tailWord_656915) baseStart_656915 baseEnd_656915 := by
    simpa [prefixWord, tailWord_656915, baseEnd_656915] using wordTrace_append hprefix tailTrace_656915
  have hstable : (prefixWord ++ tailWord_656915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656915).length < 2 ^ (prefixWord ++ tailWord_656915).sum := by decide
  have hdescent : baseEnd_656915 < baseStart_656915 := by decide
  rcases family_descends (prefixWord ++ tailWord_656915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656925 : List Nat := [1, 4, 2, 2, 1, 1, 3, 1, 1, 5, 2]
def baseStart_656925 : Nat := 118140960795 + 656925 * 2 ^ 59
def prefixEnd_656925 : Nat := 4983230072969 + 3 ^ 40 * 656925 * 2
def baseEnd_656925 : Nat := 337318278954947511616363

theorem tailTrace_656925 : CollatzResearch.WordTrace tailWord_656925 prefixEnd_656925 337318278954947511616363 := by
  unfold tailWord_656925
  simp only [CollatzResearch.WordTrace]
  refine ⟨23960023145080393702900229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15973348763386929135266819 23960023145080393702900229)
  ·
    refine ⟨4492504339702573819293793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23960023145080393702900229 4492504339702573819293793)
    ·
      refine ⟨3369378254776930364470345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4492504339702573819293793 3369378254776930364470345)
      ·
        refine ⟨2527033691082697773352759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3369378254776930364470345 2527033691082697773352759)
        ·
          refine ⟨3790550536624046660029139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2527033691082697773352759 3790550536624046660029139)
          ·
            refine ⟨5685825804936069990043709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3790550536624046660029139 5685825804936069990043709)
            ·
              refine ⟨2132184676851026246266391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5685825804936069990043709 2132184676851026246266391)
              ·
                refine ⟨3198277015276539369399587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2132184676851026246266391 3198277015276539369399587)
                ·
                  refine ⟨4797415522914809054099381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3198277015276539369399587 4797415522914809054099381)
                  ·
                    refine ⟨449757705273263348821817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4797415522914809054099381 449757705273263348821817)
                    ·
                      refine ⟨337318278954947511616363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 449757705273263348821817 337318278954947511616363)
                      ·
                        rfl

theorem cell23_656925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_656925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656925 prefixEnd_656925 := by exact prefixLift 656925
  have htrace : WordTrace (prefixWord ++ tailWord_656925) baseStart_656925 baseEnd_656925 := by
    simpa [prefixWord, tailWord_656925, baseEnd_656925] using wordTrace_append hprefix tailTrace_656925
  have hstable : (prefixWord ++ tailWord_656925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656925).length < 2 ^ (prefixWord ++ tailWord_656925).sum := by decide
  have hdescent : baseEnd_656925 < baseStart_656925 := by decide
  rcases family_descends (prefixWord ++ tailWord_656925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656972 : List Nat := [2, 2, 1, 3, 1, 3, 2, 2, 3, 2, 2]
def baseStart_656972 : Nat := 118140960795 + 656972 * 2 ^ 59
def prefixEnd_656972 : Nat := 4983230072969 + 3 ^ 40 * 656972 * 2
def baseEnd_656972 : Nat := 337342412545708827728647

theorem tailTrace_656972 : CollatzResearch.WordTrace tailWord_656972 prefixEnd_656972 337342412545708827728647 := by
  unfold tailWord_656972
  simp only [CollatzResearch.WordTrace]
  refine ⟨11980868687955060364930585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15974491583940080486574113 11980868687955060364930585)
  ·
    refine ⟨8985651515966295273697939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11980868687955060364930585 8985651515966295273697939)
    ·
      refine ⟨13478477273949442910546909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8985651515966295273697939 13478477273949442910546909)
      ·
        refine ⟨5054428977731041091455091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13478477273949442910546909 5054428977731041091455091)
        ·
          refine ⟨7581643466596561637182637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5054428977731041091455091 7581643466596561637182637)
          ·
            refine ⟨2843116299973710613943489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7581643466596561637182637 2843116299973710613943489)
            ·
              refine ⟨2132337224980282960457617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2843116299973710613943489 2132337224980282960457617)
              ·
                refine ⟨1599252918735212220343213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2132337224980282960457617 1599252918735212220343213)
                ·
                  refine ⟨599719844525704582628705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1599252918735212220343213 599719844525704582628705)
                  ·
                    refine ⟨449789883394278436971529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 599719844525704582628705 449789883394278436971529)
                    ·
                      refine ⟨337342412545708827728647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 449789883394278436971529 337342412545708827728647)
                      ·
                        rfl

theorem cell23_656972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_656972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656972 prefixEnd_656972 := by exact prefixLift 656972
  have htrace : WordTrace (prefixWord ++ tailWord_656972) baseStart_656972 baseEnd_656972 := by
    simpa [prefixWord, tailWord_656972, baseEnd_656972] using wordTrace_append hprefix tailTrace_656972
  have hstable : (prefixWord ++ tailWord_656972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656972).length < 2 ^ (prefixWord ++ tailWord_656972).sum := by decide
  have hdescent : baseEnd_656972 < baseStart_656972 := by decide
  rcases family_descends (prefixWord ++ tailWord_656972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656978 : List Nat := [3, 2, 2, 1, 2, 3, 1, 9]
def baseStart_656978 : Nat := 118140960795 + 656978 * 2 ^ 59
def prefixEnd_656978 : Nat := 4983230072969 + 3 ^ 40 * 656978 * 2
def baseEnd_656978 : Nat := 12494277534430955713097

theorem tailTrace_656978 : CollatzResearch.WordTrace tailWord_656978 prefixEnd_656978 12494277534430955713097 := by
  unfold tailWord_656978
  simp only [CollatzResearch.WordTrace]
  refine ⟨5990489053472095938644897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15974637475925589169719725 5990489053472095938644897)
  ·
    refine ⟨4492866790104071953983673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5990489053472095938644897 4492866790104071953983673)
    ·
      refine ⟨3369650092578053965487755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4492866790104071953983673 3369650092578053965487755)
      ·
        refine ⟨5054475138867080948231633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3369650092578053965487755 5054475138867080948231633)
        ·
          refine ⟨3790856354150310711173725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5054475138867080948231633 3790856354150310711173725)
          ·
            refine ⟨1421571132806366516690147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3790856354150310711173725 1421571132806366516690147)
            ·
              refine ⟨2132356699209549775035221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421571132806366516690147 2132356699209549775035221)
              ·
                refine ⟨12494277534430955713097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2132356699209549775035221 12494277534430955713097)
                ·
                  rfl

theorem cell23_656978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 9].length) (baseStart_656978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656978 prefixEnd_656978 := by exact prefixLift 656978
  have htrace : WordTrace (prefixWord ++ tailWord_656978) baseStart_656978 baseEnd_656978 := by
    simpa [prefixWord, tailWord_656978, baseEnd_656978] using wordTrace_append hprefix tailTrace_656978
  have hstable : (prefixWord ++ tailWord_656978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656978).length < 2 ^ (prefixWord ++ tailWord_656978).sum := by decide
  have hdescent : baseEnd_656978 < baseStart_656978 := by decide
  rcases family_descends (prefixWord ++ tailWord_656978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_656991 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 3, 9]
def baseStart_656991 : Nat := 118140960795 + 656991 * 2 ^ 59
def prefixEnd_656991 : Nat := 4983230072969 + 3 ^ 40 * 656991 * 2
def baseEnd_656991 : Nat := 112450722892714751130353

theorem tailTrace_656991 : CollatzResearch.WordTrace tailWord_656991 prefixEnd_656991 112450722892714751130353 := by
  unfold tailWord_656991
  simp only [CollatzResearch.WordTrace]
  refine ⟨23962430362841286974802827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15974953575227524649868551 23962430362841286974802827)
  ·
    refine ⟨35943645544261930462204241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23962430362841286974802827 35943645544261930462204241)
    ·
      refine ⟨26957734158196447846653181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35943645544261930462204241 26957734158196447846653181)
      ·
        refine ⟨10109150309323667942494943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26957734158196447846653181 10109150309323667942494943)
        ·
          refine ⟨15163725463985501913742415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10109150309323667942494943 15163725463985501913742415)
          ·
            refine ⟨22745588195978252870613623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15163725463985501913742415 22745588195978252870613623)
            ·
              refine ⟨34118382293967379305920435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22745588195978252870613623 34118382293967379305920435)
              ·
                refine ⟨51177573440951068958880653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34118382293967379305920435 51177573440951068958880653)
                ·
                  refine ⟨19191590040356650859580245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51177573440951068958880653 19191590040356650859580245)
                  ·
                    refine ⟨112450722892714751130353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 19191590040356650859580245 112450722892714751130353)
                    ·
                      rfl

theorem cell23_656991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 9].length) (baseStart_656991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_656991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_656991 prefixEnd_656991 := by exact prefixLift 656991
  have htrace : WordTrace (prefixWord ++ tailWord_656991) baseStart_656991 baseEnd_656991 := by
    simpa [prefixWord, tailWord_656991, baseEnd_656991] using wordTrace_append hprefix tailTrace_656991
  have hstable : (prefixWord ++ tailWord_656991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_656991).length < 2 ^ (prefixWord ++ tailWord_656991).sum := by decide
  have hdescent : baseEnd_656991 < baseStart_656991 := by decide
  rcases family_descends (prefixWord ++ tailWord_656991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657006 : List Nat := [4, 1, 2, 2, 3, 2, 1, 1, 3, 2, 2]
def baseStart_657006 : Nat := 118140960795 + 657006 * 2 ^ 59
def prefixEnd_657006 : Nat := 4983230072969 + 3 ^ 40 * 657006 * 2
def baseEnd_657006 : Nat := 337359870887961694703491

theorem tailTrace_657006 : CollatzResearch.WordTrace tailWord_657006 prefixEnd_657006 337359870887961694703491 := by
  unfold tailWord_657006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2995372182223368067074859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15975318305191296357732581 2995372182223368067074859)
  ·
    refine ⟨4493058273335052100612289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2995372182223368067074859 4493058273335052100612289)
    ·
      refine ⟨3369793705001289075459217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4493058273335052100612289 3369793705001289075459217)
      ·
        refine ⟨2527345278750966806594413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3369793705001289075459217 2527345278750966806594413)
        ·
          refine ⟨947754479531612552472905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2527345278750966806594413 947754479531612552472905)
          ·
            refine ⟨710815859648709414354679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 947754479531612552472905 710815859648709414354679)
            ·
              refine ⟨1066223789473064121532019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710815859648709414354679 1066223789473064121532019)
              ·
                refine ⟨1599335684209596182298029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066223789473064121532019 1599335684209596182298029)
                ·
                  refine ⟨599750881578598568361761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1599335684209596182298029 599750881578598568361761)
                  ·
                    refine ⟨449813161183948926271321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 599750881578598568361761 449813161183948926271321)
                    ·
                      refine ⟨337359870887961694703491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 449813161183948926271321 337359870887961694703491)
                      ·
                        rfl

theorem cell23_657006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_657006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657006 prefixEnd_657006 := by exact prefixLift 657006
  have htrace : WordTrace (prefixWord ++ tailWord_657006) baseStart_657006 baseEnd_657006 := by
    simpa [prefixWord, tailWord_657006, baseEnd_657006] using wordTrace_append hprefix tailTrace_657006
  have hstable : (prefixWord ++ tailWord_657006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657006).length < 2 ^ (prefixWord ++ tailWord_657006).sum := by decide
  have hdescent : baseEnd_657006 < baseStart_657006 := by decide
  rcases family_descends (prefixWord ++ tailWord_657006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657011 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 10]
def baseStart_657011 : Nat := 118140960795 + 657011 * 2 ^ 59
def prefixEnd_657011 : Nat := 4983230072969 + 3 ^ 40 * 657011 * 2
def baseEnd_657011 : Nat := 337362438291234175140967

theorem tailTrace_657011 : CollatzResearch.WordTrace tailWord_657011 prefixEnd_657011 337362438291234175140967 := by
  unfold tailWord_657011
  simp only [CollatzResearch.WordTrace]
  refine ⟨23963159822768830390530887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15975439881845886927020591 23963159822768830390530887)
  ·
    refine ⟨35944739734153245585796331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23963159822768830390530887 35944739734153245585796331)
    ·
      refine ⟨53917109601229868378694497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35944739734153245585796331 53917109601229868378694497)
      ·
        refine ⟨40437832200922401284020873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53917109601229868378694497 40437832200922401284020873)
        ·
          refine ⟨30328374150691800963015655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40437832200922401284020873 30328374150691800963015655)
          ·
            refine ⟨45492561226037701444523483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30328374150691800963015655 45492561226037701444523483)
            ·
              refine ⟨68238841839056552166785225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45492561226037701444523483 68238841839056552166785225)
              ·
                refine ⟨51179131379292414125088919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68238841839056552166785225 51179131379292414125088919)
                ·
                  refine ⟨76768697068938621187633379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51179131379292414125088919 76768697068938621187633379)
                  ·
                    refine ⟨115153045603407931781450069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76768697068938621187633379 115153045603407931781450069)
                    ·
                      refine ⟨337362438291234175140967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 115153045603407931781450069 337362438291234175140967)
                      ·
                        rfl

theorem cell23_657011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_657011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657011 prefixEnd_657011 := by exact prefixLift 657011
  have htrace : WordTrace (prefixWord ++ tailWord_657011) baseStart_657011 baseEnd_657011 := by
    simpa [prefixWord, tailWord_657011, baseEnd_657011] using wordTrace_append hprefix tailTrace_657011
  have hstable : (prefixWord ++ tailWord_657011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657011).length < 2 ^ (prefixWord ++ tailWord_657011).sum := by decide
  have hdescent : baseEnd_657011 < baseStart_657011 := by decide
  rcases family_descends (prefixWord ++ tailWord_657011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657015 : List Nat := [1, 1, 3, 1, 1, 3, 1, 4, 3, 3, 2]
def baseStart_657015 : Nat := 118140960795 + 657015 * 2 ^ 59
def prefixEnd_657015 : Nat := 4983230072969 + 3 ^ 40 * 657015 * 2
def baseEnd_657015 : Nat := 337364492213852159490949

theorem tailTrace_657015 : CollatzResearch.WordTrace tailWord_657015 prefixEnd_657015 337364492213852159490949 := by
  unfold tailWord_657015
  simp only [CollatzResearch.WordTrace]
  refine ⟨23963305714754339073676499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15975537143169559382450999 23963305714754339073676499)
  ·
    refine ⟨35944958572131508610514749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23963305714754339073676499 35944958572131508610514749)
    ·
      refine ⟨13479359464549315728943031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35944958572131508610514749 13479359464549315728943031)
      ·
        refine ⟨20219039196823973593414547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13479359464549315728943031 20219039196823973593414547)
        ·
          refine ⟨30328558795235960390121821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20219039196823973593414547 30328558795235960390121821)
          ·
            refine ⟨11373209548213485146295683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30328558795235960390121821 11373209548213485146295683)
            ·
              refine ⟨17059814322320227719443525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11373209548213485146295683 17059814322320227719443525)
              ·
                refine ⟨3198715185435042697395661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17059814322320227719443525 3198715185435042697395661)
                ·
                  refine ⟨1199518194538141011523373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3198715185435042697395661 1199518194538141011523373)
                  ·
                    refine ⟨449819322951802879321265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1199518194538141011523373 449819322951802879321265)
                    ·
                      refine ⟨337364492213852159490949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 449819322951802879321265 337364492213852159490949)
                      ·
                        rfl

theorem cell23_657015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 4, 3, 3, 2].length) (baseStart_657015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657015 prefixEnd_657015 := by exact prefixLift 657015
  have htrace : WordTrace (prefixWord ++ tailWord_657015) baseStart_657015 baseEnd_657015 := by
    simpa [prefixWord, tailWord_657015, baseEnd_657015] using wordTrace_append hprefix tailTrace_657015
  have hstable : (prefixWord ++ tailWord_657015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657015).length < 2 ^ (prefixWord ++ tailWord_657015).sum := by decide
  have hdescent : baseEnd_657015 < baseStart_657015 := by decide
  rcases family_descends (prefixWord ++ tailWord_657015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657079 : List Nat := [1, 1, 3, 1, 5, 1, 2, 3, 2, 2, 2]
def baseStart_657079 : Nat := 118140960795 + 657079 * 2 ^ 59
def prefixEnd_657079 : Nat := 4983230072969 + 3 ^ 40 * 657079 * 2
def baseEnd_657079 : Nat := 337397354975739909090655

theorem tailTrace_657079 : CollatzResearch.WordTrace tailWord_657079 prefixEnd_657079 337397354975739909090655 := by
  unfold tailWord_657079
  simp only [CollatzResearch.WordTrace]
  refine ⟨23965639986522478004006291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15977093324348318669337527 23965639986522478004006291)
  ·
    refine ⟨35948459979783717006009437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23965639986522478004006291 35948459979783717006009437)
    ·
      refine ⟨13480672492418893877253539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35948459979783717006009437 13480672492418893877253539)
      ·
        refine ⟨20221008738628340815880309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13480672492418893877253539 20221008738628340815880309)
        ·
          refine ⟨1895719569246406951488779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20221008738628340815880309 1895719569246406951488779)
          ·
            refine ⟨2843579353869610427233169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1895719569246406951488779 2843579353869610427233169)
            ·
              refine ⟨2132684515402207820424877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2843579353869610427233169 2132684515402207820424877)
              ·
                refine ⟨799756693275827932659329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2132684515402207820424877 799756693275827932659329)
                ·
                  refine ⟨599817519956870949494497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 799756693275827932659329 599817519956870949494497)
                  ·
                    refine ⟨449863139967653212120873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 599817519956870949494497 449863139967653212120873)
                    ·
                      refine ⟨337397354975739909090655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 449863139967653212120873 337397354975739909090655)
                      ·
                        rfl

theorem cell23_657079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 2, 2, 2].length) (baseStart_657079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657079 prefixEnd_657079 := by exact prefixLift 657079
  have htrace : WordTrace (prefixWord ++ tailWord_657079) baseStart_657079 baseEnd_657079 := by
    simpa [prefixWord, tailWord_657079, baseEnd_657079] using wordTrace_append hprefix tailTrace_657079
  have hstable : (prefixWord ++ tailWord_657079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657079).length < 2 ^ (prefixWord ++ tailWord_657079).sum := by decide
  have hdescent : baseEnd_657079 < baseStart_657079 := by decide
  rcases family_descends (prefixWord ++ tailWord_657079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657102 : List Nat := [4, 1, 1, 1, 3, 1, 4, 3, 5]
def baseStart_657102 : Nat := 118140960795 + 657102 * 2 ^ 59
def prefixEnd_657102 : Nat := 4983230072969 + 3 ^ 40 * 657102 * 2
def baseEnd_657102 : Nat := 37489907225643702122561

theorem tailTrace_657102 : CollatzResearch.WordTrace tailWord_657102 prefixEnd_657102 37489907225643702122561 := by
  unfold tailWord_657102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2995809858179894116511695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15977652576959435288062373 2995809858179894116511695)
  ·
    refine ⟨4493714787269841174767543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2995809858179894116511695 4493714787269841174767543)
    ·
      refine ⟨6740572180904761762151315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4493714787269841174767543 6740572180904761762151315)
      ·
        refine ⟨10110858271357142643226973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6740572180904761762151315 10110858271357142643226973)
        ·
          refine ⟨3791571851758928491210115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10110858271357142643226973 3791571851758928491210115)
          ·
            refine ⟨5687357777638392736815173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3791571851758928491210115 5687357777638392736815173)
            ·
              refine ⟨1066379583307198638152845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5687357777638392736815173 1066379583307198638152845)
              ·
                refine ⟨399892343740199489307317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1066379583307198638152845 399892343740199489307317)
                ·
                  refine ⟨37489907225643702122561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 399892343740199489307317 37489907225643702122561)
                  ·
                    rfl

theorem cell23_657102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_657102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657102 prefixEnd_657102 := by exact prefixLift 657102
  have htrace : WordTrace (prefixWord ++ tailWord_657102) baseStart_657102 baseEnd_657102 := by
    simpa [prefixWord, tailWord_657102, baseEnd_657102] using wordTrace_append hprefix tailTrace_657102
  have hstable : (prefixWord ++ tailWord_657102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657102).length < 2 ^ (prefixWord ++ tailWord_657102).sum := by decide
  have hdescent : baseEnd_657102 < baseStart_657102 := by decide
  rcases family_descends (prefixWord ++ tailWord_657102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657155 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 3]
def baseStart_657155 : Nat := 118140960795 + 657155 * 2 ^ 59
def prefixEnd_657155 : Nat := 4983230072969 + 3 ^ 40 * 657155 * 2
def baseEnd_657155 : Nat := 337436379505481611740305

theorem tailTrace_657155 : CollatzResearch.WordTrace tailWord_657155 prefixEnd_657155 337436379505481611740305 := by
  unfold tailWord_657155
  simp only [CollatzResearch.WordTrace]
  refine ⟨23968411934247142983772919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15978941289498095322515279 23968411934247142983772919)
  ·
    refine ⟨35952617901370714475659379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23968411934247142983772919 35952617901370714475659379)
    ·
      refine ⟨53928926852056071713489069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35952617901370714475659379 53928926852056071713489069)
      ·
        refine ⟨20223347569521026892558401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53928926852056071713489069 20223347569521026892558401)
        ·
          refine ⟨15167510677140770169418801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20223347569521026892558401 15167510677140770169418801)
          ·
            refine ⟨11375633007855577627064101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15167510677140770169418801 11375633007855577627064101)
            ·
              refine ⟨2132931188972920805074519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11375633007855577627064101 2132931188972920805074519)
              ·
                refine ⟨3199396783459381207611779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2132931188972920805074519 3199396783459381207611779)
                ·
                  refine ⟨4799095175189071811417669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3199396783459381207611779 4799095175189071811417669)
                  ·
                    refine ⟨899830345347950964640813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4799095175189071811417669 899830345347950964640813)
                    ·
                      refine ⟨337436379505481611740305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 899830345347950964640813 337436379505481611740305)
                      ·
                        rfl

theorem cell23_657155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 3].length) (baseStart_657155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657155 prefixEnd_657155 := by exact prefixLift 657155
  have htrace : WordTrace (prefixWord ++ tailWord_657155) baseStart_657155 baseEnd_657155 := by
    simpa [prefixWord, tailWord_657155, baseEnd_657155] using wordTrace_append hprefix tailTrace_657155
  have hstable : (prefixWord ++ tailWord_657155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657155).length < 2 ^ (prefixWord ++ tailWord_657155).sum := by decide
  have hdescent : baseEnd_657155 < baseStart_657155 := by decide
  rcases family_descends (prefixWord ++ tailWord_657155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657175 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 8]
def baseStart_657175 : Nat := 118140960795 + 657175 * 2 ^ 59
def prefixEnd_657175 : Nat := 4983230072969 + 3 ^ 40 * 657175 * 2
def baseEnd_657175 : Nat := 37494072124285725943357

theorem tailTrace_657175 : CollatzResearch.WordTrace tailWord_657175 prefixEnd_657175 37494072124285725943357 := by
  unfold tailWord_657175
  simp only [CollatzResearch.WordTrace]
  refine ⟨23969141394174686399500979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15979427596116457599667319 23969141394174686399500979)
  ·
    refine ⟨35953712091262029599251469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23969141394174686399500979 35953712091262029599251469)
    ·
      refine ⟨13482642034223261099719301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35953712091262029599251469 13482642034223261099719301)
      ·
        refine ⟨2527995381416861456197369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13482642034223261099719301 2527995381416861456197369)
        ·
          refine ⟨1895996536062646092148027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2527995381416861456197369 1895996536062646092148027)
          ·
            refine ⟨2843994804093969138222041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1895996536062646092148027 2843994804093969138222041)
            ·
              refine ⟨2132996103070476853666531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2843994804093969138222041 2132996103070476853666531)
              ·
                refine ⟨3199494154605715280499797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2132996103070476853666531 3199494154605715280499797)
                ·
                  refine ⟨37494072124285725943357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3199494154605715280499797 37494072124285725943357)
                  ·
                    rfl

theorem cell23_657175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 8].length) (baseStart_657175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657175 prefixEnd_657175 := by exact prefixLift 657175
  have htrace : WordTrace (prefixWord ++ tailWord_657175) baseStart_657175 baseEnd_657175 := by
    simpa [prefixWord, tailWord_657175, baseEnd_657175] using wordTrace_append hprefix tailTrace_657175
  have hstable : (prefixWord ++ tailWord_657175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657175).length < 2 ^ (prefixWord ++ tailWord_657175).sum := by decide
  have hdescent : baseEnd_657175 < baseStart_657175 := by decide
  rcases family_descends (prefixWord ++ tailWord_657175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657192 : List Nat := [2, 1, 5, 1, 1, 3, 1, 3, 6]
def baseStart_657192 : Nat := 118140960795 + 657192 * 2 ^ 59
def prefixEnd_657192 : Nat := 4983230072969 + 3 ^ 40 * 657192 * 2
def baseEnd_657192 : Nat := 37495042032188662997515

theorem tailTrace_657192 : CollatzResearch.WordTrace tailWord_657192 prefixEnd_657192 37495042032188662997515 := by
  unfold tailWord_657192
  simp only [CollatzResearch.WordTrace]
  refine ⟨11984880717556549151434915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15979840956742065535246553 11984880717556549151434915)
  ·
    refine ⟨17977321076334823727152373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11984880717556549151434915 17977321076334823727152373)
    ·
      refine ⟨1685373850906389724420535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17977321076334823727152373 1685373850906389724420535)
      ·
        refine ⟨2528060776359584586630803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1685373850906389724420535 2528060776359584586630803)
        ·
          refine ⟨3792091164539376879946205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2528060776359584586630803 3792091164539376879946205)
          ·
            refine ⟨1422034186702266329979827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3792091164539376879946205 1422034186702266329979827)
            ·
              refine ⟨2133051280053399494969741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422034186702266329979827 2133051280053399494969741)
              ·
                refine ⟨799894230020024810613653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2133051280053399494969741 799894230020024810613653)
                ·
                  refine ⟨37495042032188662997515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 799894230020024810613653 37495042032188662997515)
                  ·
                    rfl

theorem cell23_657192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 3, 6].length) (baseStart_657192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657192 prefixEnd_657192 := by exact prefixLift 657192
  have htrace : WordTrace (prefixWord ++ tailWord_657192) baseStart_657192 baseEnd_657192 := by
    simpa [prefixWord, tailWord_657192, baseEnd_657192] using wordTrace_append hprefix tailTrace_657192
  have hstable : (prefixWord ++ tailWord_657192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657192).length < 2 ^ (prefixWord ++ tailWord_657192).sum := by decide
  have hdescent : baseEnd_657192 < baseStart_657192 := by decide
  rcases family_descends (prefixWord ++ tailWord_657192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657206 : List Nat := [5, 1, 2, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_657206 : Nat := 118140960795 + 657206 * 2 ^ 59
def prefixEnd_657206 : Nat := 4983230072969 + 3 ^ 40 * 657206 * 2
def baseEnd_657206 : Nat := 337462567018860912202571

theorem tailTrace_657206 : CollatzResearch.WordTrace tailWord_657206 prefixEnd_657206 337462567018860912202571 := by
  unfold tailWord_657206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1498142003566398668367467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15980181371374919129252981 1498142003566398668367467)
  ·
    refine ⟨2247213005349598002551201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1498142003566398668367467 2247213005349598002551201)
    ·
      refine ⟨1685409754012198501913401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2247213005349598002551201 1685409754012198501913401)
      ·
        refine ⟨1264057315509148876435051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1685409754012198501913401 1264057315509148876435051)
        ·
          refine ⟨1896085973263723314652577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1264057315509148876435051 1896085973263723314652577)
          ·
            refine ⟨1422064479947792485989433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1896085973263723314652577 1422064479947792485989433)
            ·
              refine ⟨1066548359960844364492075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1422064479947792485989433 1066548359960844364492075)
              ·
                refine ⟨1599822539941266546738113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066548359960844364492075 1599822539941266546738113)
                ·
                  refine ⟨1199866904955949910053585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1599822539941266546738113 1199866904955949910053585)
                  ·
                    refine ⟨899900178716962432540189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1199866904955949910053585 899900178716962432540189)
                    ·
                      refine ⟨337462567018860912202571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 899900178716962432540189 337462567018860912202571)
                      ·
                        rfl

theorem cell23_657206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_657206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657206 prefixEnd_657206 := by exact prefixLift 657206
  have htrace : WordTrace (prefixWord ++ tailWord_657206) baseStart_657206 baseEnd_657206 := by
    simpa [prefixWord, tailWord_657206, baseEnd_657206] using wordTrace_append hprefix tailTrace_657206
  have hstable : (prefixWord ++ tailWord_657206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657206).length < 2 ^ (prefixWord ++ tailWord_657206).sum := by decide
  have hdescent : baseEnd_657206 < baseStart_657206 := by decide
  rcases family_descends (prefixWord ++ tailWord_657206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657212 : List Nat := [2, 2, 2, 2, 1, 1, 2, 3, 1, 5, 2]
def baseStart_657212 : Nat := 118140960795 + 657212 * 2 ^ 59
def prefixEnd_657212 : Nat := 4983230072969 + 3 ^ 40 * 657212 * 2
def baseEnd_657212 : Nat := 337465647902787888727543

theorem tailTrace_657212 : CollatzResearch.WordTrace tailWord_657212 prefixEnd_657212 337465647902787888727543 := by
  unfold tailWord_657212
  simp only [CollatzResearch.WordTrace]
  refine ⟨11985245447520320859298945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15980327263360427812398593 11985245447520320859298945)
  ·
    refine ⟨8988934085640240644474209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11985245447520320859298945 8988934085640240644474209)
    ·
      refine ⟨6741700564230180483355657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8988934085640240644474209 6741700564230180483355657)
      ·
        refine ⟨5056275423172635362516743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6741700564230180483355657 5056275423172635362516743)
        ·
          refine ⟨7584413134758953043775115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5056275423172635362516743 7584413134758953043775115)
          ·
            refine ⟨11376619702138429565662673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7584413134758953043775115 11376619702138429565662673)
            ·
              refine ⟨8532464776603822174247005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11376619702138429565662673 8532464776603822174247005)
              ·
                refine ⟨3199674291226433315342627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8532464776603822174247005 3199674291226433315342627)
                ·
                  refine ⟨4799511436839649973013941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3199674291226433315342627 4799511436839649973013941)
                  ·
                    refine ⟨449954197203717184970057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4799511436839649973013941 449954197203717184970057)
                    ·
                      refine ⟨337465647902787888727543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 449954197203717184970057 337465647902787888727543)
                      ·
                        rfl

theorem cell23_657212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_657212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657212 prefixEnd_657212 := by exact prefixLift 657212
  have htrace : WordTrace (prefixWord ++ tailWord_657212) baseStart_657212 baseEnd_657212 := by
    simpa [prefixWord, tailWord_657212, baseEnd_657212] using wordTrace_append hprefix tailTrace_657212
  have hstable : (prefixWord ++ tailWord_657212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657212).length < 2 ^ (prefixWord ++ tailWord_657212).sum := by decide
  have hdescent : baseEnd_657212 < baseStart_657212 := by decide
  rcases family_descends (prefixWord ++ tailWord_657212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657270 : List Nat := [5, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3]
def baseStart_657270 : Nat := 118140960795 + 657270 * 2 ^ 59
def prefixEnd_657270 : Nat := 4983230072969 + 3 ^ 40 * 657270 * 2
def baseEnd_657270 : Nat := 337495429780748661802277

theorem tailTrace_657270 : CollatzResearch.WordTrace tailWord_657270 prefixEnd_657270 337495429780748661802277 := by
  unfold tailWord_657270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1498287895551907351513079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15981737552553678416139509 1498287895551907351513079)
  ·
    refine ⟨2247431843327861027269619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1498287895551907351513079 2247431843327861027269619)
    ·
      refine ⟨3371147764991791540904429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2247431843327861027269619 3371147764991791540904429)
      ·
        refine ⟨1264180411871921827839161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3371147764991791540904429 1264180411871921827839161)
        ·
          refine ⟨948135308903941370879371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1264180411871921827839161 948135308903941370879371)
          ·
            refine ⟨1422202963355912056319057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948135308903941370879371 1422202963355912056319057)
            ·
              refine ⟨1066652222516934042239293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1422202963355912056319057 1066652222516934042239293)
              ·
                refine ⟨399994583443850265839735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1066652222516934042239293 399994583443850265839735)
                ·
                  refine ⟨599991875165775398759603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 399994583443850265839735 599991875165775398759603)
                  ·
                    refine ⟨899987812748663098139405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 599991875165775398759603 899987812748663098139405)
                    ·
                      refine ⟨337495429780748661802277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 899987812748663098139405 337495429780748661802277)
                      ·
                        rfl

theorem cell23_657270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_657270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657270 prefixEnd_657270 := by exact prefixLift 657270
  have htrace : WordTrace (prefixWord ++ tailWord_657270) baseStart_657270 baseEnd_657270 := by
    simpa [prefixWord, tailWord_657270, baseEnd_657270] using wordTrace_append hprefix tailTrace_657270
  have hstable : (prefixWord ++ tailWord_657270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657270).length < 2 ^ (prefixWord ++ tailWord_657270).sum := by decide
  have hdescent : baseEnd_657270 < baseStart_657270 := by decide
  rcases family_descends (prefixWord ++ tailWord_657270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657309 : List Nat := [1, 4, 2, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_657309 : Nat := 118140960795 + 657309 * 2 ^ 59
def prefixEnd_657309 : Nat := 4983230072969 + 3 ^ 40 * 657309 * 2
def baseEnd_657309 : Nat := 337515455526274009214597

theorem tailTrace_657309 : CollatzResearch.WordTrace tailWord_657309 prefixEnd_657309 337515455526274009214597 := by
  unfold tailWord_657309
  simp only [CollatzResearch.WordTrace]
  refine ⟨23974028775689227284878981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15982685850459484856585987 23974028775689227284878981)
  ·
    refine ⟨4495130395441730115914809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23974028775689227284878981 4495130395441730115914809)
    ·
      refine ⟨3371347796581297586936107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4495130395441730115914809 3371347796581297586936107)
      ·
        refine ⟨5057021694871946380404161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3371347796581297586936107 5057021694871946380404161)
        ·
          refine ⟨3792766271153959785303121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5057021694871946380404161 3792766271153959785303121)
          ·
            refine ⟨2844574703365469838977341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3792766271153959785303121 2844574703365469838977341)
            ·
              refine ⟨1066715513762051189616503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2844574703365469838977341 1066715513762051189616503)
              ·
                refine ⟨1600073270643076784424755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066715513762051189616503 1600073270643076784424755)
                ·
                  refine ⟨2400109905964615176637133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1600073270643076784424755 2400109905964615176637133)
                  ·
                    refine ⟨900041214736730691238925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2400109905964615176637133 900041214736730691238925)
                    ·
                      refine ⟨337515455526274009214597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 900041214736730691238925 337515455526274009214597)
                      ·
                        rfl

theorem cell23_657309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_657309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657309 prefixEnd_657309 := by exact prefixLift 657309
  have htrace : WordTrace (prefixWord ++ tailWord_657309) baseStart_657309 baseEnd_657309 := by
    simpa [prefixWord, tailWord_657309, baseEnd_657309] using wordTrace_append hprefix tailTrace_657309
  have hstable : (prefixWord ++ tailWord_657309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657309).length < 2 ^ (prefixWord ++ tailWord_657309).sum := by decide
  have hdescent : baseEnd_657309 < baseStart_657309 := by decide
  rcases family_descends (prefixWord ++ tailWord_657309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657370 : List Nat := [3, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2]
def baseStart_657370 : Nat := 118140960795 + 657370 * 2 ^ 59
def prefixEnd_657370 : Nat := 4983230072969 + 3 ^ 40 * 657370 * 2
def baseEnd_657370 : Nat := 337546777846198270551817

theorem tailTrace_657370 : CollatzResearch.WordTrace tailWord_657370 prefixEnd_657370 337546777846198270551817 := by
  unfold tailWord_657370
  simp only [CollatzResearch.WordTrace]
  refine ⟨5994063407117058675712391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15984169085645489801899709 5994063407117058675712391)
  ·
    refine ⟨8991095110675588013568587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5994063407117058675712391 8991095110675588013568587)
    ·
      refine ⟨13486642666013382020352881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8991095110675588013568587 13486642666013382020352881)
      ·
        refine ⟨10114981999510036515264661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13486642666013382020352881 10114981999510036515264661)
        ·
          refine ⟨474139781227032961653031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10114981999510036515264661 474139781227032961653031)
          ·
            refine ⟨711209671840549442479547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474139781227032961653031 711209671840549442479547)
            ·
              refine ⟨1066814507760824163719321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 711209671840549442479547 1066814507760824163719321)
              ·
                refine ⟨800110880820618122789491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1066814507760824163719321 800110880820618122789491)
                ·
                  refine ⟨1200166321230927184184237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 800110880820618122789491 1200166321230927184184237)
                  ·
                    refine ⟨450062370461597694069089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1200166321230927184184237 450062370461597694069089)
                    ·
                      refine ⟨337546777846198270551817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 450062370461597694069089 337546777846198270551817)
                      ·
                        rfl

theorem cell23_657370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_657370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657370 prefixEnd_657370 := by exact prefixLift 657370
  have htrace : WordTrace (prefixWord ++ tailWord_657370) baseStart_657370 baseEnd_657370 := by
    simpa [prefixWord, tailWord_657370, baseEnd_657370] using wordTrace_append hprefix tailTrace_657370
  have hstable : (prefixWord ++ tailWord_657370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657370).length < 2 ^ (prefixWord ++ tailWord_657370).sum := by decide
  have hdescent : baseEnd_657370 < baseStart_657370 := by decide
  rcases family_descends (prefixWord ++ tailWord_657370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657409 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 1, 7, 2]
def baseStart_657409 : Nat := 118140960795 + 657409 * 2 ^ 59
def prefixEnd_657409 : Nat := 4983230072969 + 3 ^ 40 * 657409 * 2
def baseEnd_657409 : Nat := 337566803591723617964137

theorem tailTrace_657409 : CollatzResearch.WordTrace tailWord_657409 prefixEnd_657409 337566803591723617964137 := by
  unfold tailWord_657409
  simp only [CollatzResearch.WordTrace]
  refine ⟨23977676075326944363519281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15985117383551296242346187 23977676075326944363519281)
  ·
    refine ⟨17983257056495208272639461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23977676075326944363519281 17983257056495208272639461)
    ·
      refine ⟨3371860698092851551119899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17983257056495208272639461 3371860698092851551119899)
      ·
        refine ⟨5057791047139277326679849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3371860698092851551119899 5057791047139277326679849)
        ·
          refine ⟨3793343285354457995009887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5057791047139277326679849 3793343285354457995009887)
          ·
            refine ⟨5690014928031686992514831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3793343285354457995009887 5690014928031686992514831)
            ·
              refine ⟨8535022392047530488772247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5690014928031686992514831 8535022392047530488772247)
              ·
                refine ⟨12802533588071295733158371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8535022392047530488772247 12802533588071295733158371)
                ·
                  refine ⟨19203800382106943599737557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12802533588071295733158371 19203800382106943599737557)
                  ·
                    refine ⟨450089071455631490618849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19203800382106943599737557 450089071455631490618849)
                    ·
                      refine ⟨337566803591723617964137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 450089071455631490618849 337566803591723617964137)
                      ·
                        rfl

theorem cell23_657409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_657409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657409 prefixEnd_657409 := by exact prefixLift 657409
  have htrace : WordTrace (prefixWord ++ tailWord_657409) baseStart_657409 baseEnd_657409 := by
    simpa [prefixWord, tailWord_657409, baseEnd_657409] using wordTrace_append hprefix tailTrace_657409
  have hstable : (prefixWord ++ tailWord_657409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657409).length < 2 ^ (prefixWord ++ tailWord_657409).sum := by decide
  have hdescent : baseEnd_657409 < baseStart_657409 := by decide
  rcases family_descends (prefixWord ++ tailWord_657409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657436 : List Nat := [2, 2, 3, 1, 3, 3, 1, 1, 2, 5]
def baseStart_657436 : Nat := 118140960795 + 657436 * 2 ^ 59
def prefixEnd_657436 : Nat := 4983230072969 + 3 ^ 40 * 657436 * 2
def baseEnd_657436 : Nat := 112526889189798337442171

theorem tailTrace_657436 : CollatzResearch.WordTrace tailWord_657436 prefixEnd_657436 112526889189798337442171 := by
  unfold tailWord_657436
  simp only [CollatzResearch.WordTrace]
  refine ⟨11989330423114563987376081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15985773897486085316501441 11989330423114563987376081)
  ·
    refine ⟨8991997817335922990532061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11989330423114563987376081 8991997817335922990532061)
    ·
      refine ⟨3371999181500971121449523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8991997817335922990532061 3371999181500971121449523)
      ·
        refine ⟨5057998772251456682174285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3371999181500971121449523 5057998772251456682174285)
        ·
          refine ⟨1896749539594296255815357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5057998772251456682174285 1896749539594296255815357)
          ·
            refine ⟨711281077347861095930759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1896749539594296255815357 711281077347861095930759)
            ·
              refine ⟨1066921616021791643896139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 711281077347861095930759 1066921616021791643896139)
              ·
                refine ⟨1600382424032687465844209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066921616021791643896139 1600382424032687465844209)
                ·
                  refine ⟨1200286818024515599383157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1600382424032687465844209 1200286818024515599383157)
                  ·
                    refine ⟨112526889189798337442171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1200286818024515599383157 112526889189798337442171)
                    ·
                      rfl

theorem cell23_657436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_657436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657436 prefixEnd_657436 := by exact prefixLift 657436
  have htrace : WordTrace (prefixWord ++ tailWord_657436) baseStart_657436 baseEnd_657436 := by
    simpa [prefixWord, tailWord_657436, baseEnd_657436] using wordTrace_append hprefix tailTrace_657436
  have hstable : (prefixWord ++ tailWord_657436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657436).length < 2 ^ (prefixWord ++ tailWord_657436).sum := by decide
  have hdescent : baseEnd_657436 < baseStart_657436 := by decide
  rcases family_descends (prefixWord ++ tailWord_657436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657439 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 1, 6, 2]
def baseStart_657439 : Nat := 118140960795 + 657439 * 2 ^ 59
def prefixEnd_657439 : Nat := 4983230072969 + 3 ^ 40 * 657439 * 2
def baseEnd_657439 : Nat := 337582208011358500588999

theorem tailTrace_657439 : CollatzResearch.WordTrace tailWord_657439 prefixEnd_657439 337582208011358500588999 := by
  unfold tailWord_657439
  simp only [CollatzResearch.WordTrace]
  refine ⟨23978770265218259487111371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15985846843478839658074247 23978770265218259487111371)
  ·
    refine ⟨35968155397827389230667057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23978770265218259487111371 35968155397827389230667057)
    ·
      refine ⟨26976116548370541923000293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35968155397827389230667057 26976116548370541923000293)
      ·
        refine ⟨5058021852819476610562555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26976116548370541923000293 5058021852819476610562555)
        ·
          refine ⟨7587032779229214915843833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5058021852819476610562555 7587032779229214915843833)
          ·
            refine ⟨5690274584421911186882875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7587032779229214915843833 5690274584421911186882875)
            ·
              refine ⟨8535411876632866780324313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5690274584421911186882875 8535411876632866780324313)
              ·
                refine ⟨6401558907474650085243235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8535411876632866780324313 6401558907474650085243235)
                ·
                  refine ⟨9602338361211975127864853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6401558907474650085243235 9602338361211975127864853)
                  ·
                    refine ⟨450109610681811334118665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9602338361211975127864853 450109610681811334118665)
                    ·
                      refine ⟨337582208011358500588999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 450109610681811334118665 337582208011358500588999)
                      ·
                        rfl

theorem cell23_657439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_657439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657439 prefixEnd_657439 := by exact prefixLift 657439
  have htrace : WordTrace (prefixWord ++ tailWord_657439) baseStart_657439 baseEnd_657439 := by
    simpa [prefixWord, tailWord_657439, baseEnd_657439] using wordTrace_append hprefix tailTrace_657439
  have hstable : (prefixWord ++ tailWord_657439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657439).length < 2 ^ (prefixWord ++ tailWord_657439).sum := by decide
  have hdescent : baseEnd_657439 < baseStart_657439 := by decide
  rcases family_descends (prefixWord ++ tailWord_657439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657459 : List Nat := [1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 3]
def baseStart_657459 : Nat := 118140960795 + 657459 * 2 ^ 59
def prefixEnd_657459 : Nat := 4983230072969 + 3 ^ 40 * 657459 * 2
def baseEnd_657459 : Nat := 337592477624448422338907

theorem tailTrace_657459 : CollatzResearch.WordTrace tailWord_657459 prefixEnd_657459 337592477624448422338907 := by
  unfold tailWord_657459
  simp only [CollatzResearch.WordTrace]
  refine ⟨23979499725145802902839431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15986333150097201935226287 23979499725145802902839431)
  ·
    refine ⟨35969249587718704354259147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23979499725145802902839431 35969249587718704354259147)
    ·
      refine ⟨53953874381578056531388721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35969249587718704354259147 53953874381578056531388721)
      ·
        refine ⟨40465405786183542398541541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53953874381578056531388721 40465405786183542398541541)
        ·
          refine ⟨7587263584909414199726539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40465405786183542398541541 7587263584909414199726539)
          ·
            refine ⟨11380895377364121299589809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7587263584909414199726539 11380895377364121299589809)
            ·
              refine ⟨8535671533023090974692357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11380895377364121299589809 8535671533023090974692357)
              ·
                refine ⟨1600438412441829557754817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8535671533023090974692357 1600438412441829557754817)
                ·
                  refine ⟨1200328809331372168316113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1600438412441829557754817 1200328809331372168316113)
                  ·
                    refine ⟨900246606998529126237085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1200328809331372168316113 900246606998529126237085)
                    ·
                      refine ⟨337592477624448422338907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 900246606998529126237085 337592477624448422338907)
                      ·
                        rfl

theorem cell23_657459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 3].length) (baseStart_657459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657459 prefixEnd_657459 := by exact prefixLift 657459
  have htrace : WordTrace (prefixWord ++ tailWord_657459) baseStart_657459 baseEnd_657459 := by
    simpa [prefixWord, tailWord_657459, baseEnd_657459] using wordTrace_append hprefix tailTrace_657459
  have hstable : (prefixWord ++ tailWord_657459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657459).length < 2 ^ (prefixWord ++ tailWord_657459).sum := by decide
  have hdescent : baseEnd_657459 < baseStart_657459 := by decide
  rcases family_descends (prefixWord ++ tailWord_657459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657482 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_657482 : Nat := 118140960795 + 657482 * 2 ^ 59
def prefixEnd_657482 : Nat := 4983230072969 + 3 ^ 40 * 657482 * 2
def baseEnd_657482 : Nat := 337604287679501832351301

theorem tailTrace_657482 : CollatzResearch.WordTrace tailWord_657482 prefixEnd_657482 337604287679501832351301 := by
  unfold tailWord_657482
  simp only [CollatzResearch.WordTrace]
  refine ⟨5995084651015619457731675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15986892402708318553951133 5995084651015619457731675)
  ·
    refine ⟨8992626976523429186597513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5995084651015619457731675 8992626976523429186597513)
    ·
      refine ⟨6744470232392571889948135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8992626976523429186597513 6744470232392571889948135)
      ·
        refine ⟨10116705348588857834922203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6744470232392571889948135 10116705348588857834922203)
        ·
          refine ⟨15175058022883286752383305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10116705348588857834922203 15175058022883286752383305)
          ·
            refine ⟨11381293517162465064287479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15175058022883286752383305 11381293517162465064287479)
            ·
              refine ⟨17071940275743697596431219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11381293517162465064287479 17071940275743697596431219)
              ·
                refine ⟨25607910413615546394646829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17071940275743697596431219 25607910413615546394646829)
                ·
                  refine ⟨9602966405105829897992561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25607910413615546394646829 9602966405105829897992561)
                  ·
                    refine ⟨7202224803829372423494421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9602966405105829897992561 7202224803829372423494421)
                    ·
                      refine ⟨337604287679501832351301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7202224803829372423494421 337604287679501832351301)
                      ·
                        rfl

theorem cell23_657482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_657482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657482 prefixEnd_657482 := by exact prefixLift 657482
  have htrace : WordTrace (prefixWord ++ tailWord_657482) baseStart_657482 baseEnd_657482 := by
    simpa [prefixWord, tailWord_657482, baseEnd_657482] using wordTrace_append hprefix tailTrace_657482
  have hstable : (prefixWord ++ tailWord_657482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657482).length < 2 ^ (prefixWord ++ tailWord_657482).sum := by decide
  have hdescent : baseEnd_657482 < baseStart_657482 := by decide
  rcases family_descends (prefixWord ++ tailWord_657482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657500 : List Nat := [2, 2, 4, 1, 1, 4, 1, 3, 1, 4]
def baseStart_657500 : Nat := 118140960795 + 657500 * 2 ^ 59
def prefixEnd_657500 : Nat := 4983230072969 + 3 ^ 40 * 657500 * 2
def baseEnd_657500 : Nat := 112537843443760920642073

theorem tailTrace_657500 : CollatzResearch.WordTrace tailWord_657500 prefixEnd_657500 112537843443760920642073 := by
  unfold tailWord_657500
  simp only [CollatzResearch.WordTrace]
  refine ⟨11990497558998633452540977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15987330078664844603387969 11990497558998633452540977)
  ·
    refine ⟨8992873169248975089405733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11990497558998633452540977 8992873169248975089405733)
    ·
      refine ⟨1686163719234182829263575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8992873169248975089405733 1686163719234182829263575)
      ·
        refine ⟨2529245578851274243895363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1686163719234182829263575 2529245578851274243895363)
        ·
          refine ⟨3793868368276911365843045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2529245578851274243895363 3793868368276911365843045)
          ·
            refine ⟨711350319051920881095571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3793868368276911365843045 711350319051920881095571)
            ·
              refine ⟨1067025478577881321643357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 711350319051920881095571 1067025478577881321643357)
              ·
                refine ⟨400134554466705495616259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1067025478577881321643357 400134554466705495616259)
                ·
                  refine ⟨600201831700058243424389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 400134554466705495616259 600201831700058243424389)
                  ·
                    refine ⟨112537843443760920642073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 600201831700058243424389 112537843443760920642073)
                    ·
                      rfl

theorem cell23_657500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_657500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657500 prefixEnd_657500 := by exact prefixLift 657500
  have htrace : WordTrace (prefixWord ++ tailWord_657500) baseStart_657500 baseEnd_657500 := by
    simpa [prefixWord, tailWord_657500, baseEnd_657500] using wordTrace_append hprefix tailTrace_657500
  have hstable : (prefixWord ++ tailWord_657500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657500).length < 2 ^ (prefixWord ++ tailWord_657500).sum := by decide
  have hdescent : baseEnd_657500 < baseStart_657500 := by decide
  rcases family_descends (prefixWord ++ tailWord_657500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657516 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 4, 3, 2]
def baseStart_657516 : Nat := 118140960795 + 657516 * 2 ^ 59
def prefixEnd_657516 : Nat := 4983230072969 + 3 ^ 40 * 657516 * 2
def baseEnd_657516 : Nat := 337621746021754699326145

theorem tailTrace_657516 : CollatzResearch.WordTrace tailWord_657516 prefixEnd_657516 337621746021754699326145 := by
  unfold tailWord_657516
  simp only [CollatzResearch.WordTrace]
  refine ⟨11990789342969650818832201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15987719123959534425109601 11990789342969650818832201)
  ·
    refine ⟨8993092007227238114124151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11990789342969650818832201 8993092007227238114124151)
    ·
      refine ⟨13489638010840857171186227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8993092007227238114124151 13489638010840857171186227)
      ·
        refine ⟨20234457016261285756779341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13489638010840857171186227 20234457016261285756779341)
        ·
          refine ⟨7587921381097982158792253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20234457016261285756779341 7587921381097982158792253)
          ·
            refine ⟨2845470517911743309547095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7587921381097982158792253 2845470517911743309547095)
            ·
              refine ⟨4268205776867614964320643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2845470517911743309547095 4268205776867614964320643)
              ·
                refine ⟨6402308665301422446480965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4268205776867614964320643 6402308665301422446480965)
                ·
                  refine ⟨1200432874744016708715181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6402308665301422446480965 1200432874744016708715181)
                  ·
                    refine ⟨450162328029006265768193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1200432874744016708715181 450162328029006265768193)
                    ·
                      refine ⟨337621746021754699326145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 450162328029006265768193 337621746021754699326145)
                      ·
                        rfl

theorem cell23_657516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 3, 2].length) (baseStart_657516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657516 prefixEnd_657516 := by exact prefixLift 657516
  have htrace : WordTrace (prefixWord ++ tailWord_657516) baseStart_657516 baseEnd_657516 := by
    simpa [prefixWord, tailWord_657516, baseEnd_657516] using wordTrace_append hprefix tailTrace_657516
  have hstable : (prefixWord ++ tailWord_657516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657516).length < 2 ^ (prefixWord ++ tailWord_657516).sum := by decide
  have hdescent : baseEnd_657516 < baseStart_657516 := by decide
  rcases family_descends (prefixWord ++ tailWord_657516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657546 : List Nat := [3, 1, 2, 3, 1, 3, 1, 1, 3, 1, 4]
def baseStart_657546 : Nat := 118140960795 + 657546 * 2 ^ 59
def prefixEnd_657546 : Nat := 4983230072969 + 3 ^ 40 * 657546 * 2
def baseEnd_657546 : Nat := 337637150441389581951007

theorem tailTrace_657546 : CollatzResearch.WordTrace tailWord_657546 prefixEnd_657546 337637150441389581951007 := by
  unfold tailWord_657546
  simp only [CollatzResearch.WordTrace]
  refine ⟨5995668218957654190314123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15988448583887077840837661 5995668218957654190314123)
  ·
    refine ⟨8993502328436481285471185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5995668218957654190314123 8993502328436481285471185)
    ·
      refine ⟨6745126746327360964103389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8993502328436481285471185 6745126746327360964103389)
      ·
        refine ⟨2529422529872760361538771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6745126746327360964103389 2529422529872760361538771)
        ·
          refine ⟨3794133794809140542308157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2529422529872760361538771 3794133794809140542308157)
          ·
            refine ⟨1422800173053427703365559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3794133794809140542308157 1422800173053427703365559)
            ·
              refine ⟨2134200259580141555048339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422800173053427703365559 2134200259580141555048339)
              ·
                refine ⟨3201300389370212332572509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2134200259580141555048339 3201300389370212332572509)
                ·
                  refine ⟨1200487646013829624714691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3201300389370212332572509 1200487646013829624714691)
                  ·
                    refine ⟨1800731469020744437072037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1200487646013829624714691 1800731469020744437072037)
                    ·
                      refine ⟨337637150441389581951007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1800731469020744437072037 337637150441389581951007)
                      ·
                        rfl

theorem cell23_657546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_657546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657546 prefixEnd_657546 := by exact prefixLift 657546
  have htrace : WordTrace (prefixWord ++ tailWord_657546) baseStart_657546 baseEnd_657546 := by
    simpa [prefixWord, tailWord_657546, baseEnd_657546] using wordTrace_append hprefix tailTrace_657546
  have hstable : (prefixWord ++ tailWord_657546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657546).length < 2 ^ (prefixWord ++ tailWord_657546).sum := by decide
  have hdescent : baseEnd_657546 < baseStart_657546 := by decide
  rcases family_descends (prefixWord ++ tailWord_657546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657550 : List Nat := [4, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2]
def baseStart_657550 : Nat := 118140960795 + 657550 * 2 ^ 59
def prefixEnd_657550 : Nat := 4983230072969 + 3 ^ 40 * 657550 * 2
def baseEnd_657550 : Nat := 337639204364007566300989

theorem tailTrace_657550 : CollatzResearch.WordTrace tailWord_657550 prefixEnd_657550 337639204364007566300989 := by
  unfold tailWord_657550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2997852345977015680550263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15988545845210750296268069 2997852345977015680550263)
  ·
    refine ⟨4496778518965523520825395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2997852345977015680550263 4496778518965523520825395)
    ·
      refine ⟨6745167778448285281238093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4496778518965523520825395 6745167778448285281238093)
      ·
        refine ⟨2529437916918106980464285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6745167778448285281238093 2529437916918106980464285)
        ·
          refine ⟨948539218844290117674107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2529437916918106980464285 948539218844290117674107)
          ·
            refine ⟨1422808828266435176511161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948539218844290117674107 1422808828266435176511161)
            ·
              refine ⟨1067106621199826382383371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1422808828266435176511161 1067106621199826382383371)
              ·
                refine ⟨1600659931799739573575057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1067106621199826382383371 1600659931799739573575057)
                ·
                  refine ⟨1200494948849804680181293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1600659931799739573575057 1200494948849804680181293)
                  ·
                    refine ⟨450185605818676755067985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1200494948849804680181293 450185605818676755067985)
                    ·
                      refine ⟨337639204364007566300989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 450185605818676755067985 337639204364007566300989)
                      ·
                        rfl

theorem cell23_657550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_657550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657550 prefixEnd_657550 := by exact prefixLift 657550
  have htrace : WordTrace (prefixWord ++ tailWord_657550) baseStart_657550 baseEnd_657550 := by
    simpa [prefixWord, tailWord_657550, baseEnd_657550] using wordTrace_append hprefix tailTrace_657550
  have hstable : (prefixWord ++ tailWord_657550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657550).length < 2 ^ (prefixWord ++ tailWord_657550).sum := by decide
  have hdescent : baseEnd_657550 < baseStart_657550 := by decide
  rcases family_descends (prefixWord ++ tailWord_657550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657552 : List Nat := [2, 1, 1, 1, 1, 1, 5, 11]
def baseStart_657552 : Nat := 118140960795 + 657552 * 2 ^ 59
def prefixEnd_657552 : Nat := 4983230072969 + 3 ^ 40 * 657552 * 2
def baseEnd_657552 : Nat := 12505193752789502165777

theorem tailTrace_657552 : CollatzResearch.WordTrace tailWord_657552 prefixEnd_657552 12505193752789502165777 := by
  unfold tailWord_657552
  simp only [CollatzResearch.WordTrace]
  refine ⟨11991445856904439892987455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15988594475872586523983273 11991445856904439892987455)
  ·
    refine ⟨17987168785356659839481183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11991445856904439892987455 17987168785356659839481183)
    ·
      refine ⟨26980753178034989759221775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17987168785356659839481183 26980753178034989759221775)
      ·
        refine ⟨40471129767052484638832663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26980753178034989759221775 40471129767052484638832663)
        ·
          refine ⟨60706694650578726958248995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40471129767052484638832663 60706694650578726958248995)
          ·
            refine ⟨91060041975868090437373493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60706694650578726958248995 91060041975868090437373493)
            ·
              refine ⟨8536878935237633478503765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91060041975868090437373493 8536878935237633478503765)
              ·
                refine ⟨12505193752789502165777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 8536878935237633478503765 12505193752789502165777)
                ·
                  rfl

theorem cell23_657552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 11].length) (baseStart_657552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657552 prefixEnd_657552 := by exact prefixLift 657552
  have htrace : WordTrace (prefixWord ++ tailWord_657552) baseStart_657552 baseEnd_657552 := by
    simpa [prefixWord, tailWord_657552, baseEnd_657552] using wordTrace_append hprefix tailTrace_657552
  have hstable : (prefixWord ++ tailWord_657552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657552).length < 2 ^ (prefixWord ++ tailWord_657552).sum := by decide
  have hdescent : baseEnd_657552 < baseStart_657552 := by decide
  rcases family_descends (prefixWord ++ tailWord_657552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657719 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 2, 8]
def baseStart_657719 : Nat := 118140960795 + 657719 * 2 ^ 59
def prefixEnd_657719 : Nat := 4983230072969 + 3 ^ 40 * 657719 * 2
def baseEnd_657719 : Nat := 112575327531539135029237

theorem tailTrace_657719 : CollatzResearch.WordTrace tailWord_657719 prefixEnd_657719 112575327531539135029237 := by
  unfold tailWord_657719
  simp only [CollatzResearch.WordTrace]
  refine ⟨23988982704203867307304211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15992655136135911538202807 23988982704203867307304211)
  ·
    refine ⟨35983474056305800960956317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23988982704203867307304211 35983474056305800960956317)
    ·
      refine ⟨13493802771114675360358619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35983474056305800960956317 13493802771114675360358619)
      ·
        refine ⟨20240704156672013040537929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13493802771114675360358619 20240704156672013040537929)
        ·
          refine ⟨15180528117504009780403447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20240704156672013040537929 15180528117504009780403447)
          ·
            refine ⟨22770792176256014670605171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15180528117504009780403447 22770792176256014670605171)
            ·
              refine ⟨34156188264384022005907757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22770792176256014670605171 34156188264384022005907757)
              ·
                refine ⟨12808570599144008252215409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34156188264384022005907757 12808570599144008252215409)
                ·
                  refine ⟨9606427949358006189161557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12808570599144008252215409 9606427949358006189161557)
                  ·
                    refine ⟨112575327531539135029237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9606427949358006189161557 112575327531539135029237)
                    ·
                      rfl

theorem cell23_657719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_657719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657719 prefixEnd_657719 := by exact prefixLift 657719
  have htrace : WordTrace (prefixWord ++ tailWord_657719) baseStart_657719 baseEnd_657719 := by
    simpa [prefixWord, tailWord_657719, baseEnd_657719] using wordTrace_append hprefix tailTrace_657719
  have hstable : (prefixWord ++ tailWord_657719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657719).length < 2 ^ (prefixWord ++ tailWord_657719).sum := by decide
  have hdescent : baseEnd_657719 < baseStart_657719 := by decide
  rcases family_descends (prefixWord ++ tailWord_657719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657760 : List Nat := [2, 1, 1, 3, 5, 1, 1, 1, 2, 4, 2]
def baseStart_657760 : Nat := 118140960795 + 657760 * 2 ^ 59
def prefixEnd_657760 : Nat := 4983230072969 + 3 ^ 40 * 657760 * 2
def baseEnd_657760 : Nat := 337747035301451744675023

theorem tailTrace_657760 : CollatzResearch.WordTrace tailWord_657760 prefixEnd_657760 337747035301451744675023 := by
  unfold tailWord_657760
  simp only [CollatzResearch.WordTrace]
  refine ⟨11995239048527665654773367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15993652064703554206364489 11995239048527665654773367)
  ·
    refine ⟨17992858572791498482160051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11995239048527665654773367 17992858572791498482160051)
    ·
      refine ⟨26989287859187247723240077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17992858572791498482160051 26989287859187247723240077)
      ·
        refine ⟨10120982947195217896215029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26989287859187247723240077 10120982947195217896215029)
        ·
          refine ⟨948842151299551677770159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10120982947195217896215029 948842151299551677770159)
          ·
            refine ⟨1423263226949327516655239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948842151299551677770159 1423263226949327516655239)
            ·
              refine ⟨2134894840423991274982859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1423263226949327516655239 2134894840423991274982859)
              ·
                refine ⟨3202342260635986912474289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2134894840423991274982859 3202342260635986912474289)
                ·
                  refine ⟨2401756695476990184355717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3202342260635986912474289 2401756695476990184355717)
                  ·
                    refine ⟨450329380401935659566697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2401756695476990184355717 450329380401935659566697)
                    ·
                      refine ⟨337747035301451744675023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 450329380401935659566697 337747035301451744675023)
                      ·
                        rfl

theorem cell23_657760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_657760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657760 prefixEnd_657760 := by exact prefixLift 657760
  have htrace : WordTrace (prefixWord ++ tailWord_657760) baseStart_657760 baseEnd_657760 := by
    simpa [prefixWord, tailWord_657760, baseEnd_657760] using wordTrace_append hprefix tailTrace_657760
  have hstable : (prefixWord ++ tailWord_657760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657760).length < 2 ^ (prefixWord ++ tailWord_657760).sum := by decide
  have hdescent : baseEnd_657760 < baseStart_657760 := by decide
  rcases family_descends (prefixWord ++ tailWord_657760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657770 : List Nat := [3, 1, 3, 3, 1, 2, 1, 2, 3, 4]
def baseStart_657770 : Nat := 118140960795 + 657770 * 2 ^ 59
def prefixEnd_657770 : Nat := 4983230072969 + 3 ^ 40 * 657770 * 2
def baseEnd_657770 : Nat := 112584056702665568516659

theorem tailTrace_657770 : CollatzResearch.WordTrace tailWord_657770 prefixEnd_657770 112584056702665568516659 := by
  unfold tailWord_657770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5997710706754775754352691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15993895218012735344940509 5997710706754775754352691)
  ·
    refine ⟨8996566060132163631529037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5997710706754775754352691 8996566060132163631529037)
    ·
      refine ⟨3373712272549561361823389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8996566060132163631529037 3373712272549561361823389)
      ·
        refine ⟨1265142102206085510683771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3373712272549561361823389 1265142102206085510683771)
        ·
          refine ⟨1897713153309128266025657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1265142102206085510683771 1897713153309128266025657)
          ·
            refine ⟨1423284864981846199519243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1897713153309128266025657 1423284864981846199519243)
            ·
              refine ⟨2134927297472769299278865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1423284864981846199519243 2134927297472769299278865)
              ·
                refine ⟨1601195473104576974459149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2134927297472769299278865 1601195473104576974459149)
                ·
                  refine ⟨600448302414216365422181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1601195473104576974459149 600448302414216365422181)
                  ·
                    refine ⟨112584056702665568516659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 600448302414216365422181 112584056702665568516659)
                    ·
                      rfl

theorem cell23_657770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_657770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657770 prefixEnd_657770 := by exact prefixLift 657770
  have htrace : WordTrace (prefixWord ++ tailWord_657770) baseStart_657770 baseEnd_657770 := by
    simpa [prefixWord, tailWord_657770, baseEnd_657770] using wordTrace_append hprefix tailTrace_657770
  have hstable : (prefixWord ++ tailWord_657770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657770).length < 2 ^ (prefixWord ++ tailWord_657770).sum := by decide
  have hdescent : baseEnd_657770 < baseStart_657770 := by decide
  rcases family_descends (prefixWord ++ tailWord_657770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657836 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 5]
def baseStart_657836 : Nat := 118140960795 + 657836 * 2 ^ 59
def prefixEnd_657836 : Nat := 4983230072969 + 3 ^ 40 * 657836 * 2
def baseEnd_657836 : Nat := 337786059831193447324673

theorem tailTrace_657836 : CollatzResearch.WordTrace tailWord_657836 prefixEnd_657836 337786059831193447324673 := by
  unfold tailWord_657836
  simp only [CollatzResearch.WordTrace]
  refine ⟨11996625022389998144656681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15995500029853330859542241 11996625022389998144656681)
  ·
    refine ⟨8997468766792498608492511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11996625022389998144656681 8997468766792498608492511)
    ·
      refine ⟨13496203150188747912738767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8997468766792498608492511 13496203150188747912738767)
      ·
        refine ⟨20244304725283121869108151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13496203150188747912738767 20244304725283121869108151)
        ·
          refine ⟨30366457087924682803662227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20244304725283121869108151 30366457087924682803662227)
          ·
            refine ⟨45549685631887024205493341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30366457087924682803662227 45549685631887024205493341)
            ·
              refine ⟨17081132111957634077060003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45549685631887024205493341 17081132111957634077060003)
              ·
                refine ⟨25621698167936451115590005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17081132111957634077060003 25621698167936451115590005)
                ·
                  refine ⟨2402034203244042292086563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25621698167936451115590005 2402034203244042292086563)
                  ·
                    refine ⟨3603051304866063438129845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2402034203244042292086563 3603051304866063438129845)
                    ·
                      refine ⟨337786059831193447324673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3603051304866063438129845 337786059831193447324673)
                      ·
                        rfl

theorem cell23_657836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_657836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657836 prefixEnd_657836 := by exact prefixLift 657836
  have htrace : WordTrace (prefixWord ++ tailWord_657836) baseStart_657836 baseEnd_657836 := by
    simpa [prefixWord, tailWord_657836, baseEnd_657836] using wordTrace_append hprefix tailTrace_657836
  have hstable : (prefixWord ++ tailWord_657836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657836).length < 2 ^ (prefixWord ++ tailWord_657836).sum := by decide
  have hdescent : baseEnd_657836 < baseStart_657836 := by decide
  rcases family_descends (prefixWord ++ tailWord_657836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657850 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2]
def baseStart_657850 : Nat := 118140960795 + 657850 * 2 ^ 59
def prefixEnd_657850 : Nat := 4983230072969 + 3 ^ 40 * 657850 * 2
def baseEnd_657850 : Nat := 337793248560356392549609

theorem tailTrace_657850 : CollatzResearch.WordTrace tailWord_657850 prefixEnd_657850 337793248560356392549609 := by
  unfold tailWord_657850
  simp only [CollatzResearch.WordTrace]
  refine ⟨5998440166682319170080751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15995840444486184453548669 5998440166682319170080751)
  ·
    refine ⟨8997660250023478755121127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5998440166682319170080751 8997660250023478755121127)
    ·
      refine ⟨13496490375035218132681691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8997660250023478755121127 13496490375035218132681691)
      ·
        refine ⟨20244735562552827199022537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13496490375035218132681691 20244735562552827199022537)
        ·
          refine ⟨15183551671914620399266903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20244735562552827199022537 15183551671914620399266903)
          ·
            refine ⟨22775327507871930598900355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15183551671914620399266903 22775327507871930598900355)
            ·
              refine ⟨34162991261807895898350533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22775327507871930598900355 34162991261807895898350533)
              ·
                refine ⟨6405560861588980480940725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34162991261807895898350533 6405560861588980480940725)
                ·
                  refine ⟨600521330773966920088193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6405560861588980480940725 600521330773966920088193)
                  ·
                    refine ⟨450390998080475190066145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 600521330773966920088193 450390998080475190066145)
                    ·
                      refine ⟨337793248560356392549609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 450390998080475190066145 337793248560356392549609)
                      ·
                        rfl

theorem cell23_657850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2].length) (baseStart_657850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657850 prefixEnd_657850 := by exact prefixLift 657850
  have htrace : WordTrace (prefixWord ++ tailWord_657850) baseStart_657850 baseEnd_657850 := by
    simpa [prefixWord, tailWord_657850, baseEnd_657850] using wordTrace_append hprefix tailTrace_657850
  have hstable : (prefixWord ++ tailWord_657850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657850).length < 2 ^ (prefixWord ++ tailWord_657850).sum := by decide
  have hdescent : baseEnd_657850 < baseStart_657850 := by decide
  rcases family_descends (prefixWord ++ tailWord_657850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657853 : List Nat := [1, 4, 1, 2, 2, 2, 1, 3, 1, 1, 5]
def baseStart_657853 : Nat := 118140960795 + 657853 * 2 ^ 59
def prefixEnd_657853 : Nat := 4983230072969 + 3 ^ 40 * 657853 * 2
def baseEnd_657853 : Nat := 337794789002319880812095

theorem tailTrace_657853 : CollatzResearch.WordTrace tailWord_657853 prefixEnd_657853 337794789002319880812095 := by
  unfold tailWord_657853
  simp only [CollatzResearch.WordTrace]
  refine ⟨23993870085718408192682213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15995913390478938795121475 23993870085718408192682213)
  ·
    refine ⟨4498850641072201536127915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23993870085718408192682213 4498850641072201536127915)
    ·
      refine ⟨6748275961608302304191873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4498850641072201536127915 6748275961608302304191873)
      ·
        refine ⟨5061206971206226728143905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6748275961608302304191873 5061206971206226728143905)
        ·
          refine ⟨3795905228404670046107929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5061206971206226728143905 3795905228404670046107929)
          ·
            refine ⟨2846928921303502534580947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3795905228404670046107929 2846928921303502534580947)
            ·
              refine ⟨4270393381955253801871421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2846928921303502534580947 4270393381955253801871421)
              ·
                refine ⟨1601397518233220175701783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4270393381955253801871421 1601397518233220175701783)
                ·
                  refine ⟨2402096277349830263552675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1601397518233220175701783 2402096277349830263552675)
                  ·
                    refine ⟨3603144416024745395329013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2402096277349830263552675 3603144416024745395329013)
                    ·
                      refine ⟨337794789002319880812095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3603144416024745395329013 337794789002319880812095)
                      ·
                        rfl

theorem cell23_657853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_657853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657853 prefixEnd_657853 := by exact prefixLift 657853
  have htrace : WordTrace (prefixWord ++ tailWord_657853) baseStart_657853 baseEnd_657853 := by
    simpa [prefixWord, tailWord_657853, baseEnd_657853] using wordTrace_append hprefix tailTrace_657853
  have hstable : (prefixWord ++ tailWord_657853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657853).length < 2 ^ (prefixWord ++ tailWord_657853).sum := by decide
  have hdescent : baseEnd_657853 < baseStart_657853 := by decide
  rcases family_descends (prefixWord ++ tailWord_657853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657877 : List Nat := [1, 3, 2, 3, 1, 2, 4, 1, 2, 4]
def baseStart_657877 : Nat := 118140960795 + 657877 * 2 ^ 59
def prefixEnd_657877 : Nat := 4983230072969 + 3 ^ 40 * 657877 * 2
def baseEnd_657877 : Nat := 112602370846009262303995

theorem tailTrace_657877 : CollatzResearch.WordTrace tailWord_657877 prefixEnd_657877 112602370846009262303995 := by
  unfold tailWord_657877
  simp only [CollatzResearch.WordTrace]
  refine ⟨23994745437631460291555885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15996496958420973527703923 23994745437631460291555885)
  ·
    refine ⟨8998029539111797609333457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23994745437631460291555885 8998029539111797609333457)
    ·
      refine ⟨6748522154333848207000093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8998029539111797609333457 6748522154333848207000093)
      ·
        refine ⟨2530695807875193077625035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6748522154333848207000093 2530695807875193077625035)
        ·
          refine ⟨3796043711812789616437553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2530695807875193077625035 3796043711812789616437553)
          ·
            refine ⟨2847032783859592212328165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3796043711812789616437553 2847032783859592212328165)
            ·
              refine ⟨533818646973673539811531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2847032783859592212328165 533818646973673539811531)
              ·
                refine ⟨800727970460510309717297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 533818646973673539811531 800727970460510309717297)
                ·
                  refine ⟨600545977845382732287973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 800727970460510309717297 600545977845382732287973)
                  ·
                    refine ⟨112602370846009262303995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 600545977845382732287973 112602370846009262303995)
                    ·
                      rfl

theorem cell23_657877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_657877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657877 prefixEnd_657877 := by exact prefixLift 657877
  have htrace : WordTrace (prefixWord ++ tailWord_657877) baseStart_657877 baseEnd_657877 := by
    simpa [prefixWord, tailWord_657877, baseEnd_657877] using wordTrace_append hprefix tailTrace_657877
  have hstable : (prefixWord ++ tailWord_657877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657877).length < 2 ^ (prefixWord ++ tailWord_657877).sum := by decide
  have hdescent : baseEnd_657877 < baseStart_657877 := by decide
  rcases family_descends (prefixWord ++ tailWord_657877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657887 : List Nat := [1, 1, 2, 3, 3, 4, 1, 2, 1, 2, 3]
def baseStart_657887 : Nat := 118140960795 + 657887 * 2 ^ 59
def prefixEnd_657887 : Nat := 4983230072969 + 3 ^ 40 * 657887 * 2
def baseEnd_657887 : Nat := 337812247344572747786939

theorem tailTrace_657887 : CollatzResearch.WordTrace tailWord_657887 prefixEnd_657887 337812247344572747786939 := by
  unfold tailWord_657887
  simp only [CollatzResearch.WordTrace]
  refine ⟨23995110167595231999419915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15996740111730154666279943 23995110167595231999419915)
  ·
    refine ⟨35992665251392847999129873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23995110167595231999419915 35992665251392847999129873)
    ·
      refine ⟨26994498938544635999347405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35992665251392847999129873 26994498938544635999347405)
      ·
        refine ⟨10122937101954238499755277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26994498938544635999347405 10122937101954238499755277)
        ·
          refine ⟨3796101413232839437408229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10122937101954238499755277 3796101413232839437408229)
          ·
            refine ⟨711769014981157394514043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3796101413232839437408229 711769014981157394514043)
            ·
              refine ⟨1067653522471736091771065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 711769014981157394514043 1067653522471736091771065)
              ·
                refine ⟨800740141853802068828299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1067653522471736091771065 800740141853802068828299)
                ·
                  refine ⟨1201110212780703103242449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 800740141853802068828299 1201110212780703103242449)
                  ·
                    refine ⟨900832659585527327431837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1201110212780703103242449 900832659585527327431837)
                    ·
                      refine ⟨337812247344572747786939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 900832659585527327431837 337812247344572747786939)
                      ·
                        rfl

theorem cell23_657887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_657887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657887 prefixEnd_657887 := by exact prefixLift 657887
  have htrace : WordTrace (prefixWord ++ tailWord_657887) baseStart_657887 baseEnd_657887 := by
    simpa [prefixWord, tailWord_657887, baseEnd_657887] using wordTrace_append hprefix tailTrace_657887
  have hstable : (prefixWord ++ tailWord_657887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657887).length < 2 ^ (prefixWord ++ tailWord_657887).sum := by decide
  have hdescent : baseEnd_657887 < baseStart_657887 := by decide
  rcases family_descends (prefixWord ++ tailWord_657887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657917 : List Nat := [1, 4, 1, 1, 1, 3, 4, 2, 2, 1, 3]
def baseStart_657917 : Nat := 118140960795 + 657917 * 2 ^ 59
def prefixEnd_657917 : Nat := 4983230072969 + 3 ^ 40 * 657917 * 2
def baseEnd_657917 : Nat := 337827651764207630411801

theorem tailTrace_657917 : CollatzResearch.WordTrace tailWord_657917 prefixEnd_657917 337827651764207630411801 := by
  unfold tailWord_657917
  simp only [CollatzResearch.WordTrace]
  refine ⟨23996204357486547123012005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15997469571657698082008003 23996204357486547123012005)
  ·
    refine ⟨4499288317028727585564751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23996204357486547123012005 4499288317028727585564751)
    ·
      refine ⟨6748932475543091378347127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4499288317028727585564751 6748932475543091378347127)
      ·
        refine ⟨10123398713314637067520691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6748932475543091378347127 10123398713314637067520691)
        ·
          refine ⟨15185098069971955601281037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10123398713314637067520691 15185098069971955601281037)
          ·
            refine ⟨5694411776239483350480389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15185098069971955601281037 5694411776239483350480389)
            ·
              refine ⟨1067702208044903128215073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5694411776239483350480389 1067702208044903128215073)
              ·
                refine ⟨800776656033677346161305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1067702208044903128215073 800776656033677346161305)
                ·
                  refine ⟨600582492025258009620979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 800776656033677346161305 600582492025258009620979)
                  ·
                    refine ⟨900873738037887014431469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 600582492025258009620979 900873738037887014431469)
                    ·
                      refine ⟨337827651764207630411801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 900873738037887014431469 337827651764207630411801)
                      ·
                        rfl

theorem cell23_657917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_657917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657917 prefixEnd_657917 := by exact prefixLift 657917
  have htrace : WordTrace (prefixWord ++ tailWord_657917) baseStart_657917 baseEnd_657917 := by
    simpa [prefixWord, tailWord_657917, baseEnd_657917] using wordTrace_append hprefix tailTrace_657917
  have hstable : (prefixWord ++ tailWord_657917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657917).length < 2 ^ (prefixWord ++ tailWord_657917).sum := by decide
  have hdescent : baseEnd_657917 < baseStart_657917 := by decide
  rcases family_descends (prefixWord ++ tailWord_657917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657953 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 1, 4, 4]
def baseStart_657953 : Nat := 118140960795 + 657953 * 2 ^ 59
def prefixEnd_657953 : Nat := 4983230072969 + 3 ^ 40 * 657953 * 2
def baseEnd_657953 : Nat := 337846137067769489561635

theorem tailTrace_657953 : CollatzResearch.WordTrace tailWord_657953 prefixEnd_657953 337846137067769489561635 := by
  unfold tailWord_657953
  simp only [CollatzResearch.WordTrace]
  refine ⟨23997517385356125271322513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15998344923570750180881675 23997517385356125271322513)
  ·
    refine ⟨17998138039017093953491885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23997517385356125271322513 17998138039017093953491885)
    ·
      refine ⟨6749301764631410232559457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17998138039017093953491885 6749301764631410232559457)
      ·
        refine ⟨5061976323473557674419593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6749301764631410232559457 5061976323473557674419593)
        ·
          refine ⟨3796482242605168255814695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5061976323473557674419593 3796482242605168255814695)
          ·
            refine ⟨5694723363907752383722043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3796482242605168255814695 5694723363907752383722043)
            ·
              refine ⟨8542085045861628575583065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5694723363907752383722043 8542085045861628575583065)
              ·
                refine ⟨6406563784396221431687299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8542085045861628575583065 6406563784396221431687299)
                ·
                  refine ⟨9609845676594332147530949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6406563784396221431687299 9609845676594332147530949)
                  ·
                    refine ⟨1801846064361437277662053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9609845676594332147530949 1801846064361437277662053)
                    ·
                      refine ⟨337846137067769489561635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1801846064361437277662053 337846137067769489561635)
                      ·
                        rfl

theorem cell23_657953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_657953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657953 prefixEnd_657953 := by exact prefixLift 657953
  have htrace : WordTrace (prefixWord ++ tailWord_657953) baseStart_657953 baseEnd_657953 := by
    simpa [prefixWord, tailWord_657953, baseEnd_657953] using wordTrace_append hprefix tailTrace_657953
  have hstable : (prefixWord ++ tailWord_657953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657953).length < 2 ^ (prefixWord ++ tailWord_657953).sum := by decide
  have hdescent : baseEnd_657953 < baseStart_657953 := by decide
  rcases family_descends (prefixWord ++ tailWord_657953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657980 : List Nat := [2, 2, 2, 2, 3, 2, 2, 1, 7]
def baseStart_657980 : Nat := 118140960795 + 657980 * 2 ^ 59
def prefixEnd_657980 : Nat := 4983230072969 + 3 ^ 40 * 657980 * 2
def baseEnd_657980 : Nat := 37540000116160098213779

theorem tailTrace_657980 : CollatzResearch.WordTrace tailWord_657980 prefixEnd_657980 37540000116160098213779 := by
  unfold tailWord_657980
  simp only [CollatzResearch.WordTrace]
  refine ⟨11999251078129154441277697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15999001437505539255036929 11999251078129154441277697)
  ·
    refine ⟨8999438308596865830958273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11999251078129154441277697 8999438308596865830958273)
    ·
      refine ⟨6749578731447649373218705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8999438308596865830958273 6749578731447649373218705)
      ·
        refine ⟨5062184048585737029914029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6749578731447649373218705 5062184048585737029914029)
        ·
          refine ⟨1898319018219651386217761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5062184048585737029914029 1898319018219651386217761)
          ·
            refine ⟨1423739263664738539663321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1898319018219651386217761 1423739263664738539663321)
            ·
              refine ⟨1067804447748553904747491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1423739263664738539663321 1067804447748553904747491)
              ·
                refine ⟨1601706671622830857121237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1067804447748553904747491 1601706671622830857121237)
                ·
                  refine ⟨37540000116160098213779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1601706671622830857121237 37540000116160098213779)
                  ·
                    rfl

theorem cell23_657980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 1, 7].length) (baseStart_657980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657980 prefixEnd_657980 := by exact prefixLift 657980
  have htrace : WordTrace (prefixWord ++ tailWord_657980) baseStart_657980 baseEnd_657980 := by
    simpa [prefixWord, tailWord_657980, baseEnd_657980] using wordTrace_append hprefix tailTrace_657980
  have hstable : (prefixWord ++ tailWord_657980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657980).length < 2 ^ (prefixWord ++ tailWord_657980).sum := by decide
  have hdescent : baseEnd_657980 < baseStart_657980 := by decide
  rcases family_descends (prefixWord ++ tailWord_657980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_657991 : List Nat := [1, 1, 4, 1, 4, 2, 3, 1, 2, 2, 2]
def baseStart_657991 : Nat := 118140960795 + 657991 * 2 ^ 59
def prefixEnd_657991 : Nat := 4983230072969 + 3 ^ 40 * 657991 * 2
def baseEnd_657991 : Nat := 337865649332640340886461

theorem tailTrace_657991 : CollatzResearch.WordTrace tailWord_657991 prefixEnd_657991 337865649332640340886461 := by
  unfold tailWord_657991
  simp only [CollatzResearch.WordTrace]
  refine ⟨23998903359218457761205827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15999268906145638507470551 23998903359218457761205827)
  ·
    refine ⟨35998355038827686641808741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23998903359218457761205827 35998355038827686641808741)
    ·
      refine ⟨6749691569780191245339139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35998355038827686641808741 6749691569780191245339139)
      ·
        refine ⟨10124537354670286868008709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6749691569780191245339139 10124537354670286868008709)
        ·
          refine ⟨1898350754000678787751633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10124537354670286868008709 1898350754000678787751633)
          ·
            refine ⟨1423763065500509090813725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1898350754000678787751633 1423763065500509090813725)
            ·
              refine ⟨533911149562690909055147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1423763065500509090813725 533911149562690909055147)
              ·
                refine ⟨800866724344036363582721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 533911149562690909055147 800866724344036363582721)
                ·
                  refine ⟨600650043258027272687041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 800866724344036363582721 600650043258027272687041)
                  ·
                    refine ⟨450487532443520454515281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 600650043258027272687041 450487532443520454515281)
                    ·
                      refine ⟨337865649332640340886461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 450487532443520454515281 337865649332640340886461)
                      ·
                        rfl

theorem cell23_657991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_657991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_657991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_657991 prefixEnd_657991 := by exact prefixLift 657991
  have htrace : WordTrace (prefixWord ++ tailWord_657991) baseStart_657991 baseEnd_657991 := by
    simpa [prefixWord, tailWord_657991, baseEnd_657991] using wordTrace_append hprefix tailTrace_657991
  have hstable : (prefixWord ++ tailWord_657991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_657991).length < 2 ^ (prefixWord ++ tailWord_657991).sum := by decide
  have hdescent : baseEnd_657991 < baseStart_657991 := by decide
  rcases family_descends (prefixWord ++ tailWord_657991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658037 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_658037 : Nat := 118140960795 + 658037 * 2 ^ 59
def prefixEnd_658037 : Nat := 4983230072969 + 3 ^ 40 * 658037 * 2
def baseEnd_658037 : Nat := 337889269442747160911249

theorem tailTrace_658037 : CollatzResearch.WordTrace tailWord_658037 prefixEnd_658037 337889269442747160911249 := by
  unfold tailWord_658037
  simp only [CollatzResearch.WordTrace]
  refine ⟨24000581117051807617380365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16000387411367871744920243 24000581117051807617380365)
  ·
    refine ⟨9000217918894427856517637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24000581117051807617380365 9000217918894427856517637)
    ·
      refine ⟨1687540859792705223097057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9000217918894427856517637 1687540859792705223097057)
      ·
        refine ⟨1265655644844528917322793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1687540859792705223097057 1265655644844528917322793)
        ·
          refine ⟨949241733633396687992095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1265655644844528917322793 949241733633396687992095)
          ·
            refine ⟨1423862600450095031988143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 949241733633396687992095 1423862600450095031988143)
            ·
              refine ⟨2135793900675142547982215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1423862600450095031988143 2135793900675142547982215)
              ·
                refine ⟨3203690851012713821973323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2135793900675142547982215 3203690851012713821973323)
                ·
                  refine ⟨4805536276519070732959985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3203690851012713821973323 4805536276519070732959985)
                  ·
                    refine ⟨3604152207389303049719989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4805536276519070732959985 3604152207389303049719989)
                    ·
                      refine ⟨337889269442747160911249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3604152207389303049719989 337889269442747160911249)
                      ·
                        rfl

theorem cell23_658037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_658037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658037 prefixEnd_658037 := by exact prefixLift 658037
  have htrace : WordTrace (prefixWord ++ tailWord_658037) baseStart_658037 baseEnd_658037 := by
    simpa [prefixWord, tailWord_658037, baseEnd_658037] using wordTrace_append hprefix tailTrace_658037
  have hstable : (prefixWord ++ tailWord_658037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658037).length < 2 ^ (prefixWord ++ tailWord_658037).sum := by decide
  have hdescent : baseEnd_658037 < baseStart_658037 := by decide
  rcases family_descends (prefixWord ++ tailWord_658037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658043 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 4]
def baseStart_658043 : Nat := 118140960795 + 658043 * 2 ^ 59
def prefixEnd_658043 : Nat := 4983230072969 + 3 ^ 40 * 658043 * 2
def baseEnd_658043 : Nat := 337892350326674137436221

theorem tailTrace_658043 : CollatzResearch.WordTrace tailWord_658043 prefixEnd_658043 337892350326674137436221 := by
  unfold tailWord_658043
  simp only [CollatzResearch.WordTrace]
  refine ⟨24000799955030070642098783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16000533303353380428065855 24000799955030070642098783)
  ·
    refine ⟨36001199932545105963148175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24000799955030070642098783 36001199932545105963148175)
    ·
      refine ⟨54001799898817658944722263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36001199932545105963148175 54001799898817658944722263)
      ·
        refine ⟨81002699848226488417083395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54001799898817658944722263 81002699848226488417083395)
        ·
          refine ⟨121504049772339732625625093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81002699848226488417083395 121504049772339732625625093)
          ·
            refine ⟨22782009332313699867304705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121504049772339732625625093 22782009332313699867304705)
            ·
              refine ⟨17086506999235274900478529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22782009332313699867304705 17086506999235274900478529)
              ·
                refine ⟨12814880249426456175358897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17086506999235274900478529 12814880249426456175358897)
                ·
                  refine ⟨9611160187069842131519173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12814880249426456175358897 9611160187069842131519173)
                  ·
                    refine ⟨1802092535075595399659845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9611160187069842131519173 1802092535075595399659845)
                    ·
                      refine ⟨337892350326674137436221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1802092535075595399659845 337892350326674137436221)
                      ·
                        rfl

theorem cell23_658043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 4].length) (baseStart_658043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658043 prefixEnd_658043 := by exact prefixLift 658043
  have htrace : WordTrace (prefixWord ++ tailWord_658043) baseStart_658043 baseEnd_658043 := by
    simpa [prefixWord, tailWord_658043, baseEnd_658043] using wordTrace_append hprefix tailTrace_658043
  have hstable : (prefixWord ++ tailWord_658043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658043).length < 2 ^ (prefixWord ++ tailWord_658043).sum := by decide
  have hdescent : baseEnd_658043 < baseStart_658043 := by decide
  rcases family_descends (prefixWord ++ tailWord_658043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658110 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_658110 : Nat := 118140960795 + 658110 * 2 ^ 59
def prefixEnd_658110 : Nat := 4983230072969 + 3 ^ 40 * 658110 * 2
def baseEnd_658110 : Nat := 337926753530525375298413

theorem tailTrace_658110 : CollatzResearch.WordTrace tailWord_658110 prefixEnd_658110 337926753530525375298413 := by
  unfold tailWord_658110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3000405455723417635598473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16002162430524894056525189 3000405455723417635598473)
  ·
    refine ⟨2250304091792563226698855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3000405455723417635598473 2250304091792563226698855)
    ·
      refine ⟨3375456137688844840048283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2250304091792563226698855 3375456137688844840048283)
      ·
        refine ⟨5063184206533267260072425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3375456137688844840048283 5063184206533267260072425)
        ·
          refine ⟨3797388154899950445054319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5063184206533267260072425 3797388154899950445054319)
          ·
            refine ⟨5696082232349925667581479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3797388154899950445054319 5696082232349925667581479)
            ·
              refine ⟨8544123348524888501372219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5696082232349925667581479 8544123348524888501372219)
              ·
                refine ⟨12816185022787332752058329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8544123348524888501372219 12816185022787332752058329)
                ·
                  refine ⟨9612138767090499564043747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12816185022787332752058329 9612138767090499564043747)
                  ·
                    refine ⟨14418208150635749346065621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9612138767090499564043747 14418208150635749346065621)
                    ·
                      refine ⟨337926753530525375298413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14418208150635749346065621 337926753530525375298413)
                      ·
                        rfl

theorem cell23_658110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_658110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658110 prefixEnd_658110 := by exact prefixLift 658110
  have htrace : WordTrace (prefixWord ++ tailWord_658110) baseStart_658110 baseEnd_658110 := by
    simpa [prefixWord, tailWord_658110, baseEnd_658110] using wordTrace_append hprefix tailTrace_658110
  have hstable : (prefixWord ++ tailWord_658110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658110).length < 2 ^ (prefixWord ++ tailWord_658110).sum := by decide
  have hdescent : baseEnd_658110 < baseStart_658110 := by decide
  rcases family_descends (prefixWord ++ tailWord_658110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658124 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 1, 5, 2]
def baseStart_658124 : Nat := 118140960795 + 658124 * 2 ^ 59
def prefixEnd_658124 : Nat := 4983230072969 + 3 ^ 40 * 658124 * 2
def baseEnd_658124 : Nat := 337933942259688320523349

theorem tailTrace_658124 : CollatzResearch.WordTrace tailWord_658124 prefixEnd_658124 337933942259688320523349 := by
  unfold tailWord_658124
  simp only [CollatzResearch.WordTrace]
  refine ⟨12001877133868310737898713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16002502845157747650531617 12001877133868310737898713)
  ·
    refine ⟨9001407850401233053424035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12001877133868310737898713 9001407850401233053424035)
    ·
      refine ⟨13502111775601849580136053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9001407850401233053424035 13502111775601849580136053)
      ·
        refine ⟨1265822978962673398137755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13502111775601849580136053 1265822978962673398137755)
        ·
          refine ⟨1898734468444010097206633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1265822978962673398137755 1898734468444010097206633)
          ·
            refine ⟨1424050851333007572904975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1898734468444010097206633 1424050851333007572904975)
            ·
              refine ⟨2136076276999511359357463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1424050851333007572904975 2136076276999511359357463)
              ·
                refine ⟨3204114415499267039036195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2136076276999511359357463 3204114415499267039036195)
                ·
                  refine ⟨4806171623248900558554293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3204114415499267039036195 4806171623248900558554293)
                  ·
                    refine ⟨450578589679584427364465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4806171623248900558554293 450578589679584427364465)
                    ·
                      refine ⟨337933942259688320523349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 450578589679584427364465 337933942259688320523349)
                      ·
                        rfl

theorem cell23_658124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_658124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658124 prefixEnd_658124 := by exact prefixLift 658124
  have htrace : WordTrace (prefixWord ++ tailWord_658124) baseStart_658124 baseEnd_658124 := by
    simpa [prefixWord, tailWord_658124, baseEnd_658124] using wordTrace_append hprefix tailTrace_658124
  have hstable : (prefixWord ++ tailWord_658124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658124).length < 2 ^ (prefixWord ++ tailWord_658124).sum := by decide
  have hdescent : baseEnd_658124 < baseStart_658124 := by decide
  rcases family_descends (prefixWord ++ tailWord_658124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658137 : List Nat := [1, 2, 1, 2, 3, 2, 3, 3, 1, 1, 4]
def baseStart_658137 : Nat := 118140960795 + 658137 * 2 ^ 59
def prefixEnd_658137 : Nat := 4983230072969 + 3 ^ 40 * 658137 * 2
def baseEnd_658137 : Nat := 337940617508196769660789

theorem tailTrace_658137 : CollatzResearch.WordTrace tailWord_658137 prefixEnd_658137 337940617508196769660789 := by
  unfold tailWord_658137
  simp only [CollatzResearch.WordTrace]
  refine ⟨24004228416689524696020665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16002818944459683130680443 24004228416689524696020665)
  ·
    refine ⟨18003171312517143522015499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24004228416689524696020665 18003171312517143522015499)
    ·
      refine ⟨27004756968775715283023249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18003171312517143522015499 27004756968775715283023249)
      ·
        refine ⟨20253567726581786462267437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27004756968775715283023249 20253567726581786462267437)
        ·
          refine ⟨7595087897468169923350289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20253567726581786462267437 7595087897468169923350289)
          ·
            refine ⟨5696315923101127442512717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7595087897468169923350289 5696315923101127442512717)
            ·
              refine ⟨2136118471162922790942269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5696315923101127442512717 2136118471162922790942269)
              ·
                refine ⟨801044426686096046603351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2136118471162922790942269 801044426686096046603351)
                ·
                  refine ⟨1201566640029144069905027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801044426686096046603351 1201566640029144069905027)
                  ·
                    refine ⟨1802349960043716104857541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1201566640029144069905027 1802349960043716104857541)
                    ·
                      refine ⟨337940617508196769660789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1802349960043716104857541 337940617508196769660789)
                      ·
                        rfl

theorem cell23_658137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 1, 4].length) (baseStart_658137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658137 prefixEnd_658137 := by exact prefixLift 658137
  have htrace : WordTrace (prefixWord ++ tailWord_658137) baseStart_658137 baseEnd_658137 := by
    simpa [prefixWord, tailWord_658137, baseEnd_658137] using wordTrace_append hprefix tailTrace_658137
  have hstable : (prefixWord ++ tailWord_658137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658137).length < 2 ^ (prefixWord ++ tailWord_658137).sum := by decide
  have hdescent : baseEnd_658137 < baseStart_658137 := by decide
  rcases family_descends (prefixWord ++ tailWord_658137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658157 : List Nat := [1, 5, 1, 2, 1, 1, 3, 2, 1, 1, 5]
def baseStart_658157 : Nat := 118140960795 + 658157 * 2 ^ 59
def prefixEnd_658157 : Nat := 4983230072969 + 3 ^ 40 * 658157 * 2
def baseEnd_658157 : Nat := 337950887121286691410697

theorem tailTrace_658157 : CollatzResearch.WordTrace tailWord_658157 prefixEnd_658157 337950887121286691410697 := by
  unfold tailWord_658157
  simp only [CollatzResearch.WordTrace]
  refine ⟨24004957876617068111748725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16003305251078045407832483 24004957876617068111748725)
  ·
    refine ⟨2250464800932850135476443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24004957876617068111748725 2250464800932850135476443)
    ·
      refine ⟨3375697201399275203214665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2250464800932850135476443 3375697201399275203214665)
      ·
        refine ⟨2531772901049456402410999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3375697201399275203214665 2531772901049456402410999)
        ·
          refine ⟨3797659351574184603616499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2531772901049456402410999 3797659351574184603616499)
          ·
            refine ⟨5696489027361276905424749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3797659351574184603616499 5696489027361276905424749)
            ·
              refine ⟨2136183385260478839534281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5696489027361276905424749 2136183385260478839534281)
              ·
                refine ⟨1602137538945359129650711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2136183385260478839534281 1602137538945359129650711)
                ·
                  refine ⟨2403206308418038694476067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1602137538945359129650711 2403206308418038694476067)
                  ·
                    refine ⟨3604809462627058041714101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2403206308418038694476067 3604809462627058041714101)
                    ·
                      refine ⟨337950887121286691410697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3604809462627058041714101 337950887121286691410697)
                      ·
                        rfl

theorem cell23_658157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_658157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658157 prefixEnd_658157 := by exact prefixLift 658157
  have htrace : WordTrace (prefixWord ++ tailWord_658157) baseStart_658157 baseEnd_658157 := by
    simpa [prefixWord, tailWord_658157, baseEnd_658157] using wordTrace_append hprefix tailTrace_658157
  have hstable : (prefixWord ++ tailWord_658157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658157).length < 2 ^ (prefixWord ++ tailWord_658157).sum := by decide
  have hdescent : baseEnd_658157 < baseStart_658157 := by decide
  rcases family_descends (prefixWord ++ tailWord_658157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658190 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 1, 9]
def baseStart_658190 : Nat := 118140960795 + 658190 * 2 ^ 59
def prefixEnd_658190 : Nat := 4983230072969 + 3 ^ 40 * 658190 * 2
def baseEnd_658190 : Nat := 112655943994295020766015

theorem tailTrace_658190 : CollatzResearch.WordTrace tailWord_658190 prefixEnd_658190 112655943994295020766015 := by
  unfold tailWord_658190
  simp only [CollatzResearch.WordTrace]
  refine ⟨3000770185687189343462503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16004107656998343165133349 3000770185687189343462503)
  ·
    refine ⟨4501155278530784015193755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3000770185687189343462503 4501155278530784015193755)
    ·
      refine ⟨6751732917796176022790633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4501155278530784015193755 6751732917796176022790633)
      ·
        refine ⟨5063799688347132017092975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6751732917796176022790633 5063799688347132017092975)
        ·
          refine ⟨7595699532520698025639463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5063799688347132017092975 7595699532520698025639463)
          ·
            refine ⟨11393549298781047038459195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7595699532520698025639463 11393549298781047038459195)
            ·
              refine ⟨17090323948171570557688793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11393549298781047038459195 17090323948171570557688793)
              ·
                refine ⟨12817742961128677918266595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17090323948171570557688793 12817742961128677918266595)
                ·
                  refine ⟨19226614441693016877399893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12817742961128677918266595 19226614441693016877399893)
                  ·
                    refine ⟨112655943994295020766015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 19226614441693016877399893 112655943994295020766015)
                    ·
                      rfl

theorem cell23_658190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_658190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658190 prefixEnd_658190 := by exact prefixLift 658190
  have htrace : WordTrace (prefixWord ++ tailWord_658190) baseStart_658190 baseEnd_658190 := by
    simpa [prefixWord, tailWord_658190, baseEnd_658190] using wordTrace_append hprefix tailTrace_658190
  have hstable : (prefixWord ++ tailWord_658190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658190).length < 2 ^ (prefixWord ++ tailWord_658190).sum := by decide
  have hdescent : baseEnd_658190 < baseStart_658190 := by decide
  rcases family_descends (prefixWord ++ tailWord_658190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658194 : List Nat := [3, 2, 4, 1, 2, 2, 9]
def baseStart_658194 : Nat := 118140960795 + 658194 * 2 ^ 59
def prefixEnd_658194 : Nat := 4983230072969 + 3 ^ 40 * 658194 * 2
def baseEnd_658194 : Nat := 4172467727228432674667

theorem tailTrace_658194 : CollatzResearch.WordTrace tailWord_658194 prefixEnd_658194 4172467727228432674667 := by
  unfold tailWord_658194
  simp only [CollatzResearch.WordTrace]
  refine ⟨6001576844370755857711409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16004204918322015620563757 6001576844370755857711409)
  ·
    refine ⟨4501182633278066893283557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6001576844370755857711409 4501182633278066893283557)
    ·
      refine ⟨843971743739637542490667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4501182633278066893283557 843971743739637542490667)
      ·
        refine ⟨1265957615609456313736001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 843971743739637542490667 1265957615609456313736001)
        ·
          refine ⟨949468211707092235302001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1265957615609456313736001 949468211707092235302001)
          ·
            refine ⟨712101158780319176476501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 949468211707092235302001 712101158780319176476501)
            ·
              refine ⟨4172467727228432674667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 712101158780319176476501 4172467727228432674667)
              ·
                rfl

theorem cell23_658194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 9].length) (baseStart_658194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658194 prefixEnd_658194 := by exact prefixLift 658194
  have htrace : WordTrace (prefixWord ++ tailWord_658194) baseStart_658194 baseEnd_658194 := by
    simpa [prefixWord, tailWord_658194, baseEnd_658194] using wordTrace_append hprefix tailTrace_658194
  have hstable : (prefixWord ++ tailWord_658194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658194).length < 2 ^ (prefixWord ++ tailWord_658194).sum := by decide
  have hdescent : baseEnd_658194 < baseStart_658194 := by decide
  rcases family_descends (prefixWord ++ tailWord_658194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658200 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 4, 2, 5]
def baseStart_658200 : Nat := 118140960795 + 658200 * 2 ^ 59
def prefixEnd_658200 : Nat := 4983230072969 + 3 ^ 40 * 658200 * 2
def baseEnd_658200 : Nat := 337972966789430023172999

theorem tailTrace_658200 : CollatzResearch.WordTrace tailWord_658200 prefixEnd_658200 337972966789430023172999 := by
  unfold tailWord_658200
  simp only [CollatzResearch.WordTrace]
  refine ⟨12003263107730643227782027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16004350810307524303709369 12003263107730643227782027)
  ·
    refine ⟨18004894661595964841673041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12003263107730643227782027 18004894661595964841673041)
    ·
      refine ⟨13503670996196973631254781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18004894661595964841673041 13503670996196973631254781)
      ·
        refine ⟨5063876623573865111720543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13503670996196973631254781 5063876623573865111720543)
        ·
          refine ⟨7595814935360797667580815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5063876623573865111720543 7595814935360797667580815)
          ·
            refine ⟨11393722403041196501371223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7595814935360797667580815 11393722403041196501371223)
            ·
              refine ⟨17090583604561794752056835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11393722403041196501371223 17090583604561794752056835)
              ·
                refine ⟨25635875406842692128085253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17090583604561794752056835 25635875406842692128085253)
                ·
                  refine ⟨4806726638783004774015985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25635875406842692128085253 4806726638783004774015985)
                  ·
                    refine ⟨3605044979087253580511989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4806726638783004774015985 3605044979087253580511989)
                    ·
                      refine ⟨337972966789430023172999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3605044979087253580511989 337972966789430023172999)
                      ·
                        rfl

theorem cell23_658200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_658200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658200 prefixEnd_658200 := by exact prefixLift 658200
  have htrace : WordTrace (prefixWord ++ tailWord_658200) baseStart_658200 baseEnd_658200 := by
    simpa [prefixWord, tailWord_658200, baseEnd_658200] using wordTrace_append hprefix tailTrace_658200
  have hstable : (prefixWord ++ tailWord_658200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658200).length < 2 ^ (prefixWord ++ tailWord_658200).sum := by decide
  have hdescent : baseEnd_658200 < baseStart_658200 := by decide
  rcases family_descends (prefixWord ++ tailWord_658200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658204 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 4, 1, 3]
def baseStart_658204 : Nat := 118140960795 + 658204 * 2 ^ 59
def prefixEnd_658204 : Nat := 4983230072969 + 3 ^ 40 * 658204 * 2
def baseEnd_658204 : Nat := 337975020712048007522981

theorem tailTrace_658204 : CollatzResearch.WordTrace tailWord_658204 prefixEnd_658204 337975020712048007522981 := by
  unfold tailWord_658204
  simp only [CollatzResearch.WordTrace]
  refine ⟨12003336053723397569354833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16004448071631196759139777 12003336053723397569354833)
  ·
    refine ⟨9002502040292548177016125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12003336053723397569354833 9002502040292548177016125)
    ·
      refine ⟨3375938265109705566381047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9002502040292548177016125 3375938265109705566381047)
      ·
        refine ⟨5063907397664558349571571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3375938265109705566381047 5063907397664558349571571)
        ·
          refine ⟨7595861096496837524357357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5063907397664558349571571 7595861096496837524357357)
          ·
            refine ⟨2848447911186314071634009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7595861096496837524357357 2848447911186314071634009)
            ·
              refine ⟨2136335933389735553725507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2848447911186314071634009 2136335933389735553725507)
              ·
                refine ⟨3204503900084603330588261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2136335933389735553725507 3204503900084603330588261)
                ·
                  refine ⟨600844481265863124485299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3204503900084603330588261 600844481265863124485299)
                  ·
                    refine ⟨901266721898794686727949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 600844481265863124485299 901266721898794686727949)
                    ·
                      refine ⟨337975020712048007522981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 901266721898794686727949 337975020712048007522981)
                      ·
                        rfl

theorem cell23_658204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_658204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658204 prefixEnd_658204 := by exact prefixLift 658204
  have htrace : WordTrace (prefixWord ++ tailWord_658204) baseStart_658204 baseEnd_658204 := by
    simpa [prefixWord, tailWord_658204, baseEnd_658204] using wordTrace_append hprefix tailTrace_658204
  have hstable : (prefixWord ++ tailWord_658204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658204).length < 2 ^ (prefixWord ++ tailWord_658204).sum := by decide
  have hdescent : baseEnd_658204 < baseStart_658204 := by decide
  rcases family_descends (prefixWord ++ tailWord_658204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658205 : List Nat := [1, 4, 2, 4, 1, 2, 1, 1, 3, 2, 2]
def baseStart_658205 : Nat := 118140960795 + 658205 * 2 ^ 59
def prefixEnd_658205 : Nat := 4983230072969 + 3 ^ 40 * 658205 * 2
def baseEnd_658205 : Nat := 337975534192702503610477

theorem tailTrace_658205 : CollatzResearch.WordTrace tailWord_658205 prefixEnd_658205 337975534192702503610477 := by
  unfold tailWord_658205
  simp only [CollatzResearch.WordTrace]
  refine ⟨24006708580443172309496069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16004472386962114872997379 24006708580443172309496069)
  ·
    refine ⟨4501257858833094808030513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24006708580443172309496069 4501257858833094808030513)
    ·
      refine ⟨3375943394124821106022885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4501257858833094808030513 3375943394124821106022885)
      ·
        refine ⟨632989386398403957379291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3375943394124821106022885 632989386398403957379291)
        ·
          refine ⟨949484079597605936068937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632989386398403957379291 949484079597605936068937)
          ·
            refine ⟨712113059698204452051703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 949484079597605936068937 712113059698204452051703)
            ·
              refine ⟨1068169589547306678077555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712113059698204452051703 1068169589547306678077555)
              ·
                refine ⟨1602254384320960017116333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1068169589547306678077555 1602254384320960017116333)
                ·
                  refine ⟨600845394120360006418625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1602254384320960017116333 600845394120360006418625)
                  ·
                    refine ⟨450634045590270004813969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 600845394120360006418625 450634045590270004813969)
                    ·
                      refine ⟨337975534192702503610477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 450634045590270004813969 337975534192702503610477)
                      ·
                        rfl

theorem cell23_658205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_658205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658205 prefixEnd_658205 := by exact prefixLift 658205
  have htrace : WordTrace (prefixWord ++ tailWord_658205) baseStart_658205 baseEnd_658205 := by
    simpa [prefixWord, tailWord_658205, baseEnd_658205] using wordTrace_append hprefix tailTrace_658205
  have hstable : (prefixWord ++ tailWord_658205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658205).length < 2 ^ (prefixWord ++ tailWord_658205).sum := by decide
  have hdescent : baseEnd_658205 < baseStart_658205 := by decide
  rcases family_descends (prefixWord ++ tailWord_658205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658220 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 1, 8]
def baseStart_658220 : Nat := 118140960795 + 658220 * 2 ^ 59
def prefixEnd_658220 : Nat := 4983230072969 + 3 ^ 40 * 658220 * 2
def baseEnd_658220 : Nat := 112661078800839981640969

theorem tailTrace_658220 : CollatzResearch.WordTrace tailWord_658220 prefixEnd_658220 112661078800839981640969 := by
  unfold tailWord_658220
  simp only [CollatzResearch.WordTrace]
  refine ⟨12003627837694414935646057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16004837116925886580861409 12003627837694414935646057)
  ·
    refine ⟨9002720878270811201734543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12003627837694414935646057 9002720878270811201734543)
    ·
      refine ⟨13504081317406216802601815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9002720878270811201734543 13504081317406216802601815)
      ·
        refine ⟨20256121976109325203902723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13504081317406216802601815 20256121976109325203902723)
        ·
          refine ⟨30384182964163987805854085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20256121976109325203902723 30384182964163987805854085)
          ·
            refine ⟨5697034305780747713597641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30384182964163987805854085 5697034305780747713597641)
            ·
              refine ⟨4272775729335560785198231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5697034305780747713597641 4272775729335560785198231)
              ·
                refine ⟨6409163594003341177797347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4272775729335560785198231 6409163594003341177797347)
                ·
                  refine ⟨9613745391005011766696021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6409163594003341177797347 9613745391005011766696021)
                  ·
                    refine ⟨112661078800839981640969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9613745391005011766696021 112661078800839981640969)
                    ·
                      rfl

theorem cell23_658220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_658220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658220 prefixEnd_658220 := by exact prefixLift 658220
  have htrace : WordTrace (prefixWord ++ tailWord_658220) baseStart_658220 baseEnd_658220 := by
    simpa [prefixWord, tailWord_658220, baseEnd_658220] using wordTrace_append hprefix tailTrace_658220
  have hstable : (prefixWord ++ tailWord_658220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658220).length < 2 ^ (prefixWord ++ tailWord_658220).sum := by decide
  have hdescent : baseEnd_658220 < baseStart_658220 := by decide
  rcases family_descends (prefixWord ++ tailWord_658220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658250 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 11]
def baseStart_658250 : Nat := 118140960795 + 658250 * 2 ^ 59
def prefixEnd_658250 : Nat := 4983230072969 + 3 ^ 40 * 658250 * 2
def baseEnd_658250 : Nat := 37555404535794980838641

theorem tailTrace_658250 : CollatzResearch.WordTrace tailWord_658250 prefixEnd_658250 37555404535794980838641 := by
  unfold tailWord_658250
  simp only [CollatzResearch.WordTrace]
  refine ⟨6002087466320036248721051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16005566576853429996589469 6002087466320036248721051)
  ·
    refine ⟨9003131199480054373081577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6002087466320036248721051 9003131199480054373081577)
    ·
      refine ⟨6752348399610040779811183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9003131199480054373081577 6752348399610040779811183)
      ·
        refine ⟨10128522599415061169716775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6752348399610040779811183 10128522599415061169716775)
        ·
          refine ⟨15192783899122591754575163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10128522599415061169716775 15192783899122591754575163)
          ·
            refine ⟨22789175848683887631862745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15192783899122591754575163 22789175848683887631862745)
            ·
              refine ⟨17091881886512915723897059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22789175848683887631862745 17091881886512915723897059)
              ·
                refine ⟨25637822829769373585845589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17091881886512915723897059 25637822829769373585845589)
                ·
                  refine ⟨37555404535794980838641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 25637822829769373585845589 37555404535794980838641)
                  ·
                    rfl

theorem cell23_658250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 11].length) (baseStart_658250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658250 prefixEnd_658250 := by exact prefixLift 658250
  have htrace : WordTrace (prefixWord ++ tailWord_658250) baseStart_658250 baseEnd_658250 := by
    simpa [prefixWord, tailWord_658250, baseEnd_658250] using wordTrace_append hprefix tailTrace_658250
  have hstable : (prefixWord ++ tailWord_658250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658250).length < 2 ^ (prefixWord ++ tailWord_658250).sum := by decide
  have hdescent : baseEnd_658250 < baseStart_658250 := by decide
  rcases family_descends (prefixWord ++ tailWord_658250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658277 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 1, 5, 3]
def baseStart_658277 : Nat := 118140960795 + 658277 * 2 ^ 59
def prefixEnd_658277 : Nat := 4983230072969 + 3 ^ 40 * 658277 * 2
def baseEnd_658277 : Nat := 338012504799826221910145

theorem tailTrace_658277 : CollatzResearch.WordTrace tailWord_658277 prefixEnd_658277 338012504799826221910145 := by
  unfold tailWord_658277
  simp only [CollatzResearch.WordTrace]
  refine ⟨24009334636182328606117085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16006223090788219070744723 24009334636182328606117085)
  ·
    refine ⟨9003500488568373227293907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24009334636182328606117085 9003500488568373227293907)
    ·
      refine ⟨13505250732852559840940861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9003500488568373227293907 13505250732852559840940861)
      ·
        refine ⟨5064469024819709940352823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13505250732852559840940861 5064469024819709940352823)
        ·
          refine ⟨7596703537229564910529235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5064469024819709940352823 7596703537229564910529235)
          ·
            refine ⟨11395055305844347365793853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7596703537229564910529235 11395055305844347365793853)
            ·
              refine ⟨4273145739691630262172695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11395055305844347365793853 4273145739691630262172695)
              ·
                refine ⟨6409718609537445393259043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4273145739691630262172695 6409718609537445393259043)
                ·
                  refine ⟨9614577914306168089888565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6409718609537445393259043 9614577914306168089888565)
                  ·
                    refine ⟨901366679466203258427053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9614577914306168089888565 901366679466203258427053)
                    ·
                      refine ⟨338012504799826221910145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 901366679466203258427053 338012504799826221910145)
                      ·
                        rfl

theorem cell23_658277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_658277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658277 prefixEnd_658277 := by exact prefixLift 658277
  have htrace : WordTrace (prefixWord ++ tailWord_658277) baseStart_658277 baseEnd_658277 := by
    simpa [prefixWord, tailWord_658277, baseEnd_658277] using wordTrace_append hprefix tailTrace_658277
  have hstable : (prefixWord ++ tailWord_658277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658277).length < 2 ^ (prefixWord ++ tailWord_658277).sum := by decide
  have hdescent : baseEnd_658277 < baseStart_658277 := by decide
  rcases family_descends (prefixWord ++ tailWord_658277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658297 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 1, 7]
def baseStart_658297 : Nat := 118140960795 + 658297 * 2 ^ 59
def prefixEnd_658297 : Nat := 4983230072969 + 3 ^ 40 * 658297 * 2
def baseEnd_658297 : Nat := 112674258137638714553351

theorem tailTrace_658297 : CollatzResearch.WordTrace tailWord_658297 prefixEnd_658297 112674258137638714553351 := by
  unfold tailWord_658297
  simp only [CollatzResearch.WordTrace]
  refine ⟨24010064096109872021845145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16006709397406581347896763 24010064096109872021845145)
  ·
    refine ⟨18007548072082404016383859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24010064096109872021845145 18007548072082404016383859)
    ·
      refine ⟨27011322108123606024575789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18007548072082404016383859 27011322108123606024575789)
      ·
        refine ⟨10129245790546352259215921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27011322108123606024575789 10129245790546352259215921)
        ·
          refine ⟨7596934342909764194411941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10129245790546352259215921 7596934342909764194411941)
          ·
            refine ⟨1424425189295580786452239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7596934342909764194411941 1424425189295580786452239)
            ·
              refine ⟨2136637783943371179678359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1424425189295580786452239 2136637783943371179678359)
              ·
                refine ⟨3204956675915056769517539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2136637783943371179678359 3204956675915056769517539)
                ·
                  refine ⟨4807435013872585154276309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3204956675915056769517539 4807435013872585154276309)
                  ·
                    refine ⟨112674258137638714553351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4807435013872585154276309 112674258137638714553351)
                    ·
                      rfl

theorem cell23_658297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 7].length) (baseStart_658297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658297 prefixEnd_658297 := by exact prefixLift 658297
  have htrace : WordTrace (prefixWord ++ tailWord_658297) baseStart_658297 baseEnd_658297 := by
    simpa [prefixWord, tailWord_658297, baseEnd_658297] using wordTrace_append hprefix tailTrace_658297
  have hstable : (prefixWord ++ tailWord_658297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658297).length < 2 ^ (prefixWord ++ tailWord_658297).sum := by decide
  have hdescent : baseEnd_658297 < baseStart_658297 := by decide
  rcases family_descends (prefixWord ++ tailWord_658297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658357 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 10]
def baseStart_658357 : Nat := 118140960795 + 658357 * 2 ^ 59
def prefixEnd_658357 : Nat := 4983230072969 + 3 ^ 40 * 658357 * 2
def baseEnd_658357 : Nat := 37561509250242878767753

theorem tailTrace_658357 : CollatzResearch.WordTrace tailWord_658357 prefixEnd_658357 37561509250242878767753 := by
  unfold tailWord_658357
  simp only [CollatzResearch.WordTrace]
  refine ⟨24012252475892502269029325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16008168317261668179352883 24012252475892502269029325)
  ·
    refine ⟨9004594678459688350885997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24012252475892502269029325 9004594678459688350885997)
    ·
      refine ⟨3376723004422383131582249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9004594678459688350885997 3376723004422383131582249)
      ·
        refine ⟨2532542253316787348686687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3376723004422383131582249 2532542253316787348686687)
        ·
          refine ⟨3798813379975181023030031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2532542253316787348686687 3798813379975181023030031)
          ·
            refine ⟨5698220069962771534545047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3798813379975181023030031 5698220069962771534545047)
            ·
              refine ⟨8547330104944157301817571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5698220069962771534545047 8547330104944157301817571)
              ·
                refine ⟨12820995157416235952726357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8547330104944157301817571 12820995157416235952726357)
                ·
                  refine ⟨37561509250242878767753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 12820995157416235952726357 37561509250242878767753)
                  ·
                    rfl

theorem cell23_658357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 10].length) (baseStart_658357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658357 prefixEnd_658357 := by exact prefixLift 658357
  have htrace : WordTrace (prefixWord ++ tailWord_658357) baseStart_658357 baseEnd_658357 := by
    simpa [prefixWord, tailWord_658357, baseEnd_658357] using wordTrace_append hprefix tailTrace_658357
  have hstable : (prefixWord ++ tailWord_658357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658357).length < 2 ^ (prefixWord ++ tailWord_658357).sum := by decide
  have hdescent : baseEnd_658357 < baseStart_658357 := by decide
  rcases family_descends (prefixWord ++ tailWord_658357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658404 : List Nat := [2, 3, 1, 1, 1, 1, 2, 6, 1, 5]
def baseStart_658404 : Nat := 118140960795 + 658404 * 2 ^ 59
def prefixEnd_658404 : Nat := 4983230072969 + 3 ^ 40 * 658404 * 2
def baseEnd_658404 : Nat := 112692572280982408340687

theorem tailTrace_658404 : CollatzResearch.WordTrace tailWord_658404 prefixEnd_658404 112692572280982408340687 := by
  unfold tailWord_658404
  simp only [CollatzResearch.WordTrace]
  refine ⟨12006983353361114647995133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16009311137814819530660177 12006983353361114647995133)
  ·
    refine ⟨4502618757510417992998175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12006983353361114647995133 4502618757510417992998175)
    ·
      refine ⟨6753928136265626989497263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4502618757510417992998175 6753928136265626989497263)
      ·
        refine ⟨10130892204398440484245895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6753928136265626989497263 10130892204398440484245895)
        ·
          refine ⟨15196338306597660726368843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10130892204398440484245895 15196338306597660726368843)
          ·
            refine ⟨22794507459896491089553265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15196338306597660726368843 22794507459896491089553265)
            ·
              refine ⟨17095880594922368317164949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22794507459896491089553265 17095880594922368317164949)
              ·
                refine ⟨801369402886986014867107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17095880594922368317164949 801369402886986014867107)
                ·
                  refine ⟨1202054104330479022300661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801369402886986014867107 1202054104330479022300661)
                  ·
                    refine ⟨112692572280982408340687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1202054104330479022300661 112692572280982408340687)
                    ·
                      rfl

theorem cell23_658404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 6, 1, 5].length) (baseStart_658404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658404 prefixEnd_658404 := by exact prefixLift 658404
  have htrace : WordTrace (prefixWord ++ tailWord_658404) baseStart_658404 baseEnd_658404 := by
    simpa [prefixWord, tailWord_658404, baseEnd_658404] using wordTrace_append hprefix tailTrace_658404
  have hstable : (prefixWord ++ tailWord_658404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658404).length < 2 ^ (prefixWord ++ tailWord_658404).sum := by decide
  have hdescent : baseEnd_658404 < baseStart_658404 := by decide
  rcases family_descends (prefixWord ++ tailWord_658404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658441 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 7, 2, 2]
def baseStart_658441 : Nat := 118140960795 + 658441 * 2 ^ 59
def prefixEnd_658441 : Nat := 4983230072969 + 3 ^ 40 * 658441 * 2
def baseEnd_658441 : Nat := 338096715627163580259391

theorem tailTrace_658441 : CollatzResearch.WordTrace tailWord_658441 prefixEnd_658441 338096715627163580259391 := by
  unfold tailWord_658441
  simp only [CollatzResearch.WordTrace]
  refine ⟨24015316207588184615087177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16010210805058789743391451 24015316207588184615087177)
  ·
    refine ⟨18011487155691138461315383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24015316207588184615087177 18011487155691138461315383)
    ·
      refine ⟨27017230733536707691973075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18011487155691138461315383 27017230733536707691973075)
      ·
        refine ⟨40525846100305061537959613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27017230733536707691973075 40525846100305061537959613)
        ·
          refine ⟨15197192287614398076734855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40525846100305061537959613 15197192287614398076734855)
          ·
            refine ⟨22795788431421597115102283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15197192287614398076734855 22795788431421597115102283)
            ·
              refine ⟨34193682647132395672653425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22795788431421597115102283 34193682647132395672653425)
              ·
                refine ⟨25645261985349296754490069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34193682647132395672653425 25645261985349296754490069)
                ·
                  refine ⟨601060827781624142683361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 25645261985349296754490069 601060827781624142683361)
                  ·
                    refine ⟨450795620836218107012521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 601060827781624142683361 450795620836218107012521)
                    ·
                      refine ⟨338096715627163580259391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 450795620836218107012521 338096715627163580259391)
                      ·
                        rfl

theorem cell23_658441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 7, 2, 2].length) (baseStart_658441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658441 prefixEnd_658441 := by exact prefixLift 658441
  have htrace : WordTrace (prefixWord ++ tailWord_658441) baseStart_658441 baseEnd_658441 := by
    simpa [prefixWord, tailWord_658441, baseEnd_658441] using wordTrace_append hprefix tailTrace_658441
  have hstable : (prefixWord ++ tailWord_658441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658441).length < 2 ^ (prefixWord ++ tailWord_658441).sum := by decide
  have hdescent : baseEnd_658441 < baseStart_658441 := by decide
  rcases family_descends (prefixWord ++ tailWord_658441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658458 : List Nat := [3, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2]
def baseStart_658458 : Nat := 118140960795 + 658458 * 2 ^ 59
def prefixEnd_658458 : Nat := 4983230072969 + 3 ^ 40 * 658458 * 2
def baseEnd_658458 : Nat := 338105444798290013746813

theorem tailTrace_658458 : CollatzResearch.WordTrace tailWord_658458 prefixEnd_658458 338105444798290013746813 := by
  unfold tailWord_658458
  simp only [CollatzResearch.WordTrace]
  refine ⟨6003984062131649129614007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16010624165684397678970685 6003984062131649129614007)
  ·
    refine ⟨9005976093197473694421011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6003984062131649129614007 9005976093197473694421011)
    ·
      refine ⟨13508964139796210541631517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9005976093197473694421011 13508964139796210541631517)
      ·
        refine ⟨5065861552423578953111819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13508964139796210541631517 5065861552423578953111819)
        ·
          refine ⟨7598792328635368429667729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5065861552423578953111819 7598792328635368429667729)
          ·
            refine ⟨5699094246476526322250797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7598792328635368429667729 5699094246476526322250797)
            ·
              refine ⟨2137160342428697370844049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5699094246476526322250797 2137160342428697370844049)
              ·
                refine ⟨1602870256821523028133037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2137160342428697370844049 1602870256821523028133037)
                ·
                  refine ⟨601076346308071135549889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1602870256821523028133037 601076346308071135549889)
                  ·
                    refine ⟨450807259731053351662417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 601076346308071135549889 450807259731053351662417)
                    ·
                      refine ⟨338105444798290013746813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 450807259731053351662417 338105444798290013746813)
                      ·
                        rfl

theorem cell23_658458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_658458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658458 prefixEnd_658458 := by exact prefixLift 658458
  have htrace : WordTrace (prefixWord ++ tailWord_658458) baseStart_658458 baseEnd_658458 := by
    simpa [prefixWord, tailWord_658458, baseEnd_658458] using wordTrace_append hprefix tailTrace_658458
  have hstable : (prefixWord ++ tailWord_658458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658458).length < 2 ^ (prefixWord ++ tailWord_658458).sum := by decide
  have hdescent : baseEnd_658458 < baseStart_658458 := by decide
  rcases family_descends (prefixWord ++ tailWord_658458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658475 : List Nat := [1, 1, 1, 1, 2, 1, 8, 3, 1, 2, 2]
def baseStart_658475 : Nat := 118140960795 + 658475 * 2 ^ 59
def prefixEnd_658475 : Nat := 4983230072969 + 3 ^ 40 * 658475 * 2
def baseEnd_658475 : Nat := 338114173969416447234235

theorem tailTrace_658475 : CollatzResearch.WordTrace tailWord_658475 prefixEnd_658475 338114173969416447234235 := by
  unfold tailWord_658475
  simp only [CollatzResearch.WordTrace]
  refine ⟨24016556289465008421824879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16011037526310005614549919 24016556289465008421824879)
  ·
    refine ⟨36024834434197512632737319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24016556289465008421824879 36024834434197512632737319)
    ·
      refine ⟨54037251651296268949105979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36024834434197512632737319 54037251651296268949105979)
      ·
        refine ⟨81055877476944403423658969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54037251651296268949105979 81055877476944403423658969)
        ·
          refine ⟨60791908107708302567744227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81055877476944403423658969 60791908107708302567744227)
          ·
            refine ⟨91187862161562453851616341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60791908107708302567744227 91187862161562453851616341)
            ·
              refine ⟨1068607759705810006073629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 91187862161562453851616341 1068607759705810006073629)
              ·
                refine ⟨400727909889678752277611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1068607759705810006073629 400727909889678752277611)
                ·
                  refine ⟨601091864834518128416417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 400727909889678752277611 601091864834518128416417)
                  ·
                    refine ⟨450818898625888596312313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 601091864834518128416417 450818898625888596312313)
                    ·
                      refine ⟨338114173969416447234235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 450818898625888596312313 338114173969416447234235)
                      ·
                        rfl

theorem cell23_658475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 8, 3, 1, 2, 2].length) (baseStart_658475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658475 prefixEnd_658475 := by exact prefixLift 658475
  have htrace : WordTrace (prefixWord ++ tailWord_658475) baseStart_658475 baseEnd_658475 := by
    simpa [prefixWord, tailWord_658475, baseEnd_658475] using wordTrace_append hprefix tailTrace_658475
  have hstable : (prefixWord ++ tailWord_658475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658475).length < 2 ^ (prefixWord ++ tailWord_658475).sum := by decide
  have hdescent : baseEnd_658475 < baseStart_658475 := by decide
  rcases family_descends (prefixWord ++ tailWord_658475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658478 : List Nat := [4, 1, 3, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_658478 : Nat := 118140960795 + 658478 * 2 ^ 59
def prefixEnd_658478 : Nat := 4983230072969 + 3 ^ 40 * 658478 * 2
def baseEnd_658478 : Nat := 338115714411379935496721

theorem tailTrace_658478 : CollatzResearch.WordTrace tailWord_658478 prefixEnd_658478 338115714411379935496721 := by
  unfold tailWord_658478
  simp only [CollatzResearch.WordTrace]
  refine ⟨3002083213556767491773011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16011110472302759956122725 3002083213556767491773011)
  ·
    refine ⟨4503124820335151237659517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3002083213556767491773011 4503124820335151237659517)
    ·
      refine ⟨1688671807625681714122319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4503124820335151237659517 1688671807625681714122319)
      ·
        refine ⟨2533007711438522571183479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1688671807625681714122319 2533007711438522571183479)
        ·
          refine ⟨3799511567157783856775219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2533007711438522571183479 3799511567157783856775219)
          ·
            refine ⟨5699267350736675785162829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3799511567157783856775219 5699267350736675785162829)
            ·
              refine ⟨2137225256526253419436061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5699267350736675785162829 2137225256526253419436061)
              ·
                refine ⟨801459471197345032288523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2137225256526253419436061 801459471197345032288523)
                ·
                  refine ⟨1202189206796017548432785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801459471197345032288523 1202189206796017548432785)
                  ·
                    refine ⟨901641905097013161324589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1202189206796017548432785 901641905097013161324589)
                    ·
                      refine ⟨338115714411379935496721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 901641905097013161324589 338115714411379935496721)
                      ·
                        rfl

theorem cell23_658478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_658478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658478 prefixEnd_658478 := by exact prefixLift 658478
  have htrace : WordTrace (prefixWord ++ tailWord_658478) baseStart_658478 baseEnd_658478 := by
    simpa [prefixWord, tailWord_658478, baseEnd_658478] using wordTrace_append hprefix tailTrace_658478
  have hstable : (prefixWord ++ tailWord_658478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658478).length < 2 ^ (prefixWord ++ tailWord_658478).sum := by decide
  have hdescent : baseEnd_658478 < baseStart_658478 := by decide
  rcases family_descends (prefixWord ++ tailWord_658478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658501 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 5, 3, 2]
def baseStart_658501 : Nat := 118140960795 + 658501 * 2 ^ 59
def prefixEnd_658501 : Nat := 4983230072969 + 3 ^ 40 * 658501 * 2
def baseEnd_658501 : Nat := 338127524466433345509115

theorem tailTrace_658501 : CollatzResearch.WordTrace tailWord_658501 prefixEnd_658501 338127524466433345509115 := by
  unfold tailWord_658501
  simp only [CollatzResearch.WordTrace]
  refine ⟨24017504587370814862271357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16011669724913876574847571 24017504587370814862271357)
  ·
    refine ⟨9006564220264055573351759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24017504587370814862271357 9006564220264055573351759)
    ·
      refine ⟨13509846330396083360027639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9006564220264055573351759 13509846330396083360027639)
      ·
        refine ⟨20264769495594125040041459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13509846330396083360027639 20264769495594125040041459)
        ·
          refine ⟨30397154243391187560062189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20264769495594125040041459 30397154243391187560062189)
          ·
            refine ⟨11398932841271695335023321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30397154243391187560062189 11398932841271695335023321)
            ·
              refine ⟨8549199630953771501267491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11398932841271695335023321 8549199630953771501267491)
              ·
                refine ⟨12823799446430657251901237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8549199630953771501267491 12823799446430657251901237)
                ·
                  refine ⟨1202231198102874117365741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12823799446430657251901237 1202231198102874117365741)
                  ·
                    refine ⟨450836699288577794012153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1202231198102874117365741 450836699288577794012153)
                    ·
                      refine ⟨338127524466433345509115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 450836699288577794012153 338127524466433345509115)
                      ·
                        rfl

theorem cell23_658501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 5, 3, 2].length) (baseStart_658501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658501 prefixEnd_658501 := by exact prefixLift 658501
  have htrace : WordTrace (prefixWord ++ tailWord_658501) baseStart_658501 baseEnd_658501 := by
    simpa [prefixWord, tailWord_658501, baseEnd_658501] using wordTrace_append hprefix tailTrace_658501
  have hstable : (prefixWord ++ tailWord_658501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658501).length < 2 ^ (prefixWord ++ tailWord_658501).sum := by decide
  have hdescent : baseEnd_658501 < baseStart_658501 := by decide
  rcases family_descends (prefixWord ++ tailWord_658501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658502 : List Nat := [6, 1, 1, 1, 1, 3, 3, 1, 2, 4]
def baseStart_658502 : Nat := 118140960795 + 658502 * 2 ^ 59
def prefixEnd_658502 : Nat := 4983230072969 + 3 ^ 40 * 658502 * 2
def baseEnd_658502 : Nat := 112709345982362613865537

theorem tailTrace_658502 : CollatzResearch.WordTrace tailWord_658502 prefixEnd_658502 112709345982362613865537 := by
  unfold tailWord_658502
  simp only [CollatzResearch.WordTrace]
  refine ⟨750548158136474751033055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16011694040244794688705173 750548158136474751033055)
  ·
    refine ⟨1125822237204712126549583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 750548158136474751033055 1125822237204712126549583)
    ·
      refine ⟨1688733355807068189824375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1125822237204712126549583 1688733355807068189824375)
      ·
        refine ⟨2533100033710602284736563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1688733355807068189824375 2533100033710602284736563)
        ·
          refine ⟨3799650050565903427104845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2533100033710602284736563 3799650050565903427104845)
          ·
            refine ⟨1424868768962213785164317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3799650050565903427104845 1424868768962213785164317)
            ·
              refine ⟨534325788360830169436619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1424868768962213785164317 534325788360830169436619)
              ·
                refine ⟨801488682541245254154929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534325788360830169436619 801488682541245254154929)
                ·
                  refine ⟨601116511905933940616197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 801488682541245254154929 601116511905933940616197)
                  ·
                    refine ⟨112709345982362613865537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 601116511905933940616197 112709345982362613865537)
                    ·
                      rfl

theorem cell23_658502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_658502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658502 prefixEnd_658502 := by exact prefixLift 658502
  have htrace : WordTrace (prefixWord ++ tailWord_658502) baseStart_658502 baseEnd_658502 := by
    simpa [prefixWord, tailWord_658502, baseEnd_658502] using wordTrace_append hprefix tailTrace_658502
  have hstable : (prefixWord ++ tailWord_658502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658502).length < 2 ^ (prefixWord ++ tailWord_658502).sum := by decide
  have hdescent : baseEnd_658502 < baseStart_658502 := by decide
  rcases family_descends (prefixWord ++ tailWord_658502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658526 : List Nat := [4, 4, 1, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_658526 : Nat := 118140960795 + 658526 * 2 ^ 59
def prefixEnd_658526 : Nat := 4983230072969 + 3 ^ 40 * 658526 * 2
def baseEnd_658526 : Nat := 338140361482795747696501

theorem tailTrace_658526 : CollatzResearch.WordTrace tailWord_658526 prefixEnd_658526 338140361482795747696501 := by
  unfold tailWord_658526
  simp only [CollatzResearch.WordTrace]
  refine ⟨3002302051535030516491429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16012277608186829421287621 3002302051535030516491429)
  ·
    refine ⟨562931634662818221842143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3002302051535030516491429 562931634662818221842143)
    ·
      refine ⟨844397451994227332763215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 562931634662818221842143 844397451994227332763215)
      ·
        refine ⟨1266596177991340999144823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 844397451994227332763215 1266596177991340999144823)
        ·
          refine ⟨1899894266987011498717235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1266596177991340999144823 1899894266987011498717235)
          ·
            refine ⟨2849841400480517248075853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1899894266987011498717235 2849841400480517248075853)
            ·
              refine ⟨1068690525180193968028445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2849841400480517248075853 1068690525180193968028445)
              ·
                refine ⟨400758946942572738010667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1068690525180193968028445 400758946942572738010667)
                ·
                  refine ⟨601138420413859107016001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 400758946942572738010667 601138420413859107016001)
                  ·
                    refine ⟨450853815310394330262001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 601138420413859107016001 450853815310394330262001)
                    ·
                      refine ⟨338140361482795747696501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 450853815310394330262001 338140361482795747696501)
                      ·
                        rfl

theorem cell23_658526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_658526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658526 prefixEnd_658526 := by exact prefixLift 658526
  have htrace : WordTrace (prefixWord ++ tailWord_658526) baseStart_658526 baseEnd_658526 := by
    simpa [prefixWord, tailWord_658526, baseEnd_658526] using wordTrace_append hprefix tailTrace_658526
  have hstable : (prefixWord ++ tailWord_658526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658526).length < 2 ^ (prefixWord ++ tailWord_658526).sum := by decide
  have hdescent : baseEnd_658526 < baseStart_658526 := by decide
  rcases family_descends (prefixWord ++ tailWord_658526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658531 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 3, 4, 2]
def baseStart_658531 : Nat := 118140960795 + 658531 * 2 ^ 59
def prefixEnd_658531 : Nat := 4983230072969 + 3 ^ 40 * 658531 * 2
def baseEnd_658531 : Nat := 338142928886068228133977

theorem tailTrace_658531 : CollatzResearch.WordTrace tailWord_658531 prefixEnd_658531 338142928886068228133977 := by
  unfold tailWord_658531
  simp only [CollatzResearch.WordTrace]
  refine ⟨24018598777262129985863447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16012399184841419990575631 24018598777262129985863447)
  ·
    refine ⟨36027898165893194978795171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24018598777262129985863447 36027898165893194978795171)
    ·
      refine ⟨54041847248839792468192757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36027898165893194978795171 54041847248839792468192757)
      ·
        refine ⟨5066423179578730543893071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54041847248839792468192757 5066423179578730543893071)
        ·
          refine ⟨7599634769368095815839607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5066423179578730543893071 7599634769368095815839607)
          ·
            refine ⟨11399452154052143723759411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7599634769368095815839607 11399452154052143723759411)
            ·
              refine ⟨17099178231078215585639117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11399452154052143723759411 17099178231078215585639117)
              ·
                refine ⟨6412191836654330844614669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17099178231078215585639117 6412191836654330844614669)
                ·
                  refine ⟨2404571938745374066730501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6412191836654330844614669 2404571938745374066730501)
                  ·
                    refine ⟨450857238514757637511969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2404571938745374066730501 450857238514757637511969)
                    ·
                      refine ⟨338142928886068228133977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 450857238514757637511969 338142928886068228133977)
                      ·
                        rfl

theorem cell23_658531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_658531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658531 prefixEnd_658531 := by exact prefixLift 658531
  have htrace : WordTrace (prefixWord ++ tailWord_658531) baseStart_658531 baseEnd_658531 := by
    simpa [prefixWord, tailWord_658531, baseEnd_658531] using wordTrace_append hprefix tailTrace_658531
  have hstable : (prefixWord ++ tailWord_658531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658531).length < 2 ^ (prefixWord ++ tailWord_658531).sum := by decide
  have hdescent : baseEnd_658531 < baseStart_658531 := by decide
  rcases family_descends (prefixWord ++ tailWord_658531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658605 : List Nat := [1, 5, 2, 1, 3, 1, 1, 4, 5]
def baseStart_658605 : Nat := 118140960795 + 658605 * 2 ^ 59
def prefixEnd_658605 : Nat := 4983230072969 + 3 ^ 40 * 658605 * 2
def baseEnd_658605 : Nat := 37575658494944548734293

theorem tailTrace_658605 : CollatzResearch.WordTrace tailWord_658605 prefixEnd_658605 37575658494944548734293 := by
  unfold tailWord_658605
  simp only [CollatzResearch.WordTrace]
  refine ⟨24021297778994040624057269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16014198519329360416038179 24021297778994040624057269)
  ·
    refine ⟨2251996666780691308505369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24021297778994040624057269 2251996666780691308505369)
    ·
      refine ⟨1688997500085518481379027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2251996666780691308505369 1688997500085518481379027)
      ·
        refine ⟨2533496250128277722068541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1688997500085518481379027 2533496250128277722068541)
        ·
          refine ⟨950061093798104145775703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2533496250128277722068541 950061093798104145775703)
          ·
            refine ⟨1425091640697156218663555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950061093798104145775703 1425091640697156218663555)
            ·
              refine ⟨2137637461045734327995333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1425091640697156218663555 2137637461045734327995333)
              ·
                refine ⟨400807023946075186499125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2137637461045734327995333 400807023946075186499125)
                ·
                  refine ⟨37575658494944548734293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 400807023946075186499125 37575658494944548734293)
                  ·
                    rfl

theorem cell23_658605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_658605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658605 prefixEnd_658605 := by exact prefixLift 658605
  have htrace : WordTrace (prefixWord ++ tailWord_658605) baseStart_658605 baseEnd_658605 := by
    simpa [prefixWord, tailWord_658605, baseEnd_658605] using wordTrace_append hprefix tailTrace_658605
  have hstable : (prefixWord ++ tailWord_658605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658605).length < 2 ^ (prefixWord ++ tailWord_658605).sum := by decide
  have hdescent : baseEnd_658605 < baseStart_658605 := by decide
  rcases family_descends (prefixWord ++ tailWord_658605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658621 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 4, 1, 4]
def baseStart_658621 : Nat := 118140960795 + 658621 * 2 ^ 59
def prefixEnd_658621 : Nat := 4983230072969 + 3 ^ 40 * 658621 * 2
def baseEnd_658621 : Nat := 338189142144972876008563

theorem tailTrace_658621 : CollatzResearch.WordTrace tailWord_658621 prefixEnd_658621 338189142144972876008563 := by
  unfold tailWord_658621
  simp only [CollatzResearch.WordTrace]
  refine ⟨24021881346936075356639717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16014587564624050237759811 24021881346936075356639717)
  ·
    refine ⟨4504102752550514129369947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24021881346936075356639717 4504102752550514129369947)
    ·
      refine ⟨6756154128825771194054921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4504102752550514129369947 6756154128825771194054921)
      ·
        refine ⟨5067115596619328395541191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6756154128825771194054921 5067115596619328395541191)
        ·
          refine ⟨7600673394928992593311787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5067115596619328395541191 7600673394928992593311787)
          ·
            refine ⟨11401010092393488889967681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7600673394928992593311787 11401010092393488889967681)
            ·
              refine ⟨8550757569295116667475761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11401010092393488889967681 8550757569295116667475761)
              ·
                refine ⟨6413068176971337500606821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8550757569295116667475761 6413068176971337500606821)
                ·
                  refine ⟨1202450283182125781363779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6413068176971337500606821 1202450283182125781363779)
                  ·
                    refine ⟨1803675424773188672045669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1202450283182125781363779 1803675424773188672045669)
                    ·
                      refine ⟨338189142144972876008563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1803675424773188672045669 338189142144972876008563)
                      ·
                        rfl

theorem cell23_658621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_658621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658621 prefixEnd_658621 := by exact prefixLift 658621
  have htrace : WordTrace (prefixWord ++ tailWord_658621) baseStart_658621 baseEnd_658621 := by
    simpa [prefixWord, tailWord_658621, baseEnd_658621] using wordTrace_append hprefix tailTrace_658621
  have hstable : (prefixWord ++ tailWord_658621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658621).length < 2 ^ (prefixWord ++ tailWord_658621).sum := by decide
  have hdescent : baseEnd_658621 < baseStart_658621 := by decide
  rcases family_descends (prefixWord ++ tailWord_658621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658638 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4]
def baseStart_658638 : Nat := 118140960795 + 658638 * 2 ^ 59
def prefixEnd_658638 : Nat := 4983230072969 + 3 ^ 40 * 658638 * 2
def baseEnd_658638 : Nat := 338197871316099309495985

theorem tailTrace_658638 : CollatzResearch.WordTrace tailWord_658638 prefixEnd_658638 338197871316099309495985 := by
  unfold tailWord_658638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3002812673484310907501071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16015000925249658173339045 3002812673484310907501071)
  ·
    refine ⟨4504219010226466361251607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3002812673484310907501071 4504219010226466361251607)
    ·
      refine ⟨6756328515339699541877411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4504219010226466361251607 6756328515339699541877411)
      ·
        refine ⟨10134492773009549312816117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6756328515339699541877411 10134492773009549312816117)
        ·
          refine ⟨950108697469645248076511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10134492773009549312816117 950108697469645248076511)
          ·
            refine ⟨1425163046204467872114767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950108697469645248076511 1425163046204467872114767)
            ·
              refine ⟨2137744569306701808172151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1425163046204467872114767 2137744569306701808172151)
              ·
                refine ⟨3206616853960052712258227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2137744569306701808172151 3206616853960052712258227)
                ·
                  refine ⟨4809925280940079068387341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3206616853960052712258227 4809925280940079068387341)
                  ·
                    refine ⟨1803721980352529650645253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4809925280940079068387341 1803721980352529650645253)
                    ·
                      refine ⟨338197871316099309495985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1803721980352529650645253 338197871316099309495985)
                      ·
                        rfl

theorem cell23_658638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_658638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658638 prefixEnd_658638 := by exact prefixLift 658638
  have htrace : WordTrace (prefixWord ++ tailWord_658638) baseStart_658638 baseEnd_658638 := by
    simpa [prefixWord, tailWord_658638, baseEnd_658638] using wordTrace_append hprefix tailTrace_658638
  have hstable : (prefixWord ++ tailWord_658638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658638).length < 2 ^ (prefixWord ++ tailWord_658638).sum := by decide
  have hdescent : baseEnd_658638 < baseStart_658638 := by decide
  rcases family_descends (prefixWord ++ tailWord_658638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658742 : List Nat := [5, 1, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_658742 : Nat := 118140960795 + 658742 * 2 ^ 59
def prefixEnd_658742 : Nat := 4983230072969 + 3 ^ 40 * 658742 * 2
def baseEnd_658742 : Nat := 112750424434722300865169

theorem tailTrace_658742 : CollatzResearch.WordTrace tailWord_658742 prefixEnd_658742 112750424434722300865169 := by
  unfold tailWord_658742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1501643411218607063862155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16017529719665142014529653 1501643411218607063862155)
  ·
    refine ⟨2252465116827910595793233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1501643411218607063862155 2252465116827910595793233)
    ·
      refine ⟨1689348837620932946844925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2252465116827910595793233 1689348837620932946844925)
      ·
        refine ⟨633505814107849855066847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1689348837620932946844925 633505814107849855066847)
        ·
          refine ⟨950258721161774782600271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633505814107849855066847 950258721161774782600271)
          ·
            refine ⟨1425388081742662173900407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950258721161774782600271 1425388081742662173900407)
            ·
              refine ⟨2138082122613993260850611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1425388081742662173900407 2138082122613993260850611)
              ·
                refine ⟨3207123183920989891275917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2138082122613993260850611 3207123183920989891275917)
                ·
                  refine ⟨1202671193970371209228469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3207123183920989891275917 1202671193970371209228469)
                  ·
                    refine ⟨112750424434722300865169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1202671193970371209228469 112750424434722300865169)
                    ·
                      rfl

theorem cell23_658742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_658742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658742 prefixEnd_658742 := by exact prefixLift 658742
  have htrace : WordTrace (prefixWord ++ tailWord_658742) baseStart_658742 baseEnd_658742 := by
    simpa [prefixWord, tailWord_658742, baseEnd_658742] using wordTrace_append hprefix tailTrace_658742
  have hstable : (prefixWord ++ tailWord_658742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658742).length < 2 ^ (prefixWord ++ tailWord_658742).sum := by decide
  have hdescent : baseEnd_658742 < baseStart_658742 := by decide
  rcases family_descends (prefixWord ++ tailWord_658742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658745 : List Nat := [1, 2, 1, 6, 2, 1, 1, 1, 3, 1, 4]
def baseStart_658745 : Nat := 118140960795 + 658745 * 2 ^ 59
def prefixEnd_658745 : Nat := 4983230072969 + 3 ^ 40 * 658745 * 2
def baseEnd_658745 : Nat := 338252813746130390857993

theorem tailTrace_658745 : CollatzResearch.WordTrace tailWord_658745 prefixEnd_658745 338252813746130390857993 := by
  unfold tailWord_658745
  simp only [CollatzResearch.WordTrace]
  refine ⟨24026403998486844534153689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16017602665657896356102459 24026403998486844534153689)
  ·
    refine ⟨18019802998865133400615267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24026403998486844534153689 18019802998865133400615267)
    ·
      refine ⟨27029704498297700100922901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18019802998865133400615267 27029704498297700100922901)
      ·
        refine ⟨1267017398357704692230761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27029704498297700100922901 1267017398357704692230761)
        ·
          refine ⟨950263048768278519173071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1267017398357704692230761 950263048768278519173071)
          ·
            refine ⟨1425394573152417778759607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950263048768278519173071 1425394573152417778759607)
            ·
              refine ⟨2138091859728626668139411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1425394573152417778759607 2138091859728626668139411)
              ·
                refine ⟨3207137789592940002209117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2138091859728626668139411 3207137789592940002209117)
                ·
                  refine ⟨1202676671097352500828419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3207137789592940002209117 1202676671097352500828419)
                  ·
                    refine ⟨1804015006646028751242629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1202676671097352500828419 1804015006646028751242629)
                    ·
                      refine ⟨338252813746130390857993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1804015006646028751242629 338252813746130390857993)
                      ·
                        rfl

theorem cell23_658745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_658745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658745 prefixEnd_658745 := by exact prefixLift 658745
  have htrace : WordTrace (prefixWord ++ tailWord_658745) baseStart_658745 baseEnd_658745 := by
    simpa [prefixWord, tailWord_658745, baseEnd_658745] using wordTrace_append hprefix tailTrace_658745
  have hstable : (prefixWord ++ tailWord_658745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658745).length < 2 ^ (prefixWord ++ tailWord_658745).sum := by decide
  have hdescent : baseEnd_658745 < baseStart_658745 := by decide
  rcases family_descends (prefixWord ++ tailWord_658745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658749 : List Nat := [1, 4, 1, 5, 1, 1, 2, 1, 2, 3, 2]
def baseStart_658749 : Nat := 118140960795 + 658749 * 2 ^ 59
def prefixEnd_658749 : Nat := 4983230072969 + 3 ^ 40 * 658749 * 2
def baseEnd_658749 : Nat := 338254867668748375207975

theorem tailTrace_658749 : CollatzResearch.WordTrace tailWord_658749 prefixEnd_658749 338254867668748375207975 := by
  unfold tailWord_658749
  simp only [CollatzResearch.WordTrace]
  refine ⟨24026549890472353217299301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16017699926981568811532867 24026549890472353217299301)
  ·
    refine ⟨4504978104463566228243619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24026549890472353217299301 4504978104463566228243619)
    ·
      refine ⟨6757467156695349342365429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4504978104463566228243619 6757467156695349342365429)
      ·
        refine ⟨633512545940189000846759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6757467156695349342365429 633512545940189000846759)
        ·
          refine ⟨950268818910283501270139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633512545940189000846759 950268818910283501270139)
          ·
            refine ⟨1425403228365425251905209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950268818910283501270139 1425403228365425251905209)
            ·
              refine ⟨1069052421274068938928907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1425403228365425251905209 1069052421274068938928907)
              ·
                refine ⟨1603578631911103408393361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069052421274068938928907 1603578631911103408393361)
                ·
                  refine ⟨1202683973933327556295021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1603578631911103408393361 1202683973933327556295021)
                  ·
                    refine ⟨451006490224997833610633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1202683973933327556295021 451006490224997833610633)
                    ·
                      refine ⟨338254867668748375207975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 451006490224997833610633 338254867668748375207975)
                      ·
                        rfl

theorem cell23_658749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_658749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658749 prefixEnd_658749 := by exact prefixLift 658749
  have htrace : WordTrace (prefixWord ++ tailWord_658749) baseStart_658749 baseEnd_658749 := by
    simpa [prefixWord, tailWord_658749, baseEnd_658749] using wordTrace_append hprefix tailTrace_658749
  have hstable : (prefixWord ++ tailWord_658749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658749).length < 2 ^ (prefixWord ++ tailWord_658749).sum := by decide
  have hdescent : baseEnd_658749 < baseStart_658749 := by decide
  rcases family_descends (prefixWord ++ tailWord_658749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658751 : List Nat := [1, 1, 2, 2, 4, 2, 2, 9]
def baseStart_658751 : Nat := 118140960795 + 658751 * 2 ^ 59
def prefixEnd_658751 : Nat := 4983230072969 + 3 ^ 40 * 658751 * 2
def baseEnd_658751 : Nat := 12527996097409532125295

theorem tailTrace_658751 : CollatzResearch.WordTrace tailWord_658751 prefixEnd_658751 12527996097409532125295 := by
  unfold tailWord_658751
  simp only [CollatzResearch.WordTrace]
  refine ⟨24026622836465107558872107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16017748557643405039248071 24026622836465107558872107)
  ·
    refine ⟨36039934254697661338308161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24026622836465107558872107 36039934254697661338308161)
    ·
      refine ⟨27029950691023246003731121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36039934254697661338308161 27029950691023246003731121)
      ·
        refine ⟨20272463018267434502798341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27029950691023246003731121 20272463018267434502798341)
        ·
          refine ⟨3801086815925143969274689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20272463018267434502798341 3801086815925143969274689)
          ·
            refine ⟨2850815111943857976956017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3801086815925143969274689 2850815111943857976956017)
            ·
              refine ⟨2138111333957893482717013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2850815111943857976956017 2138111333957893482717013)
              ·
                refine ⟨12527996097409532125295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2138111333957893482717013 12527996097409532125295)
                ·
                  rfl

theorem cell23_658751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 9].length) (baseStart_658751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658751 prefixEnd_658751 := by exact prefixLift 658751
  have htrace : WordTrace (prefixWord ++ tailWord_658751) baseStart_658751 baseEnd_658751 := by
    simpa [prefixWord, tailWord_658751, baseEnd_658751] using wordTrace_append hprefix tailTrace_658751
  have hstable : (prefixWord ++ tailWord_658751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658751).length < 2 ^ (prefixWord ++ tailWord_658751).sum := by decide
  have hdescent : baseEnd_658751 < baseStart_658751 := by decide
  rcases family_descends (prefixWord ++ tailWord_658751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658811 : List Nat := [1, 1, 1, 1, 1, 6, 1, 2, 1, 8]
def baseStart_658811 : Nat := 118140960795 + 658811 * 2 ^ 59
def prefixEnd_658811 : Nat := 4983230072969 + 3 ^ 40 * 658811 * 2
def baseEnd_658811 : Nat := 112762234489775710877563

theorem tailTrace_658811 : CollatzResearch.WordTrace tailWord_658811 prefixEnd_658811 112762234489775710877563 := by
  unfold tailWord_658811
  simp only [CollatzResearch.WordTrace]
  refine ⟨24028811216247737806056287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16019207477498491870704191 24028811216247737806056287)
  ·
    refine ⟨36043216824371606709084431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24028811216247737806056287 36043216824371606709084431)
    ·
      refine ⟨54064825236557410063626647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36043216824371606709084431 54064825236557410063626647)
      ·
        refine ⟨81097237854836115095439971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54064825236557410063626647 81097237854836115095439971)
        ·
          refine ⟨121645856782254172643159957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81097237854836115095439971 121645856782254172643159957)
          ·
            refine ⟨5702149536668164342648123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 121645856782254172643159957 5702149536668164342648123)
            ·
              refine ⟨8553224305002246513972185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5702149536668164342648123 8553224305002246513972185)
              ·
                refine ⟨6414918228751684885479139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8553224305002246513972185 6414918228751684885479139)
                ·
                  refine ⟨9622377343127527328218709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6414918228751684885479139 9622377343127527328218709)
                  ·
                    refine ⟨112762234489775710877563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9622377343127527328218709 112762234489775710877563)
                    ·
                      rfl

theorem cell23_658811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 8].length) (baseStart_658811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658811 prefixEnd_658811 := by exact prefixLift 658811
  have htrace : WordTrace (prefixWord ++ tailWord_658811) baseStart_658811 baseEnd_658811 := by
    simpa [prefixWord, tailWord_658811, baseEnd_658811] using wordTrace_append hprefix tailTrace_658811
  have hstable : (prefixWord ++ tailWord_658811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658811).length < 2 ^ (prefixWord ++ tailWord_658811).sum := by decide
  have hdescent : baseEnd_658811 < baseStart_658811 := by decide
  rcases family_descends (prefixWord ++ tailWord_658811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658846 : List Nat := [4, 3, 1, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_658846 : Nat := 118140960795 + 658846 * 2 ^ 59
def prefixEnd_658846 : Nat := 4983230072969 + 3 ^ 40 * 658846 * 2
def baseEnd_658846 : Nat := 338304675292234495695029

theorem tailTrace_658846 : CollatzResearch.WordTrace tailWord_658846 prefixEnd_658846 338304675292234495695029 := by
  unfold tailWord_658846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3003760971390117347947549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16020058514080625855720261 3003760971390117347947549)
  ·
    refine ⟨1126410364271294005480331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3003760971390117347947549 1126410364271294005480331)
    ·
      refine ⟨1689615546406941008220497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1126410364271294005480331 1689615546406941008220497)
      ·
        refine ⟨1267211659805205756165373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1689615546406941008220497 1267211659805205756165373)
        ·
          refine ⟨475204372426952158562015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1267211659805205756165373 475204372426952158562015)
          ·
            refine ⟨712806558640428237843023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475204372426952158562015 712806558640428237843023)
            ·
              refine ⟨1069209837960642356764535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712806558640428237843023 1069209837960642356764535)
              ·
                refine ⟨1603814756940963535146803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069209837960642356764535 1603814756940963535146803)
                ·
                  refine ⟨2405722135411445302720205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1603814756940963535146803 2405722135411445302720205)
                  ·
                    refine ⟨902145800779291988520077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2405722135411445302720205 902145800779291988520077)
                    ·
                      refine ⟨338304675292234495695029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 902145800779291988520077 338304675292234495695029)
                      ·
                        rfl

theorem cell23_658846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_658846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658846 prefixEnd_658846 := by exact prefixLift 658846
  have htrace : WordTrace (prefixWord ++ tailWord_658846) baseStart_658846 baseEnd_658846 := by
    simpa [prefixWord, tailWord_658846, baseEnd_658846] using wordTrace_append hprefix tailTrace_658846
  have hstable : (prefixWord ++ tailWord_658846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658846).length < 2 ^ (prefixWord ++ tailWord_658846).sum := by decide
  have hdescent : baseEnd_658846 < baseStart_658846 := by decide
  rcases family_descends (prefixWord ++ tailWord_658846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658848 : List Nat := [2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 4]
def baseStart_658848 : Nat := 118140960795 + 658848 * 2 ^ 59
def prefixEnd_658848 : Nat := 4983230072969 + 3 ^ 40 * 658848 * 2
def baseEnd_658848 : Nat := 338305702253543487870019

theorem tailTrace_658848 : CollatzResearch.WordTrace tailWord_658848 prefixEnd_658848 338305702253543487870019 := by
  unfold tailWord_658848
  simp only [CollatzResearch.WordTrace]
  refine ⟨12015080358556846562576599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16020107144742462083435465 12015080358556846562576599)
  ·
    refine ⟨18022620537835269843864899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12015080358556846562576599 18022620537835269843864899)
    ·
      refine ⟨27033930806752904765797349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18022620537835269843864899 27033930806752904765797349)
      ·
        refine ⟨5068862026266169643587003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27033930806752904765797349 5068862026266169643587003)
        ·
          refine ⟨7603293039399254465380505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5068862026266169643587003 7603293039399254465380505)
          ·
            refine ⟨5702469779549440849035379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7603293039399254465380505 5702469779549440849035379)
            ·
              refine ⟨8553704669324161273553069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5702469779549440849035379 8553704669324161273553069)
              ·
                refine ⟨3207639250996560477582401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8553704669324161273553069 3207639250996560477582401)
                ·
                  refine ⟨2405729438247420358186801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3207639250996560477582401 2405729438247420358186801)
                  ·
                    refine ⟨1804297078685565268640101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2405729438247420358186801 1804297078685565268640101)
                    ·
                      refine ⟨338305702253543487870019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1804297078685565268640101 338305702253543487870019)
                      ·
                        rfl

theorem cell23_658848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_658848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658848 prefixEnd_658848 := by exact prefixLift 658848
  have htrace : WordTrace (prefixWord ++ tailWord_658848) baseStart_658848 baseEnd_658848 := by
    simpa [prefixWord, tailWord_658848, baseEnd_658848] using wordTrace_append hprefix tailTrace_658848
  have hstable : (prefixWord ++ tailWord_658848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658848).length < 2 ^ (prefixWord ++ tailWord_658848).sum := by decide
  have hdescent : baseEnd_658848 < baseStart_658848 := by decide
  rcases family_descends (prefixWord ++ tailWord_658848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658856 : List Nat := [2, 1, 6, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_658856 : Nat := 118140960795 + 658856 * 2 ^ 59
def prefixEnd_658856 : Nat := 4983230072969 + 3 ^ 40 * 658856 * 2
def baseEnd_658856 : Nat := 338309810098779456569983

theorem tailTrace_658856 : CollatzResearch.WordTrace tailWord_658856 prefixEnd_658856 338309810098779456569983 := by
  unfold tailWord_658856
  simp only [CollatzResearch.WordTrace]
  refine ⟨12015226250542355245722211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16020301667389806994296281 12015226250542355245722211)
  ·
    refine ⟨18022839375813532868583317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12015226250542355245722211 18022839375813532868583317)
    ·
      refine ⟨844820595741259353214843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18022839375813532868583317 844820595741259353214843)
      ·
        refine ⟨1267230893611889029822265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 844820595741259353214843 1267230893611889029822265)
        ·
          refine ⟨950423170208916772366699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1267230893611889029822265 950423170208916772366699)
          ·
            refine ⟨1425634755313375158550049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950423170208916772366699 1425634755313375158550049)
            ·
              refine ⟨1069226066485031368912537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1425634755313375158550049 1069226066485031368912537)
              ·
                refine ⟨801919549863773526684403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1069226066485031368912537 801919549863773526684403)
                ·
                  refine ⟨1202879324795660290026605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801919549863773526684403 1202879324795660290026605)
                  ·
                    refine ⟨451079746798372608759977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1202879324795660290026605 451079746798372608759977)
                    ·
                      refine ⟨338309810098779456569983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 451079746798372608759977 338309810098779456569983)
                      ·
                        rfl

theorem cell23_658856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_658856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658856 prefixEnd_658856 := by exact prefixLift 658856
  have htrace : WordTrace (prefixWord ++ tailWord_658856) baseStart_658856 baseEnd_658856 := by
    simpa [prefixWord, tailWord_658856, baseEnd_658856] using wordTrace_append hprefix tailTrace_658856
  have hstable : (prefixWord ++ tailWord_658856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658856).length < 2 ^ (prefixWord ++ tailWord_658856).sum := by decide
  have hdescent : baseEnd_658856 < baseStart_658856 := by decide
  rcases family_descends (prefixWord ++ tailWord_658856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658922 : List Nat := [3, 1, 3, 1, 4, 1, 2, 1, 2, 5]
def baseStart_658922 : Nat := 118140960795 + 658922 * 2 ^ 59
def prefixEnd_658922 : Nat := 4983230072969 + 3 ^ 40 * 658922 * 2
def baseEnd_658922 : Nat := 112781233273992066114893

theorem tailTrace_658922 : CollatzResearch.WordTrace tailWord_658922 prefixEnd_658922 112781233273992066114893 := by
  unfold tailWord_658922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6008214929711400940836755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16021906479230402508898013 6008214929711400940836755)
  ·
    refine ⟨9012322394567101411255133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6008214929711400940836755 9012322394567101411255133)
    ·
      refine ⟨3379620897962663029220675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9012322394567101411255133 3379620897962663029220675)
      ·
        refine ⟨5069431346943994543831013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3379620897962663029220675 5069431346943994543831013)
        ·
          refine ⟨950518377551998976968315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5069431346943994543831013 950518377551998976968315)
          ·
            refine ⟨1425777566327998465452473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950518377551998976968315 1425777566327998465452473)
            ·
              refine ⟨1069333174745998849089355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1425777566327998465452473 1069333174745998849089355)
              ·
                refine ⟨1603999762118998273634033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069333174745998849089355 1603999762118998273634033)
                ·
                  refine ⟨1202999821589248705225525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1603999762118998273634033 1202999821589248705225525)
                  ·
                    refine ⟨112781233273992066114893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1202999821589248705225525 112781233273992066114893)
                    ·
                      rfl

theorem cell23_658922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_658922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658922 prefixEnd_658922 := by exact prefixLift 658922
  have htrace : WordTrace (prefixWord ++ tailWord_658922) baseStart_658922 baseEnd_658922 := by
    simpa [prefixWord, tailWord_658922, baseEnd_658922] using wordTrace_append hprefix tailTrace_658922
  have hstable : (prefixWord ++ tailWord_658922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658922).length < 2 ^ (prefixWord ++ tailWord_658922).sum := by decide
  have hdescent : baseEnd_658922 < baseStart_658922 := by decide
  rcases family_descends (prefixWord ++ tailWord_658922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658938 : List Nat := [3, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6]
def baseStart_658938 : Nat := 118140960795 + 658938 * 2 ^ 59
def prefixEnd_658938 : Nat := 4983230072969 + 3 ^ 40 * 658938 * 2
def baseEnd_658938 : Nat := 338351915512448135744605

theorem tailTrace_658938 : CollatzResearch.WordTrace tailWord_658938 prefixEnd_658938 338351915512448135744605 := by
  unfold tailWord_658938
  simp only [CollatzResearch.WordTrace]
  refine ⟨6008360821696909623982367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16022295524525092330619645 6008360821696909623982367)
  ·
    refine ⟨9012541232545364435973551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6008360821696909623982367 9012541232545364435973551)
    ·
      refine ⟨13518811848818046653960327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9012541232545364435973551 13518811848818046653960327)
      ·
        refine ⟨20278217773227069980940491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13518811848818046653960327 20278217773227069980940491)
        ·
          refine ⟨30417326659840604971410737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20278217773227069980940491 30417326659840604971410737)
          ·
            refine ⟨22812994994880453728558053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30417326659840604971410737 22812994994880453728558053)
            ·
              refine ⟨4277436561540085074104635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22812994994880453728558053 4277436561540085074104635)
              ·
                refine ⟨6416154842310127611156953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4277436561540085074104635 6416154842310127611156953)
                ·
                  refine ⟨4812116131732595708367715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6416154842310127611156953 4812116131732595708367715)
                  ·
                    refine ⟨7218174197598893562551573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4812116131732595708367715 7218174197598893562551573)
                    ·
                      refine ⟨338351915512448135744605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7218174197598893562551573 338351915512448135744605)
                      ·
                        rfl

theorem cell23_658938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_658938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658938 prefixEnd_658938 := by exact prefixLift 658938
  have htrace : WordTrace (prefixWord ++ tailWord_658938) baseStart_658938 baseEnd_658938 := by
    simpa [prefixWord, tailWord_658938, baseEnd_658938] using wordTrace_append hprefix tailTrace_658938
  have hstable : (prefixWord ++ tailWord_658938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658938).length < 2 ^ (prefixWord ++ tailWord_658938).sum := by decide
  have hdescent : baseEnd_658938 < baseStart_658938 := by decide
  rcases family_descends (prefixWord ++ tailWord_658938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658965 : List Nat := [1, 3, 2, 1, 3, 2, 2, 3, 6]
def baseStart_658965 : Nat := 118140960795 + 658965 * 2 ^ 59
def prefixEnd_658965 : Nat := 4983230072969 + 3 ^ 40 * 658965 * 2
def baseEnd_658965 : Nat := 37596197721124392234109

theorem tailTrace_658965 : CollatzResearch.WordTrace tailWord_658965 prefixEnd_658965 37596197721124392234109 := by
  unfold tailWord_658965
  simp only [CollatzResearch.WordTrace]
  refine ⟨24034428057689822107162349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16022952038459881404774899 24034428057689822107162349)
  ·
    refine ⟨9012910521633683290185881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24034428057689822107162349 9012910521633683290185881)
    ·
      refine ⟨6759682891225262467639411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9012910521633683290185881 6759682891225262467639411)
      ·
        refine ⟨10139524336837893701459117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6759682891225262467639411 10139524336837893701459117)
        ·
          refine ⟨3802321626314210138047169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10139524336837893701459117 3802321626314210138047169)
          ·
            refine ⟨2851741219735657603535377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3802321626314210138047169 2851741219735657603535377)
            ·
              refine ⟨2138805914801743202651533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2851741219735657603535377 2138805914801743202651533)
              ·
                refine ⟨802052218050653700994325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2138805914801743202651533 802052218050653700994325)
                ·
                  refine ⟨37596197721124392234109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 802052218050653700994325 37596197721124392234109)
                  ·
                    rfl

theorem cell23_658965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 3, 6].length) (baseStart_658965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658965 prefixEnd_658965 := by exact prefixLift 658965
  have htrace : WordTrace (prefixWord ++ tailWord_658965) baseStart_658965 baseEnd_658965 := by
    simpa [prefixWord, tailWord_658965, baseEnd_658965] using wordTrace_append hprefix tailTrace_658965
  have hstable : (prefixWord ++ tailWord_658965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658965).length < 2 ^ (prefixWord ++ tailWord_658965).sum := by decide
  have hdescent : baseEnd_658965 < baseStart_658965 := by decide
  rcases family_descends (prefixWord ++ tailWord_658965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658979 : List Nat := [1, 1, 1, 4, 5, 2, 1, 1, 2, 2, 3]
def baseStart_658979 : Nat := 118140960795 + 658979 * 2 ^ 59
def prefixEnd_658979 : Nat := 4983230072969 + 3 ^ 40 * 658979 * 2
def baseEnd_658979 : Nat := 338372968219282475331917

theorem tailTrace_658979 : CollatzResearch.WordTrace tailWord_658979 prefixEnd_658979 338372968219282475331917 := by
  unfold tailWord_658979
  simp only [CollatzResearch.WordTrace]
  refine ⟨24034938679639102498171991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16023292453092734998781327 24034938679639102498171991)
  ·
    refine ⟨36052408019458653747257987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24034938679639102498171991 36052408019458653747257987)
    ·
      refine ⟨54078612029187980620886981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36052408019458653747257987 54078612029187980620886981)
      ·
        refine ⟨10139739755472746366416309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54078612029187980620886981 10139739755472746366416309)
        ·
          refine ⟨950600602075569971851529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10139739755472746366416309 950600602075569971851529)
          ·
            refine ⟨712950451556677478888647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 950600602075569971851529 712950451556677478888647)
            ·
              refine ⟨1069425677335016218332971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712950451556677478888647 1069425677335016218332971)
              ·
                refine ⟨1604138516002524327499457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069425677335016218332971 1604138516002524327499457)
                ·
                  refine ⟨1203103887001893245624593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1604138516002524327499457 1203103887001893245624593)
                  ·
                    refine ⟨902327915251419934218445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1203103887001893245624593 902327915251419934218445)
                    ·
                      refine ⟨338372968219282475331917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 902327915251419934218445 338372968219282475331917)
                      ·
                        rfl

theorem cell23_658979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_658979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658979 prefixEnd_658979 := by exact prefixLift 658979
  have htrace : WordTrace (prefixWord ++ tailWord_658979) baseStart_658979 baseEnd_658979 := by
    simpa [prefixWord, tailWord_658979, baseEnd_658979] using wordTrace_append hprefix tailTrace_658979
  have hstable : (prefixWord ++ tailWord_658979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658979).length < 2 ^ (prefixWord ++ tailWord_658979).sum := by decide
  have hdescent : baseEnd_658979 < baseStart_658979 := by decide
  rcases family_descends (prefixWord ++ tailWord_658979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_658988 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 5]
def baseStart_658988 : Nat := 118140960795 + 658988 * 2 ^ 59
def prefixEnd_658988 : Nat := 4983230072969 + 3 ^ 40 * 658988 * 2
def baseEnd_658988 : Nat := 338377589545172940119375

theorem tailTrace_658988 : CollatzResearch.WordTrace tailWord_658988 prefixEnd_658988 338377589545172940119375 := by
  unfold tailWord_658988
  simp only [CollatzResearch.WordTrace]
  refine ⟨12017633468303248517624809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16023511291070998023499745 12017633468303248517624809)
  ·
    refine ⟨9013225101227436388218607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12017633468303248517624809 9013225101227436388218607)
    ·
      refine ⟨13519837651841154582327911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9013225101227436388218607 13519837651841154582327911)
      ·
        refine ⟨20279756477761731873491867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13519837651841154582327911 20279756477761731873491867)
        ·
          refine ⟨30419634716642597810237801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20279756477761731873491867 30419634716642597810237801)
          ·
            refine ⟨22814726037481948357678351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30419634716642597810237801 22814726037481948357678351)
            ·
              refine ⟨34222089056222922536517527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22814726037481948357678351 34222089056222922536517527)
              ·
                refine ⟨51333133584334383804776291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34222089056222922536517527 51333133584334383804776291)
                ·
                  refine ⟨76999700376501575707164437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51333133584334383804776291 76999700376501575707164437)
                  ·
                    refine ⟨3609360955148511361273333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 76999700376501575707164437 3609360955148511361273333)
                    ·
                      refine ⟨338377589545172940119375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3609360955148511361273333 338377589545172940119375)
                      ·
                        rfl

theorem cell23_658988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_658988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_658988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_658988 prefixEnd_658988 := by exact prefixLift 658988
  have htrace : WordTrace (prefixWord ++ tailWord_658988) baseStart_658988 baseEnd_658988 := by
    simpa [prefixWord, tailWord_658988, baseEnd_658988] using wordTrace_append hprefix tailTrace_658988
  have hstable : (prefixWord ++ tailWord_658988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_658988).length < 2 ^ (prefixWord ++ tailWord_658988).sum := by decide
  have hdescent : baseEnd_658988 < baseStart_658988 := by decide
  rcases family_descends (prefixWord ++ tailWord_658988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659002 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2]
def baseStart_659002 : Nat := 118140960795 + 659002 * 2 ^ 59
def prefixEnd_659002 : Nat := 4983230072969 + 3 ^ 40 * 659002 * 2
def baseEnd_659002 : Nat := 338384778274335885344311

theorem tailTrace_659002 : CollatzResearch.WordTrace tailWord_659002 prefixEnd_659002 338384778274335885344311 := by
  unfold tailWord_659002
  simp only [CollatzResearch.WordTrace]
  refine ⟨6008944389638944356564815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16023851705703851617506173 6008944389638944356564815)
  ·
    refine ⟨9013416584458416534847223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6008944389638944356564815 9013416584458416534847223)
    ·
      refine ⟨13520124876687624802270835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9013416584458416534847223 13520124876687624802270835)
      ·
        refine ⟨20280187315031437203406253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13520124876687624802270835 20280187315031437203406253)
        ·
          refine ⟨7605070243136788951277345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20280187315031437203406253 7605070243136788951277345)
          ·
            refine ⟨5703802682352591713458009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7605070243136788951277345 5703802682352591713458009)
            ·
              refine ⟨4277852011764443785093507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5703802682352591713458009 4277852011764443785093507)
              ·
                refine ⟨6416778017646665677640261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4277852011764443785093507 6416778017646665677640261)
                ·
                  refine ⟨1203145878308749814557549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6416778017646665677640261 1203145878308749814557549)
                  ·
                    refine ⟨451179704365781180459081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1203145878308749814557549 451179704365781180459081)
                    ·
                      refine ⟨338384778274335885344311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 451179704365781180459081 338384778274335885344311)
                      ·
                        rfl

theorem cell23_659002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2].length) (baseStart_659002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659002 prefixEnd_659002 := by exact prefixLift 659002
  have htrace : WordTrace (prefixWord ++ tailWord_659002) baseStart_659002 baseEnd_659002 := by
    simpa [prefixWord, tailWord_659002, baseEnd_659002] using wordTrace_append hprefix tailTrace_659002
  have hstable : (prefixWord ++ tailWord_659002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659002).length < 2 ^ (prefixWord ++ tailWord_659002).sum := by decide
  have hdescent : baseEnd_659002 < baseStart_659002 := by decide
  rcases family_descends (prefixWord ++ tailWord_659002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659009 : List Nat := [1, 2, 5, 1, 1, 1, 4, 1, 3, 1, 3]
def baseStart_659009 : Nat := 118140960795 + 659009 * 2 ^ 59
def prefixEnd_659009 : Nat := 4983230072969 + 3 ^ 40 * 659009 * 2
def baseEnd_659009 : Nat := 338388372638917357956779

theorem tailTrace_659009 : CollatzResearch.WordTrace tailWord_659009 prefixEnd_659009 338388372638917357956779 := by
  unfold tailWord_659009
  simp only [CollatzResearch.WordTrace]
  refine ⟨24036032869530417621764081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16024021913020278414509387 24036032869530417621764081)
  ·
    refine ⟨18027024652147813216323061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24036032869530417621764081 18027024652147813216323061)
    ·
      refine ⟨1690033561138857489030287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18027024652147813216323061 1690033561138857489030287)
      ·
        refine ⟨2535050341708286233545431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1690033561138857489030287 2535050341708286233545431)
        ·
          refine ⟨3802575512562429350318147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2535050341708286233545431 3802575512562429350318147)
          ·
            refine ⟨5703863268843644025477221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3802575512562429350318147 5703863268843644025477221)
            ·
              refine ⟨1069474362908183254776979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5703863268843644025477221 1069474362908183254776979)
              ·
                refine ⟨1604211544362274882165469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069474362908183254776979 1604211544362274882165469)
                ·
                  refine ⟨601579329135853080812051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1604211544362274882165469 601579329135853080812051)
                  ·
                    refine ⟨902368993703779621218077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 601579329135853080812051 902368993703779621218077)
                    ·
                      refine ⟨338388372638917357956779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 902368993703779621218077 338388372638917357956779)
                      ·
                        rfl

theorem cell23_659009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_659009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659009 prefixEnd_659009 := by exact prefixLift 659009
  have htrace : WordTrace (prefixWord ++ tailWord_659009) baseStart_659009 baseEnd_659009 := by
    simpa [prefixWord, tailWord_659009, baseEnd_659009] using wordTrace_append hprefix tailTrace_659009
  have hstable : (prefixWord ++ tailWord_659009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659009).length < 2 ^ (prefixWord ++ tailWord_659009).sum := by decide
  have hdescent : baseEnd_659009 < baseStart_659009 := by decide
  rcases family_descends (prefixWord ++ tailWord_659009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659062 : List Nat := [5, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6]
def baseStart_659062 : Nat := 118140960795 + 659062 * 2 ^ 59
def prefixEnd_659062 : Nat := 4983230072969 + 3 ^ 40 * 659062 * 2
def baseEnd_659062 : Nat := 338415587113605650594035

theorem tailTrace_659062 : CollatzResearch.WordTrace tailWord_659062 prefixEnd_659062 338415587113605650594035 := by
  unfold tailWord_659062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1502372871146150479590215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16025310625558938448962293 1502372871146150479590215)
  ·
    refine ⟨2253559306719225719385323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1502372871146150479590215 2253559306719225719385323)
    ·
      refine ⟨3380338960078838579077985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2253559306719225719385323 3380338960078838579077985)
      ·
        refine ⟨2535254220059128934308489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3380338960078838579077985 2535254220059128934308489)
        ·
          refine ⟨1901440665044346700731367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2535254220059128934308489 1901440665044346700731367)
          ·
            refine ⟨2852160997566520051097051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1901440665044346700731367 2852160997566520051097051)
            ·
              refine ⟨4278241496349780076645577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2852160997566520051097051 4278241496349780076645577)
              ·
                refine ⟨3208681122262335057484183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4278241496349780076645577 3208681122262335057484183)
                ·
                  refine ⟨4813021683393502586226275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3208681122262335057484183 4813021683393502586226275)
                  ·
                    refine ⟨7219532525090253879339413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4813021683393502586226275 7219532525090253879339413)
                    ·
                      refine ⟨338415587113605650594035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7219532525090253879339413 338415587113605650594035)
                      ·
                        rfl

theorem cell23_659062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_659062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659062 prefixEnd_659062 := by exact prefixLift 659062
  have htrace : WordTrace (prefixWord ++ tailWord_659062) baseStart_659062 baseEnd_659062 := by
    simpa [prefixWord, tailWord_659062, baseEnd_659062] using wordTrace_append hprefix tailTrace_659062
  have hstable : (prefixWord ++ tailWord_659062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659062).length < 2 ^ (prefixWord ++ tailWord_659062).sum := by decide
  have hdescent : baseEnd_659062 < baseStart_659062 := by decide
  rcases family_descends (prefixWord ++ tailWord_659062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659086 : List Nat := [4, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3]
def baseStart_659086 : Nat := 118140960795 + 659086 * 2 ^ 59
def prefixEnd_659086 : Nat := 4983230072969 + 3 ^ 40 * 659086 * 2
def baseEnd_659086 : Nat := 338427910649313556693925

theorem tailTrace_659086 : CollatzResearch.WordTrace tailWord_659086 prefixEnd_659086 338427910649313556693925 := by
  unfold tailWord_659086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3004855161281432471539639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16025894193500973181544741 3004855161281432471539639)
  ·
    refine ⟨4507282741922148707309459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3004855161281432471539639 4507282741922148707309459)
    ·
      refine ⟨6760924112883223060964189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4507282741922148707309459 6760924112883223060964189)
      ·
        refine ⟨2535346542331208647861571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6760924112883223060964189 2535346542331208647861571)
        ·
          refine ⟨3803019813496812971792357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2535346542331208647861571 3803019813496812971792357)
          ·
            refine ⟨713066215030652432211067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3803019813496812971792357 713066215030652432211067)
            ·
              refine ⟨1069599322545978648316601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713066215030652432211067 1069599322545978648316601)
              ·
                refine ⟨802199491909483986237451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1069599322545978648316601 802199491909483986237451)
                ·
                  refine ⟨1203299237864225979356177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 802199491909483986237451 1203299237864225979356177)
                  ·
                    refine ⟨902474428398169484517133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1203299237864225979356177 902474428398169484517133)
                    ·
                      refine ⟨338427910649313556693925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 902474428398169484517133 338427910649313556693925)
                      ·
                        rfl

theorem cell23_659086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_659086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659086 prefixEnd_659086 := by exact prefixLift 659086
  have htrace : WordTrace (prefixWord ++ tailWord_659086) baseStart_659086 baseEnd_659086 := by
    simpa [prefixWord, tailWord_659086, baseEnd_659086] using wordTrace_append hprefix tailTrace_659086
  have hstable : (prefixWord ++ tailWord_659086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659086).length < 2 ^ (prefixWord ++ tailWord_659086).sum := by decide
  have hdescent : baseEnd_659086 < baseStart_659086 := by decide
  rcases family_descends (prefixWord ++ tailWord_659086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659103 : List Nat := [1, 1, 2, 7, 1, 1, 3, 1, 1, 2, 3]
def baseStart_659103 : Nat := 118140960795 + 659103 * 2 ^ 59
def prefixEnd_659103 : Nat := 4983230072969 + 3 ^ 40 * 659103 * 2
def baseEnd_659103 : Nat := 338436639820439990181347

theorem tailTrace_659103 : CollatzResearch.WordTrace tailWord_659103 prefixEnd_659103 338436639820439990181347 := by
  unfold tailWord_659103
  simp only [CollatzResearch.WordTrace]
  refine ⟨24039461331189871675685963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16026307554126581117123975 24039461331189871675685963)
  ·
    refine ⟨36059191996784807513528945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24039461331189871675685963 36059191996784807513528945)
    ·
      refine ⟨27044393997588605635146709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36059191996784807513528945 27044393997588605635146709)
      ·
        refine ⟨633852984318482944573751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 27044393997588605635146709 633852984318482944573751)
        ·
          refine ⟨950779476477724416860627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633852984318482944573751 950779476477724416860627)
          ·
            refine ⟨1426169214716586625290941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950779476477724416860627 1426169214716586625290941)
            ·
              refine ⟨534813455518719984484103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1426169214716586625290941 534813455518719984484103)
              ·
                refine ⟨802220183278079976726155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534813455518719984484103 802220183278079976726155)
                ·
                  refine ⟨1203330274917119965089233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 802220183278079976726155 1203330274917119965089233)
                  ·
                    refine ⟨902497706187839973816925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1203330274917119965089233 902497706187839973816925)
                    ·
                      refine ⟨338436639820439990181347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 902497706187839973816925 338436639820439990181347)
                      ·
                        rfl

theorem cell23_659103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_659103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659103 prefixEnd_659103 := by exact prefixLift 659103
  have htrace : WordTrace (prefixWord ++ tailWord_659103) baseStart_659103 baseEnd_659103 := by
    simpa [prefixWord, tailWord_659103, baseEnd_659103] using wordTrace_append hprefix tailTrace_659103
  have hstable : (prefixWord ++ tailWord_659103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659103).length < 2 ^ (prefixWord ++ tailWord_659103).sum := by decide
  have hdescent : baseEnd_659103 < baseStart_659103 := by decide
  rcases family_descends (prefixWord ++ tailWord_659103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659109 : List Nat := [1, 3, 1, 2, 1, 2, 2, 5, 1, 3, 2]
def baseStart_659109 : Nat := 118140960795 + 659109 * 2 ^ 59
def prefixEnd_659109 : Nat := 4983230072969 + 3 ^ 40 * 659109 * 2
def baseEnd_659109 : Nat := 338439720704366966706319

theorem tailTrace_659109 : CollatzResearch.WordTrace tailWord_659109 prefixEnd_659109 338439720704366966706319 := by
  unfold tailWord_659109
  simp only [CollatzResearch.WordTrace]
  refine ⟨24039680169168134700404381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16026453446112089800269587 24039680169168134700404381)
  ·
    refine ⟨9014880063438050512651643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24039680169168134700404381 9014880063438050512651643)
    ·
      refine ⟨13522320095157075768977465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9014880063438050512651643 13522320095157075768977465)
      ·
        refine ⟨10141740071367806826733099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13522320095157075768977465 10141740071367806826733099)
        ·
          refine ⟨15212610107051710240099649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10141740071367806826733099 15212610107051710240099649)
          ·
            refine ⟨11409457580288782680074737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15212610107051710240099649 11409457580288782680074737)
            ·
              refine ⟨8557093185216587010056053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11409457580288782680074737 8557093185216587010056053)
              ·
                refine ⟨802227486114055032192755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8557093185216587010056053 802227486114055032192755)
                ·
                  refine ⟨1203341229171082548289133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 802227486114055032192755 1203341229171082548289133)
                  ·
                    refine ⟨451252960939155955608425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1203341229171082548289133 451252960939155955608425)
                    ·
                      refine ⟨338439720704366966706319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 451252960939155955608425 338439720704366966706319)
                      ·
                        rfl

theorem cell23_659109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_659109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659109 prefixEnd_659109 := by exact prefixLift 659109
  have htrace : WordTrace (prefixWord ++ tailWord_659109) baseStart_659109 baseEnd_659109 := by
    simpa [prefixWord, tailWord_659109, baseEnd_659109] using wordTrace_append hprefix tailTrace_659109
  have hstable : (prefixWord ++ tailWord_659109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659109).length < 2 ^ (prefixWord ++ tailWord_659109).sum := by decide
  have hdescent : baseEnd_659109 < baseStart_659109 := by decide
  rcases family_descends (prefixWord ++ tailWord_659109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659132 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 2, 6]
def baseStart_659132 : Nat := 118140960795 + 659132 * 2 ^ 59
def prefixEnd_659132 : Nat := 4983230072969 + 3 ^ 40 * 659132 * 2
def baseEnd_659132 : Nat := 112817176919806792239571

theorem tailTrace_659132 : CollatzResearch.WordTrace tailWord_659132 prefixEnd_659132 112817176919806792239571 := by
  unfold tailWord_659132
  simp only [CollatzResearch.WordTrace]
  refine ⟨12020259524042404814245825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16027012698723206418994433 12020259524042404814245825)
  ·
    refine ⟨9015194643031803610684369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12020259524042404814245825 9015194643031803610684369)
    ·
      refine ⟨6761395982273852708013277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9015194643031803610684369 6761395982273852708013277)
      ·
        refine ⟨2535523493352694765504979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6761395982273852708013277 2535523493352694765504979)
        ·
          refine ⟨3803285240029042148257469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2535523493352694765504979 3803285240029042148257469)
          ·
            refine ⟨1426231965010890805596551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3803285240029042148257469 1426231965010890805596551)
            ·
              refine ⟨2139347947516336208394827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1426231965010890805596551 2139347947516336208394827)
              ·
                refine ⟨3209021921274504312592241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2139347947516336208394827 3209021921274504312592241)
                ·
                  refine ⟨2406766440955878234444181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3209021921274504312592241 2406766440955878234444181)
                  ·
                    refine ⟨112817176919806792239571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2406766440955878234444181 112817176919806792239571)
                    ·
                      rfl

theorem cell23_659132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_659132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659132 prefixEnd_659132 := by exact prefixLift 659132
  have htrace : WordTrace (prefixWord ++ tailWord_659132) baseStart_659132 baseEnd_659132 := by
    simpa [prefixWord, tailWord_659132, baseEnd_659132] using wordTrace_append hprefix tailTrace_659132
  have hstable : (prefixWord ++ tailWord_659132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659132).length < 2 ^ (prefixWord ++ tailWord_659132).sum := by decide
  have hdescent : baseEnd_659132 < baseStart_659132 := by decide
  rcases family_descends (prefixWord ++ tailWord_659132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659156 : List Nat := [2, 4, 1, 3, 1, 1, 2, 2, 1, 4, 2]
def baseStart_659156 : Nat := 118140960795 + 659156 * 2 ^ 59
def prefixEnd_659156 : Nat := 4983230072969 + 3 ^ 40 * 659156 * 2
def baseEnd_659156 : Nat := 338463854295128282818603

theorem tailTrace_659156 : CollatzResearch.WordTrace tailWord_659156 prefixEnd_659156 338463854295128282818603 := by
  unfold tailWord_659156
  simp only [CollatzResearch.WordTrace]
  refine ⟨12020697199998930863682661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16027596266665241151576881 12020697199998930863682661)
  ·
    refine ⟨2253880724999799536940499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12020697199998930863682661 2253880724999799536940499)
    ·
      refine ⟨3380821087499699305410749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2253880724999799536940499 3380821087499699305410749)
      ·
        refine ⟨1267807907812387239529031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3380821087499699305410749 1267807907812387239529031)
        ·
          refine ⟨1901711861718580859293547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1267807907812387239529031 1901711861718580859293547)
          ·
            refine ⟨2852567792577871288940321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1901711861718580859293547 2852567792577871288940321)
            ·
              refine ⟨2139425844433403466705241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2852567792577871288940321 2139425844433403466705241)
              ·
                refine ⟨1604569383325052600028931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2139425844433403466705241 1604569383325052600028931)
                ·
                  refine ⟨2406854074987578900043397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1604569383325052600028931 2406854074987578900043397)
                  ·
                    refine ⟨451285139060171043758137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2406854074987578900043397 451285139060171043758137)
                    ·
                      refine ⟨338463854295128282818603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 451285139060171043758137 338463854295128282818603)
                      ·
                        rfl

theorem cell23_659156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_659156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659156 prefixEnd_659156 := by exact prefixLift 659156
  have htrace : WordTrace (prefixWord ++ tailWord_659156) baseStart_659156 baseEnd_659156 := by
    simpa [prefixWord, tailWord_659156, baseEnd_659156] using wordTrace_append hprefix tailTrace_659156
  have hstable : (prefixWord ++ tailWord_659156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659156).length < 2 ^ (prefixWord ++ tailWord_659156).sum := by decide
  have hdescent : baseEnd_659156 < baseStart_659156 := by decide
  rcases family_descends (prefixWord ++ tailWord_659156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659172 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 4, 3, 3]
def baseStart_659172 : Nat := 118140960795 + 659172 * 2 ^ 59
def prefixEnd_659172 : Nat := 4983230072969 + 3 ^ 40 * 659172 * 2
def baseEnd_659172 : Nat := 338472069985600220218529

theorem tailTrace_659172 : CollatzResearch.WordTrace tailWord_659172 prefixEnd_659172 338472069985600220218529 := by
  unfold tailWord_659172
  simp only [CollatzResearch.WordTrace]
  refine ⟨12020988983969948229973885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16027985311959930973298513 12020988983969948229973885)
  ·
    refine ⟨4507870868988730586240207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12020988983969948229973885 4507870868988730586240207)
    ·
      refine ⟨6761806303483095879360311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4507870868988730586240207 6761806303483095879360311)
      ·
        refine ⟨10142709455224643819040467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6761806303483095879360311 10142709455224643819040467)
        ·
          refine ⟨15214064182836965728560701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10142709455224643819040467 15214064182836965728560701)
          ·
            refine ⟨5705274068563862148210263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15214064182836965728560701 5705274068563862148210263)
            ·
              refine ⟨8557911102845793222315395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5705274068563862148210263 8557911102845793222315395)
              ·
                refine ⟨12836866654268689833473093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8557911102845793222315395 12836866654268689833473093)
                ·
                  refine ⟨2406912497675379343776205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12836866654268689833473093 2406912497675379343776205)
                  ·
                    refine ⟨902592186628267253916077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2406912497675379343776205 902592186628267253916077)
                    ·
                      refine ⟨338472069985600220218529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 902592186628267253916077 338472069985600220218529)
                      ·
                        rfl

theorem cell23_659172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_659172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659172 prefixEnd_659172 := by exact prefixLift 659172
  have htrace : WordTrace (prefixWord ++ tailWord_659172) baseStart_659172 baseEnd_659172 := by
    simpa [prefixWord, tailWord_659172, baseEnd_659172] using wordTrace_append hprefix tailTrace_659172
  have hstable : (prefixWord ++ tailWord_659172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659172).length < 2 ^ (prefixWord ++ tailWord_659172).sum := by decide
  have hdescent : baseEnd_659172 < baseStart_659172 := by decide
  rcases family_descends (prefixWord ++ tailWord_659172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659190 : List Nat := [5, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2]
def baseStart_659190 : Nat := 118140960795 + 659190 * 2 ^ 59
def prefixEnd_659190 : Nat := 4983230072969 + 3 ^ 40 * 659190 * 2
def baseEnd_659190 : Nat := 338481312637381149793447

theorem tailTrace_659190 : CollatzResearch.WordTrace tailWord_659190 prefixEnd_659190 338481312637381149793447 := by
  unfold tailWord_659190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1502664655117167845881439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16028422987916457022735349 1502664655117167845881439)
  ·
    refine ⟨2253996982675751768822159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1502664655117167845881439 2253996982675751768822159)
    ·
      refine ⟨3380995474013627653233239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2253996982675751768822159 3380995474013627653233239)
      ·
        refine ⟨5071493211020441479849859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3380995474013627653233239 5071493211020441479849859)
        ·
          refine ⟨7607239816530662219774789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5071493211020441479849859 7607239816530662219774789)
          ·
            refine ⟨1426357465599499166207773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7607239816530662219774789 1426357465599499166207773)
            ·
              refine ⟨534884049599812187327915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1426357465599499166207773 534884049599812187327915)
              ·
                refine ⟨802326074399718280991873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 534884049599812187327915 802326074399718280991873)
                ·
                  refine ⟨601744555799788710743905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 802326074399718280991873 601744555799788710743905)
                  ·
                    refine ⟨451308416849841533057929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 601744555799788710743905 451308416849841533057929)
                    ·
                      refine ⟨338481312637381149793447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 451308416849841533057929 338481312637381149793447)
                      ·
                        rfl

theorem cell23_659190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_659190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659190 prefixEnd_659190 := by exact prefixLift 659190
  have htrace : WordTrace (prefixWord ++ tailWord_659190) baseStart_659190 baseEnd_659190 := by
    simpa [prefixWord, tailWord_659190, baseEnd_659190] using wordTrace_append hprefix tailTrace_659190
  have hstable : (prefixWord ++ tailWord_659190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659190).length < 2 ^ (prefixWord ++ tailWord_659190).sum := by decide
  have hdescent : baseEnd_659190 < baseStart_659190 := by decide
  rcases family_descends (prefixWord ++ tailWord_659190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659212 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 1, 3, 4]
def baseStart_659212 : Nat := 118140960795 + 659212 * 2 ^ 59
def prefixEnd_659212 : Nat := 4983230072969 + 3 ^ 40 * 659212 * 2
def baseEnd_659212 : Nat := 338492609211780063718345

theorem tailTrace_659212 : CollatzResearch.WordTrace tailWord_659212 prefixEnd_659212 338492609211780063718345 := by
  unfold tailWord_659212
  simp only [CollatzResearch.WordTrace]
  refine ⟨12021718443897491645701945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16028957925196655527602593 12021718443897491645701945)
  ·
    refine ⟨9016288832923118734276459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12021718443897491645701945 9016288832923118734276459)
    ·
      refine ⟨13524433249384678101414689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9016288832923118734276459 13524433249384678101414689)
      ·
        refine ⟨10143324937038508576061017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13524433249384678101414689 10143324937038508576061017)
        ·
          refine ⟨7607493702778881432045763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10143324937038508576061017 7607493702778881432045763)
          ·
            refine ⟨11411240554168322148068645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7607493702778881432045763 11411240554168322148068645)
            ·
              refine ⟨2139607603906560402762871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11411240554168322148068645 2139607603906560402762871)
              ·
                refine ⟨3209411405859840604144307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2139607603906560402762871 3209411405859840604144307)
                ·
                  refine ⟨4814117108789760906216461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3209411405859840604144307 4814117108789760906216461)
                  ·
                    refine ⟨1805293915796160339831173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4814117108789760906216461 1805293915796160339831173)
                    ·
                      refine ⟨338492609211780063718345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1805293915796160339831173 338492609211780063718345)
                      ·
                        rfl

theorem cell23_659212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_659212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659212 prefixEnd_659212 := by exact prefixLift 659212
  have htrace : WordTrace (prefixWord ++ tailWord_659212) baseStart_659212 baseEnd_659212 := by
    simpa [prefixWord, tailWord_659212, baseEnd_659212] using wordTrace_append hprefix tailTrace_659212
  have hstable : (prefixWord ++ tailWord_659212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659212).length < 2 ^ (prefixWord ++ tailWord_659212).sum := by decide
  have hdescent : baseEnd_659212 < baseStart_659212 := by decide
  rcases family_descends (prefixWord ++ tailWord_659212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659230 : List Nat := [4, 3, 2, 2, 2, 1, 1, 1, 7]
def baseStart_659230 : Nat := 118140960795 + 659230 * 2 ^ 59
def prefixEnd_659230 : Nat := 4983230072969 + 3 ^ 40 * 659230 * 2
def baseEnd_659230 : Nat := 37611316873728999254807

theorem tailTrace_659230 : CollatzResearch.WordTrace tailWord_659230 prefixEnd_659230 37611316873728999254807 := by
  unfold tailWord_659230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3005511675216221545694893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16029395601153181577039429 3005511675216221545694893)
  ·
    refine ⟨1127066878206083079635585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3005511675216221545694893 1127066878206083079635585)
    ·
      refine ⟨845300158654562309726689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1127066878206083079635585 845300158654562309726689)
      ·
        refine ⟨633975118990921732295017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 845300158654562309726689 633975118990921732295017)
        ·
          refine ⟨475481339243191299221263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 633975118990921732295017 475481339243191299221263)
          ·
            refine ⟨713222008864786948831895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475481339243191299221263 713222008864786948831895)
            ·
              refine ⟨1069833013297180423247843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713222008864786948831895 1069833013297180423247843)
              ·
                refine ⟨1604749519945770634871765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069833013297180423247843 1604749519945770634871765)
                ·
                  refine ⟨37611316873728999254807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1604749519945770634871765 37611316873728999254807)
                  ·
                    rfl

theorem cell23_659230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_659230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659230 prefixEnd_659230 := by exact prefixLift 659230
  have htrace : WordTrace (prefixWord ++ tailWord_659230) baseStart_659230 baseEnd_659230 := by
    simpa [prefixWord, tailWord_659230, baseEnd_659230] using wordTrace_append hprefix tailTrace_659230
  have hstable : (prefixWord ++ tailWord_659230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659230).length < 2 ^ (prefixWord ++ tailWord_659230).sum := by decide
  have hdescent : baseEnd_659230 < baseStart_659230 := by decide
  rcases family_descends (prefixWord ++ tailWord_659230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659356 : List Nat := [2, 2, 3, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_659356 : Nat := 118140960795 + 659356 * 2 ^ 59
def prefixEnd_659356 : Nat := 4983230072969 + 3 ^ 40 * 659356 * 2
def baseEnd_659356 : Nat := 338566550426027500317683

theorem tailTrace_659356 : CollatzResearch.WordTrace tailWord_659356 prefixEnd_659356 338566550426027500317683 := by
  unfold tailWord_659356
  simp only [CollatzResearch.WordTrace]
  refine ⟨12024344499636647942322961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16032459332848863923097281 12024344499636647942322961)
  ·
    refine ⟨9018258374727485956742221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12024344499636647942322961 9018258374727485956742221)
    ·
      refine ⟨3381846890522807233778333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9018258374727485956742221 3381846890522807233778333)
      ·
        refine ⟨1268192583946052712666875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3381846890522807233778333 1268192583946052712666875)
        ·
          refine ⟨1902288875919079069000313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1268192583946052712666875 1902288875919079069000313)
          ·
            refine ⟨1426716656939309301750235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1902288875919079069000313 1426716656939309301750235)
            ·
              refine ⟨2140074985408963952625353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1426716656939309301750235 2140074985408963952625353)
              ·
                refine ⟨1605056239056722964469015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2140074985408963952625353 1605056239056722964469015)
                ·
                  refine ⟨2407584358585084446703523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1605056239056722964469015 2407584358585084446703523)
                  ·
                    refine ⟨3611376537877626670055285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2407584358585084446703523 3611376537877626670055285)
                    ·
                      refine ⟨338566550426027500317683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3611376537877626670055285 338566550426027500317683)
                      ·
                        rfl

theorem cell23_659356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_659356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659356 prefixEnd_659356 := by exact prefixLift 659356
  have htrace : WordTrace (prefixWord ++ tailWord_659356) baseStart_659356 baseEnd_659356 := by
    simpa [prefixWord, tailWord_659356, baseEnd_659356] using wordTrace_append hprefix tailTrace_659356
  have hstable : (prefixWord ++ tailWord_659356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659356).length < 2 ^ (prefixWord ++ tailWord_659356).sum := by decide
  have hdescent : baseEnd_659356 < baseStart_659356 := by decide
  rcases family_descends (prefixWord ++ tailWord_659356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659369 : List Nat := [1, 2, 1, 1, 1, 1, 4, 5, 1, 3, 3]
def baseStart_659369 : Nat := 118140960795 + 659369 * 2 ^ 59
def prefixEnd_659369 : Nat := 4983230072969 + 3 ^ 40 * 659369 * 2
def baseEnd_659369 : Nat := 338573225674535949455123

theorem tailTrace_659369 : CollatzResearch.WordTrace tailWord_659369 prefixEnd_659369 338573225674535949455123 := by
  unfold tailWord_659369
  simp only [CollatzResearch.WordTrace]
  refine ⟨24049163148226199104869161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16032775432150799403246107 24049163148226199104869161)
  ·
    refine ⟨18036872361169649328651871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24049163148226199104869161 18036872361169649328651871)
    ·
      refine ⟨27055308541754473992977807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18036872361169649328651871 27055308541754473992977807)
      ·
        refine ⟨40582962812631710989466711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27055308541754473992977807 40582962812631710989466711)
        ·
          refine ⟨60874444218947566484200067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40582962812631710989466711 60874444218947566484200067)
          ·
            refine ⟨91311666328421349726300101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60874444218947566484200067 91311666328421349726300101)
            ·
              refine ⟨17120937436579003073681269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91311666328421349726300101 17120937436579003073681269)
              ·
                refine ⟨1605087884679281538157619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17120937436579003073681269 1605087884679281538157619)
                ·
                  refine ⟨2407631827018922307236429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1605087884679281538157619 2407631827018922307236429)
                  ·
                    refine ⟨902861935132095865213661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2407631827018922307236429 902861935132095865213661)
                    ·
                      refine ⟨338573225674535949455123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 902861935132095865213661 338573225674535949455123)
                      ·
                        rfl

theorem cell23_659369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 1, 3, 3].length) (baseStart_659369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659369 prefixEnd_659369 := by exact prefixLift 659369
  have htrace : WordTrace (prefixWord ++ tailWord_659369) baseStart_659369 baseEnd_659369 := by
    simpa [prefixWord, tailWord_659369, baseEnd_659369] using wordTrace_append hprefix tailTrace_659369
  have hstable : (prefixWord ++ tailWord_659369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659369).length < 2 ^ (prefixWord ++ tailWord_659369).sum := by decide
  have hdescent : baseEnd_659369 < baseStart_659369 := by decide
  rcases family_descends (prefixWord ++ tailWord_659369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659414 : List Nat := [5, 2, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_659414 : Nat := 118140960795 + 659414 * 2 ^ 59
def prefixEnd_659414 : Nat := 4983230072969 + 3 ^ 40 * 659414 * 2
def baseEnd_659414 : Nat := 112865444101329424464139

theorem tailTrace_659414 : CollatzResearch.WordTrace tailWord_659414 prefixEnd_659414 112865444101329424464139 := by
  unfold tailWord_659414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1503175277066448236891081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16033869622042114526838197 1503175277066448236891081)
  ·
    refine ⟨1127381457799836177668311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1503175277066448236891081 1127381457799836177668311)
    ·
      refine ⟨1691072186699754266502467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1127381457799836177668311 1691072186699754266502467)
      ·
        refine ⟨2536608280049631399753701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1691072186699754266502467 2536608280049631399753701)
        ·
          refine ⟨475614052509305887453819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2536608280049631399753701 475614052509305887453819)
          ·
            refine ⟨713421078763958831180729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475614052509305887453819 713421078763958831180729)
            ·
              refine ⟨535065809072969123385547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 713421078763958831180729 535065809072969123385547)
              ·
                refine ⟨802598713609453685078321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535065809072969123385547 802598713609453685078321)
                ·
                  refine ⟨601949035207090263808741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 802598713609453685078321 601949035207090263808741)
                  ·
                    refine ⟨112865444101329424464139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 601949035207090263808741 112865444101329424464139)
                    ·
                      rfl

theorem cell23_659414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_659414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659414 prefixEnd_659414 := by exact prefixLift 659414
  have htrace : WordTrace (prefixWord ++ tailWord_659414) baseStart_659414 baseEnd_659414 := by
    simpa [prefixWord, tailWord_659414, baseEnd_659414] using wordTrace_append hprefix tailTrace_659414
  have hstable : (prefixWord ++ tailWord_659414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659414).length < 2 ^ (prefixWord ++ tailWord_659414).sum := by decide
  have hdescent : baseEnd_659414 < baseStart_659414 := by decide
  rcases family_descends (prefixWord ++ tailWord_659414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659459 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 3]
def baseStart_659459 : Nat := 118140960795 + 659459 * 2 ^ 59
def prefixEnd_659459 : Nat := 4983230072969 + 3 ^ 40 * 659459 * 2
def baseEnd_659459 : Nat := 338619438933440597329709

theorem tailTrace_659459 : CollatzResearch.WordTrace tailWord_659459 prefixEnd_659459 338619438933440597329709 := by
  unfold tailWord_659459
  simp only [CollatzResearch.WordTrace]
  refine ⟨24052445717900144475645431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16034963811933429650430287 24052445717900144475645431)
  ·
    refine ⟨36078668576850216713468147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24052445717900144475645431 36078668576850216713468147)
    ·
      refine ⟨54118002865275325070202221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36078668576850216713468147 54118002865275325070202221)
      ·
        refine ⟨20294251074478246901325833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54118002865275325070202221 20294251074478246901325833)
        ·
          refine ⟨15220688305858685175994375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20294251074478246901325833 15220688305858685175994375)
          ·
            refine ⟨22831032458788027763991563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15220688305858685175994375 22831032458788027763991563)
            ·
              refine ⟨34246548688182041645987345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22831032458788027763991563 34246548688182041645987345)
              ·
                refine ⟨25684911516136531234490509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34246548688182041645987345 25684911516136531234490509)
                ·
                  refine ⟨9631841818551199212933941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25684911516136531234490509 9631841818551199212933941)
                  ·
                    refine ⟨902985170489174926212557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9631841818551199212933941 902985170489174926212557)
                    ·
                      refine ⟨338619438933440597329709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 902985170489174926212557 338619438933440597329709)
                      ·
                        rfl

theorem cell23_659459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_659459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659459 prefixEnd_659459 := by exact prefixLift 659459
  have htrace : WordTrace (prefixWord ++ tailWord_659459) baseStart_659459 baseEnd_659459 := by
    simpa [prefixWord, tailWord_659459, baseEnd_659459] using wordTrace_append hprefix tailTrace_659459
  have hstable : (prefixWord ++ tailWord_659459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659459).length < 2 ^ (prefixWord ++ tailWord_659459).sum := by decide
  have hdescent : baseEnd_659459 < baseStart_659459 := by decide
  rcases family_descends (prefixWord ++ tailWord_659459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659516 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 4, 1, 4]
def baseStart_659516 : Nat := 118140960795 + 659516 * 2 ^ 59
def prefixEnd_659516 : Nat := 4983230072969 + 3 ^ 40 * 659516 * 2
def baseEnd_659516 : Nat := 338648707330746874316947

theorem tailTrace_659516 : CollatzResearch.WordTrace tailWord_659516 prefixEnd_659516 338648707330746874316947 := by
  unfold tailWord_659516
  simp only [CollatzResearch.WordTrace]
  refine ⟨12027262339346821605235201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16036349785795762140313601 12027262339346821605235201)
  ·
    refine ⟨9020446754510116203926401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12027262339346821605235201 9020446754510116203926401)
    ·
      refine ⟨6765335065882587152944801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9020446754510116203926401 6765335065882587152944801)
      ·
        refine ⟨5074001299411940364708601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6765335065882587152944801 5074001299411940364708601)
        ·
          refine ⟨3805500974558955273531451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5074001299411940364708601 3805500974558955273531451)
          ·
            refine ⟨5708251461838432910297177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3805500974558955273531451 5708251461838432910297177)
            ·
              refine ⟨4281188596378824682722883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5708251461838432910297177 4281188596378824682722883)
              ·
                refine ⟨6421782894568237024084325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4281188596378824682722883 6421782894568237024084325)
                ·
                  refine ⟨1204084292731544442015811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6421782894568237024084325 1204084292731544442015811)
                  ·
                    refine ⟨1806126439097316663023717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1204084292731544442015811 1806126439097316663023717)
                    ·
                      refine ⟨338648707330746874316947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1806126439097316663023717 338648707330746874316947)
                      ·
                        rfl

theorem cell23_659516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_659516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659516 prefixEnd_659516 := by exact prefixLift 659516
  have htrace : WordTrace (prefixWord ++ tailWord_659516) baseStart_659516 baseEnd_659516 := by
    simpa [prefixWord, tailWord_659516, baseEnd_659516] using wordTrace_append hprefix tailTrace_659516
  have hstable : (prefixWord ++ tailWord_659516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659516).length < 2 ^ (prefixWord ++ tailWord_659516).sum := by decide
  have hdescent : baseEnd_659516 < baseStart_659516 := by decide
  rcases family_descends (prefixWord ++ tailWord_659516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659519 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 5]
def baseStart_659519 : Nat := 118140960795 + 659519 * 2 ^ 59
def prefixEnd_659519 : Nat := 4983230072969 + 3 ^ 40 * 659519 * 2
def baseEnd_659519 : Nat := 338650247772710362579433

theorem tailTrace_659519 : CollatzResearch.WordTrace tailWord_659519 prefixEnd_659519 338650247772710362579433 := by
  unfold tailWord_659519
  simp only [CollatzResearch.WordTrace]
  refine ⟨24054634097682774722829611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16036422731788516481886407 24054634097682774722829611)
  ·
    refine ⟨36081951146524162084244417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24054634097682774722829611 36081951146524162084244417)
    ·
      refine ⟨27061463359893121563183313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36081951146524162084244417 27061463359893121563183313)
      ·
        refine ⟨20296097519919841172387485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27061463359893121563183313 20296097519919841172387485)
        ·
          refine ⟨7611036569969940439645307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20296097519919841172387485 7611036569969940439645307)
          ·
            refine ⟨11416554854954910659467961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7611036569969940439645307 11416554854954910659467961)
            ·
              refine ⟨8562416141216182994600971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11416554854954910659467961 8562416141216182994600971)
              ·
                refine ⟨12843624211824274491901457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8562416141216182994600971 12843624211824274491901457)
                ·
                  refine ⟨9632718158868205868926093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12843624211824274491901457 9632718158868205868926093)
                  ·
                    refine ⟨3612269309575577200847285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9632718158868205868926093 3612269309575577200847285)
                    ·
                      refine ⟨338650247772710362579433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3612269309575577200847285 338650247772710362579433)
                      ·
                        rfl

theorem cell23_659519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_659519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659519 prefixEnd_659519 := by exact prefixLift 659519
  have htrace : WordTrace (prefixWord ++ tailWord_659519) baseStart_659519 baseEnd_659519 := by
    simpa [prefixWord, tailWord_659519, baseEnd_659519] using wordTrace_append hprefix tailTrace_659519
  have hstable : (prefixWord ++ tailWord_659519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659519).length < 2 ^ (prefixWord ++ tailWord_659519).sum := by decide
  have hdescent : baseEnd_659519 < baseStart_659519 := by decide
  rcases family_descends (prefixWord ++ tailWord_659519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659529 : List Nat := [1, 2, 1, 1, 2, 2, 3, 2, 2, 1, 6]
def baseStart_659529 : Nat := 118140960795 + 659529 * 2 ^ 59
def prefixEnd_659529 : Nat := 4983230072969 + 3 ^ 40 * 659529 * 2
def baseEnd_659529 : Nat := 338655382579255323454387

theorem tailTrace_659529 : CollatzResearch.WordTrace tailWord_659529 prefixEnd_659529 338655382579255323454387 := by
  unfold tailWord_659529
  simp only [CollatzResearch.WordTrace]
  refine ⟨24054998827646546430693641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16036665885097697620462427 24054998827646546430693641)
  ·
    refine ⟨18041249120734909823020231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24054998827646546430693641 18041249120734909823020231)
    ·
      refine ⟨27061873681102364734530347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18041249120734909823020231 27061873681102364734530347)
      ·
        refine ⟨40592810521653547101795521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27061873681102364734530347 40592810521653547101795521)
        ·
          refine ⟨30444607891240160326346641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40592810521653547101795521 30444607891240160326346641)
          ·
            refine ⟨22833455918430120244759981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30444607891240160326346641 22833455918430120244759981)
            ·
              refine ⟨8562545969411295091784993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22833455918430120244759981 8562545969411295091784993)
              ·
                refine ⟨6421909477058471318838745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8562545969411295091784993 6421909477058471318838745)
                ·
                  refine ⟨4816432107793853489129059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6421909477058471318838745 4816432107793853489129059)
                  ·
                    refine ⟨7224648161690780233693589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4816432107793853489129059 7224648161690780233693589)
                    ·
                      refine ⟨338655382579255323454387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7224648161690780233693589 338655382579255323454387)
                      ·
                        rfl

theorem cell23_659529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_659529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659529 prefixEnd_659529 := by exact prefixLift 659529
  have htrace : WordTrace (prefixWord ++ tailWord_659529) baseStart_659529 baseEnd_659529 := by
    simpa [prefixWord, tailWord_659529, baseEnd_659529] using wordTrace_append hprefix tailTrace_659529
  have hstable : (prefixWord ++ tailWord_659529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659529).length < 2 ^ (prefixWord ++ tailWord_659529).sum := by decide
  have hdescent : baseEnd_659529 < baseStart_659529 := by decide
  rcases family_descends (prefixWord ++ tailWord_659529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659577 : List Nat := [1, 2, 1, 3, 4, 2, 3, 2, 1, 4]
def baseStart_659577 : Nat := 118140960795 + 659577 * 2 ^ 59
def prefixEnd_659577 : Nat := 4983230072969 + 3 ^ 40 * 659577 * 2
def baseEnd_659577 : Nat := 112893343216890378551389

theorem tailTrace_659577 : CollatzResearch.WordTrace tailWord_659577 prefixEnd_659577 112893343216890378551389 := by
  unfold tailWord_659577
  simp only [CollatzResearch.WordTrace]
  refine ⟨24056749531472650628440985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16037833020981767085627323 24056749531472650628440985)
  ·
    refine ⟨18042562148604487971330739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24056749531472650628440985 18042562148604487971330739)
    ·
      refine ⟨27063843222906731956996109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18042562148604487971330739 27063843222906731956996109)
      ·
        refine ⟨10148941208590024483873541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27063843222906731956996109 10148941208590024483873541)
        ·
          refine ⟨1902926476610629590726289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10148941208590024483873541 1902926476610629590726289)
          ·
            refine ⟨1427194857457972193044717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1902926476610629590726289 1427194857457972193044717)
            ·
              refine ⟨535198071546739572391769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1427194857457972193044717 535198071546739572391769)
              ·
                refine ⟨401398553660054679293827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 535198071546739572391769 401398553660054679293827)
                ·
                  refine ⟨602097830490082018940741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 401398553660054679293827 602097830490082018940741)
                  ·
                    refine ⟨112893343216890378551389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 602097830490082018940741 112893343216890378551389)
                    ·
                      rfl

theorem cell23_659577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 1, 4].length) (baseStart_659577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659577 prefixEnd_659577 := by exact prefixLift 659577
  have htrace : WordTrace (prefixWord ++ tailWord_659577) baseStart_659577 baseEnd_659577 := by
    simpa [prefixWord, tailWord_659577, baseEnd_659577] using wordTrace_append hprefix tailTrace_659577
  have hstable : (prefixWord ++ tailWord_659577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659577).length < 2 ^ (prefixWord ++ tailWord_659577).sum := by decide
  have hdescent : baseEnd_659577 < baseStart_659577 := by decide
  rcases family_descends (prefixWord ++ tailWord_659577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659579 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 7]
def baseStart_659579 : Nat := 118140960795 + 659579 * 2 ^ 59
def prefixEnd_659579 : Nat := 4983230072969 + 3 ^ 40 * 659579 * 2
def baseEnd_659579 : Nat := 338681056611980127829157

theorem tailTrace_659579 : CollatzResearch.WordTrace tailWord_659579 prefixEnd_659579 338681056611980127829157 := by
  unfold tailWord_659579
  simp only [CollatzResearch.WordTrace]
  refine ⟨24056822477465404970013791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16037881651643603313342527 24056822477465404970013791)
  ·
    refine ⟨36085233716198107455020687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24056822477465404970013791 36085233716198107455020687)
    ·
      refine ⟨54127850574297161182531031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36085233716198107455020687 54127850574297161182531031)
      ·
        refine ⟨81191775861445741773796547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54127850574297161182531031 81191775861445741773796547)
        ·
          refine ⟨121787663792168612660694821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81191775861445741773796547 121787663792168612660694821)
          ·
            refine ⟨22835186961031614873880279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121787663792168612660694821 22835186961031614873880279)
            ·
              refine ⟨34252780441547422310820419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22835186961031614873880279 34252780441547422310820419)
              ·
                refine ⟨51379170662321133466230629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34252780441547422310820419 51379170662321133466230629)
                ·
                  refine ⟨9633594499185212524918243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51379170662321133466230629 9633594499185212524918243)
                  ·
                    refine ⟨14450391748777818787377365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9633594499185212524918243 14450391748777818787377365)
                    ·
                      refine ⟨338681056611980127829157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14450391748777818787377365 338681056611980127829157)
                      ·
                        rfl

theorem cell23_659579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 7].length) (baseStart_659579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659579 prefixEnd_659579 := by exact prefixLift 659579
  have htrace : WordTrace (prefixWord ++ tailWord_659579) baseStart_659579 baseEnd_659579 := by
    simpa [prefixWord, tailWord_659579, baseEnd_659579] using wordTrace_append hprefix tailTrace_659579
  have hstable : (prefixWord ++ tailWord_659579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659579).length < 2 ^ (prefixWord ++ tailWord_659579).sum := by decide
  have hdescent : baseEnd_659579 < baseStart_659579 := by decide
  rcases family_descends (prefixWord ++ tailWord_659579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659593 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 4, 3, 2]
def baseStart_659593 : Nat := 118140960795 + 659593 * 2 ^ 59
def prefixEnd_659593 : Nat := 4983230072969 + 3 ^ 40 * 659593 * 2
def baseEnd_659593 : Nat := 338688245341143073054093

theorem tailTrace_659593 : CollatzResearch.WordTrace tailWord_659593 prefixEnd_659593 338688245341143073054093 := by
  unfold tailWord_659593
  simp only [CollatzResearch.WordTrace]
  refine ⟨24057333099414685361023433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16038222066276456907348955 24057333099414685361023433)
  ·
    refine ⟨18042999824561014020767575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24057333099414685361023433 18042999824561014020767575)
    ·
      refine ⟨27064499736841521031151363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18042999824561014020767575 27064499736841521031151363)
      ·
        refine ⟨40596749605262281546727045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27064499736841521031151363 40596749605262281546727045)
        ·
          refine ⟨7611890550986677790011321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40596749605262281546727045 7611890550986677790011321)
          ·
            refine ⟨5708917913240008342508491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7611890550986677790011321 5708917913240008342508491)
            ·
              refine ⟨8563376869860012513762737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5708917913240008342508491 8563376869860012513762737)
              ·
                refine ⟨6422532652395009385322053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8563376869860012513762737 6422532652395009385322053)
                ·
                  refine ⟨1204224872324064259747885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6422532652395009385322053 1204224872324064259747885)
                  ·
                    refine ⟨451584327121524097405457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1204224872324064259747885 451584327121524097405457)
                    ·
                      refine ⟨338688245341143073054093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 451584327121524097405457 338688245341143073054093)
                      ·
                        rfl

theorem cell23_659593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 4, 3, 2].length) (baseStart_659593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659593 prefixEnd_659593 := by exact prefixLift 659593
  have htrace : WordTrace (prefixWord ++ tailWord_659593) baseStart_659593 baseEnd_659593 := by
    simpa [prefixWord, tailWord_659593, baseEnd_659593] using wordTrace_append hprefix tailTrace_659593
  have hstable : (prefixWord ++ tailWord_659593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659593).length < 2 ^ (prefixWord ++ tailWord_659593).sum := by decide
  have hdescent : baseEnd_659593 < baseStart_659593 := by decide
  rcases family_descends (prefixWord ++ tailWord_659593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659599 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 1, 12]
def baseStart_659599 : Nat := 118140960795 + 659599 * 2 ^ 59
def prefixEnd_659599 : Nat := 4983230072969 + 3 ^ 40 * 659599 * 2
def baseEnd_659599 : Nat := 112897108741690016526355

theorem tailTrace_659599 : CollatzResearch.WordTrace tailWord_659599 prefixEnd_659599 112897108741690016526355 := by
  unfold tailWord_659599
  simp only [CollatzResearch.WordTrace]
  refine ⟨24057551937392948385741851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16038367958261965590494567 24057551937392948385741851)
  ·
    refine ⟨36086327906089422578612777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24057551937392948385741851 36086327906089422578612777)
    ·
      refine ⟨27064745929567066933959583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36086327906089422578612777 27064745929567066933959583)
      ·
        refine ⟨40597118894350600400939375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27064745929567066933959583 40597118894350600400939375)
        ·
          refine ⟨60895678341525900601409063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40597118894350600400939375 60895678341525900601409063)
          ·
            refine ⟨91343517512288850902113595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60895678341525900601409063 91343517512288850902113595)
            ·
              refine ⟨137015276268433276353170393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91343517512288850902113595 137015276268433276353170393)
              ·
                refine ⟨102761457201324957264877795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137015276268433276353170393 102761457201324957264877795)
                ·
                  refine ⟨154142185801987435897316693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 102761457201324957264877795 154142185801987435897316693)
                  ·
                    refine ⟨112897108741690016526355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 154142185801987435897316693 112897108741690016526355)
                    ·
                      rfl

theorem cell23_659599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 12].length) (baseStart_659599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659599 prefixEnd_659599 := by exact prefixLift 659599
  have htrace : WordTrace (prefixWord ++ tailWord_659599) baseStart_659599 baseEnd_659599 := by
    simpa [prefixWord, tailWord_659599, baseEnd_659599] using wordTrace_append hprefix tailTrace_659599
  have hstable : (prefixWord ++ tailWord_659599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659599).length < 2 ^ (prefixWord ++ tailWord_659599).sum := by decide
  have hdescent : baseEnd_659599 < baseStart_659599 := by decide
  rcases family_descends (prefixWord ++ tailWord_659599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659616 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 3, 6]
def baseStart_659616 : Nat := 118140960795 + 659616 * 2 ^ 59
def prefixEnd_659616 : Nat := 4983230072969 + 3 ^ 40 * 659616 * 2
def baseEnd_659616 : Nat := 112900018465398827688829

theorem tailTrace_659616 : CollatzResearch.WordTrace tailWord_659616 prefixEnd_659616 112900018465398827688829 := by
  unfold tailWord_659616
  simp only [CollatzResearch.WordTrace]
  refine ⟨12029085989165680144555351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16038781318887573526073801 12029085989165680144555351)
  ·
    refine ⟨18043628983748520216833027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12029085989165680144555351 18043628983748520216833027)
    ·
      refine ⟨27065443475622780325249541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18043628983748520216833027 27065443475622780325249541)
      ·
        refine ⟨5074770651679271310984289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27065443475622780325249541 5074770651679271310984289)
        ·
          refine ⟨3806077988759453483238217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5074770651679271310984289 3806077988759453483238217)
          ·
            refine ⟨2854558491569590112428663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3806077988759453483238217 2854558491569590112428663)
            ·
              refine ⟨4281837737354385168642995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2854558491569590112428663 4281837737354385168642995)
              ·
                refine ⟨6422756606031577752964493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4281837737354385168642995 6422756606031577752964493)
                ·
                  refine ⟨2408533727261841657361685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6422756606031577752964493 2408533727261841657361685)
                  ·
                    refine ⟨112900018465398827688829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2408533727261841657361685 112900018465398827688829)
                    ·
                      rfl

theorem cell23_659616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 3, 6].length) (baseStart_659616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659616 prefixEnd_659616 := by exact prefixLift 659616
  have htrace : WordTrace (prefixWord ++ tailWord_659616) baseStart_659616 baseEnd_659616 := by
    simpa [prefixWord, tailWord_659616, baseEnd_659616] using wordTrace_append hprefix tailTrace_659616
  have hstable : (prefixWord ++ tailWord_659616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659616).length < 2 ^ (prefixWord ++ tailWord_659616).sum := by decide
  have hdescent : baseEnd_659616 < baseStart_659616 := by decide
  rcases family_descends (prefixWord ++ tailWord_659616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659640 : List Nat := [2, 1, 2, 1, 2, 1, 4, 3, 3, 2, 2]
def baseStart_659640 : Nat := 118140960795 + 659640 * 2 ^ 59
def prefixEnd_659640 : Nat := 4983230072969 + 3 ^ 40 * 659640 * 2
def baseEnd_659640 : Nat := 338712378931904389166377

theorem tailTrace_659640 : CollatzResearch.WordTrace tailWord_659640 prefixEnd_659640 338712378931904389166377 := by
  unfold tailWord_659640
  simp only [CollatzResearch.WordTrace]
  refine ⟨12029523665122206193992187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16039364886829608258656249 12029523665122206193992187)
  ·
    refine ⟨18044285497683309290988281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12029523665122206193992187 18044285497683309290988281)
    ·
      refine ⟨13533214123262481968241211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18044285497683309290988281 13533214123262481968241211)
      ·
        refine ⟨20299821184893722952361817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13533214123262481968241211 20299821184893722952361817)
        ·
          refine ⟨15224865888670292214271363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20299821184893722952361817 15224865888670292214271363)
          ·
            refine ⟨22837298833005438321407045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15224865888670292214271363 22837298833005438321407045)
            ·
              refine ⟨4281993531188519685263821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22837298833005438321407045 4281993531188519685263821)
              ·
                refine ⟨1605747574195694881973933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4281993531188519685263821 1605747574195694881973933)
                ·
                  refine ⟨602155340323385580740225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1605747574195694881973933 602155340323385580740225)
                  ·
                    refine ⟨451616505242539185555169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 602155340323385580740225 451616505242539185555169)
                    ·
                      refine ⟨338712378931904389166377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 451616505242539185555169 338712378931904389166377)
                      ·
                        rfl

theorem cell23_659640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 3, 2, 2].length) (baseStart_659640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659640 prefixEnd_659640 := by exact prefixLift 659640
  have htrace : WordTrace (prefixWord ++ tailWord_659640) baseStart_659640 baseEnd_659640 := by
    simpa [prefixWord, tailWord_659640, baseEnd_659640] using wordTrace_append hprefix tailTrace_659640
  have hstable : (prefixWord ++ tailWord_659640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659640).length < 2 ^ (prefixWord ++ tailWord_659640).sum := by decide
  have hdescent : baseEnd_659640 < baseStart_659640 := by decide
  rcases family_descends (prefixWord ++ tailWord_659640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659673 : List Nat := [1, 2, 1, 2, 3, 1, 4, 2, 1, 3, 3]
def baseStart_659673 : Nat := 118140960795 + 659673 * 2 ^ 59
def prefixEnd_659673 : Nat := 4983230072969 + 3 ^ 40 * 659673 * 2
def baseEnd_659673 : Nat := 338729323793502760053725

theorem tailTrace_659673 : CollatzResearch.WordTrace tailWord_659673 prefixEnd_659673 338729323793502760053725 := by
  unfold tailWord_659673
  simp only [CollatzResearch.WordTrace]
  refine ⟨24060250939124859023935673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16040167292749906015957115 24060250939124859023935673)
  ·
    refine ⟨18045188204343644267951755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24060250939124859023935673 18045188204343644267951755)
    ·
      refine ⟨27067782306515466401927633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18045188204343644267951755 27067782306515466401927633)
      ·
        refine ⟨20300836729886599801445725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27067782306515466401927633 20300836729886599801445725)
        ·
          refine ⟨7612813773707474925542147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20300836729886599801445725 7612813773707474925542147)
          ·
            refine ⟨11419220660561212388313221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7612813773707474925542147 11419220660561212388313221)
            ·
              refine ⟨2141103873855227322808729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11419220660561212388313221 2141103873855227322808729)
              ·
                refine ⟨1605827905391420492106547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2141103873855227322808729 1605827905391420492106547)
                ·
                  refine ⟨2408741858087130738159821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1605827905391420492106547 2408741858087130738159821)
                  ·
                    refine ⟨903278196782674026809933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2408741858087130738159821 903278196782674026809933)
                    ·
                      refine ⟨338729323793502760053725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 903278196782674026809933 338729323793502760053725)
                      ·
                        rfl

theorem cell23_659673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_659673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659673 prefixEnd_659673 := by exact prefixLift 659673
  have htrace : WordTrace (prefixWord ++ tailWord_659673) baseStart_659673 baseEnd_659673 := by
    simpa [prefixWord, tailWord_659673, baseEnd_659673] using wordTrace_append hprefix tailTrace_659673
  have hstable : (prefixWord ++ tailWord_659673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659673).length < 2 ^ (prefixWord ++ tailWord_659673).sum := by decide
  have hdescent : baseEnd_659673 < baseStart_659673 := by decide
  rcases family_descends (prefixWord ++ tailWord_659673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659677 : List Nat := [1, 4, 3, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_659677 : Nat := 118140960795 + 659677 * 2 ^ 59
def prefixEnd_659677 : Nat := 4983230072969 + 3 ^ 40 * 659677 * 2
def baseEnd_659677 : Nat := 338731377716120744403707

theorem tailTrace_659677 : CollatzResearch.WordTrace tailWord_659677 prefixEnd_659677 338731377716120744403707 := by
  unfold tailWord_659677
  simp only [CollatzResearch.WordTrace]
  refine ⟨24060396831110367707081285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16040264554073578471387523 24060396831110367707081285)
  ·
    refine ⟨4511324405833193945077741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24060396831110367707081285 4511324405833193945077741)
    ·
      refine ⟨1691746652187447729404153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4511324405833193945077741 1691746652187447729404153)
      ·
        refine ⟨1268809989140585797053115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1691746652187447729404153 1268809989140585797053115)
        ·
          refine ⟨1903214983710878695579673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1268809989140585797053115 1903214983710878695579673)
          ·
            refine ⟨1427411237783159021684755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1903214983710878695579673 1427411237783159021684755)
            ·
              refine ⟨2141116856674738532527133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1427411237783159021684755 2141116856674738532527133)
              ·
                refine ⟨802918821253026949697675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2141116856674738532527133 802918821253026949697675)
                ·
                  refine ⟨1204378231879540424546513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 802918821253026949697675 1204378231879540424546513)
                  ·
                    refine ⟨903283673909655318409885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1204378231879540424546513 903283673909655318409885)
                    ·
                      refine ⟨338731377716120744403707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 903283673909655318409885 338731377716120744403707)
                      ·
                        rfl

theorem cell23_659677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_659677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659677 prefixEnd_659677 := by exact prefixLift 659677
  have htrace : WordTrace (prefixWord ++ tailWord_659677) baseStart_659677 baseEnd_659677 := by
    simpa [prefixWord, tailWord_659677, baseEnd_659677] using wordTrace_append hprefix tailTrace_659677
  have hstable : (prefixWord ++ tailWord_659677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659677).length < 2 ^ (prefixWord ++ tailWord_659677).sum := by decide
  have hdescent : baseEnd_659677 < baseStart_659677 := by decide
  rcases family_descends (prefixWord ++ tailWord_659677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659690 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 4, 1, 3]
def baseStart_659690 : Nat := 118140960795 + 659690 * 2 ^ 59
def prefixEnd_659690 : Nat := 4983230072969 + 3 ^ 40 * 659690 * 2
def baseEnd_659690 : Nat := 338738052964629193541147

theorem tailTrace_659690 : CollatzResearch.WordTrace tailWord_659690 prefixEnd_659690 338738052964629193541147 := by
  unfold tailWord_659690
  simp only [CollatzResearch.WordTrace]
  refine ⟨6015217745015817731826131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16040580653375513951536349 6015217745015817731826131)
  ·
    refine ⟨9022826617523726597739197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6015217745015817731826131 9022826617523726597739197)
    ·
      refine ⟨3383559981571397474152199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9022826617523726597739197 3383559981571397474152199)
      ·
        refine ⟨5075339972357096211228299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3383559981571397474152199 5075339972357096211228299)
        ·
          refine ⟨7613009958535644316842449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5075339972357096211228299 7613009958535644316842449)
          ·
            refine ⟨5709757468901733237631837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7613009958535644316842449 5709757468901733237631837)
            ·
              refine ⟨2141159050838149964111939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5709757468901733237631837 2141159050838149964111939)
              ·
                refine ⟨3211738576257224946167909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2141159050838149964111939 3211738576257224946167909)
                ·
                  refine ⟨602200983048229677406483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3211738576257224946167909 602200983048229677406483)
                  ·
                    refine ⟨903301474572344516109725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 602200983048229677406483 903301474572344516109725)
                    ·
                      refine ⟨338738052964629193541147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 903301474572344516109725 338738052964629193541147)
                      ·
                        rfl

theorem cell23_659690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_659690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659690 prefixEnd_659690 := by exact prefixLift 659690
  have htrace : WordTrace (prefixWord ++ tailWord_659690) baseStart_659690 baseEnd_659690 := by
    simpa [prefixWord, tailWord_659690, baseEnd_659690] using wordTrace_append hprefix tailTrace_659690
  have hstable : (prefixWord ++ tailWord_659690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659690).length < 2 ^ (prefixWord ++ tailWord_659690).sum := by decide
  have hdescent : baseEnd_659690 < baseStart_659690 := by decide
  rcases family_descends (prefixWord ++ tailWord_659690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659696 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 4]
def baseStart_659696 : Nat := 118140960795 + 659696 * 2 ^ 59
def prefixEnd_659696 : Nat := 4983230072969 + 3 ^ 40 * 659696 * 2
def baseEnd_659696 : Nat := 338741133848556170066119

theorem tailTrace_659696 : CollatzResearch.WordTrace tailWord_659696 prefixEnd_659696 338741133848556170066119 := by
  unfold tailWord_659696
  simp only [CollatzResearch.WordTrace]
  refine ⟨12030544909020766976011471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16040726545361022634681961 12030544909020766976011471)
  ·
    refine ⟨18045817363531150464017207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12030544909020766976011471 18045817363531150464017207)
    ·
      refine ⟨27068726045296725696025811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18045817363531150464017207 27068726045296725696025811)
      ·
        refine ⟨40603089067945088544038717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27068726045296725696025811 40603089067945088544038717)
        ·
          refine ⟨15226158400479408204014519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40603089067945088544038717 15226158400479408204014519)
          ·
            refine ⟨22839237600719112306021779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15226158400479408204014519 22839237600719112306021779)
            ·
              refine ⟨34258856401078668459032669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22839237600719112306021779 34258856401078668459032669)
              ·
                refine ⟨12847071150404500672137251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34258856401078668459032669 12847071150404500672137251)
                ·
                  refine ⟨19270606725606751008205877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12847071150404500672137251 19270606725606751008205877)
                  ·
                    refine ⟨1806619380525632907019301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19270606725606751008205877 1806619380525632907019301)
                    ·
                      refine ⟨338741133848556170066119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1806619380525632907019301 338741133848556170066119)
                      ·
                        rfl

theorem cell23_659696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 4].length) (baseStart_659696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659696 prefixEnd_659696 := by exact prefixLift 659696
  have htrace : WordTrace (prefixWord ++ tailWord_659696) baseStart_659696 baseEnd_659696 := by
    simpa [prefixWord, tailWord_659696, baseEnd_659696] using wordTrace_append hprefix tailTrace_659696
  have hstable : (prefixWord ++ tailWord_659696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659696).length < 2 ^ (prefixWord ++ tailWord_659696).sum := by decide
  have hdescent : baseEnd_659696 < baseStart_659696 := by decide
  rcases family_descends (prefixWord ++ tailWord_659696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659747 : List Nat := [1, 1, 1, 4, 2, 2, 2, 4, 2, 2, 2]
def baseStart_659747 : Nat := 118140960795 + 659747 * 2 ^ 59
def prefixEnd_659747 : Nat := 4983230072969 + 3 ^ 40 * 659747 * 2
def baseEnd_659747 : Nat := 338767321361935470528385

theorem tailTrace_659747 : CollatzResearch.WordTrace tailWord_659747 prefixEnd_659747 338767321361935470528385 := by
  unfold tailWord_659747
  simp only [CollatzResearch.WordTrace]
  refine ⟨24062949940856769662129495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16041966627237846441419663 24062949940856769662129495)
  ·
    refine ⟨36094424911285154493194243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24062949940856769662129495 36094424911285154493194243)
    ·
      refine ⟨54141637366927731739791365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36094424911285154493194243 54141637366927731739791365)
      ·
        refine ⟨10151557006298949701210881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54141637366927731739791365 10151557006298949701210881)
        ·
          refine ⟨7613667754724212275908161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10151557006298949701210881 7613667754724212275908161)
          ·
            refine ⟨5710250816043159206931121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7613667754724212275908161 5710250816043159206931121)
            ·
              refine ⟨4282688112032369405198341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5710250816043159206931121 4282688112032369405198341)
              ·
                refine ⟨803004021006069263474689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4282688112032369405198341 803004021006069263474689)
                ·
                  refine ⟨602253015754551947606017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 803004021006069263474689 602253015754551947606017)
                  ·
                    refine ⟨451689761815913960704513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 602253015754551947606017 451689761815913960704513)
                    ·
                      refine ⟨338767321361935470528385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 451689761815913960704513 338767321361935470528385)
                      ·
                        rfl

theorem cell23_659747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 2, 2, 2].length) (baseStart_659747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659747 prefixEnd_659747 := by exact prefixLift 659747
  have htrace : WordTrace (prefixWord ++ tailWord_659747) baseStart_659747 baseEnd_659747 := by
    simpa [prefixWord, tailWord_659747, baseEnd_659747] using wordTrace_append hprefix tailTrace_659747
  have hstable : (prefixWord ++ tailWord_659747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659747).length < 2 ^ (prefixWord ++ tailWord_659747).sum := by decide
  have hdescent : baseEnd_659747 < baseStart_659747 := by decide
  rcases family_descends (prefixWord ++ tailWord_659747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659758 : List Nat := [4, 1, 3, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_659758 : Nat := 118140960795 + 659758 * 2 ^ 59
def prefixEnd_659758 : Nat := 4983230072969 + 3 ^ 40 * 659758 * 2
def baseEnd_659758 : Nat := 338772969649134927490835

theorem tailTrace_659758 : CollatzResearch.WordTrace tailWord_659758 prefixEnd_659758 338772969649134927490835 := by
  unfold tailWord_659758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3007918892977114817597491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16042234095877945693853285 3007918892977114817597491)
  ·
    refine ⟨4511878339465672226396237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3007918892977114817597491 4511878339465672226396237)
    ·
      refine ⟨1691954377299627084898589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4511878339465672226396237 1691954377299627084898589)
      ·
        refine ⟨634482891487360156836971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1691954377299627084898589 634482891487360156836971)
        ·
          refine ⟨951724337231040235255457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634482891487360156836971 951724337231040235255457)
          ·
            refine ⟨713793252923280176441593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 951724337231040235255457 713793252923280176441593)
            ·
              refine ⟨535344939692460132331195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 713793252923280176441593 535344939692460132331195)
              ·
                refine ⟨803017409538690198496793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535344939692460132331195 803017409538690198496793)
                ·
                  refine ⟨602263057154017648872595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 803017409538690198496793 602263057154017648872595)
                  ·
                    refine ⟨903394585731026473308893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 602263057154017648872595 903394585731026473308893)
                    ·
                      refine ⟨338772969649134927490835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 903394585731026473308893 338772969649134927490835)
                      ·
                        rfl

theorem cell23_659758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_659758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659758 prefixEnd_659758 := by exact prefixLift 659758
  have htrace : WordTrace (prefixWord ++ tailWord_659758) baseStart_659758 baseEnd_659758 := by
    simpa [prefixWord, tailWord_659758, baseEnd_659758] using wordTrace_append hprefix tailTrace_659758
  have hstable : (prefixWord ++ tailWord_659758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659758).length < 2 ^ (prefixWord ++ tailWord_659758).sum := by decide
  have hdescent : baseEnd_659758 < baseStart_659758 := by decide
  rcases family_descends (prefixWord ++ tailWord_659758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659763 : List Nat := [1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 3]
def baseStart_659763 : Nat := 118140960795 + 659763 * 2 ^ 59
def prefixEnd_659763 : Nat := 4983230072969 + 3 ^ 40 * 659763 * 2
def baseEnd_659763 : Nat := 338775537052407407928311

theorem tailTrace_659763 : CollatzResearch.WordTrace tailWord_659763 prefixEnd_659763 338775537052407407928311 := by
  unfold tailWord_659763
  simp only [CollatzResearch.WordTrace]
  refine ⟨24063533508798804394711943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16042355672532536263141295 24063533508798804394711943)
  ·
    refine ⟨36095300263198206592067915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24063533508798804394711943 36095300263198206592067915)
    ·
      refine ⟨54142950394797309888101873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36095300263198206592067915 54142950394797309888101873)
      ·
        refine ⟨40607212796097982416076405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54142950394797309888101873 40607212796097982416076405)
        ·
          refine ⟨3806926199634185851507163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40607212796097982416076405 3806926199634185851507163)
          ·
            refine ⟨5710389299451278777260745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3806926199634185851507163 5710389299451278777260745)
            ·
              refine ⟨4282791974588459082945559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5710389299451278777260745 4282791974588459082945559)
              ·
                refine ⟨6424187961882688624418339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4282791974588459082945559 6424187961882688624418339)
                ·
                  refine ⟨9636281942824032936627509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6424187961882688624418339 9636281942824032936627509)
                  ·
                    refine ⟨903401432139753087808829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9636281942824032936627509 903401432139753087808829)
                    ·
                      refine ⟨338775537052407407928311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 903401432139753087808829 338775537052407407928311)
                      ·
                        rfl

theorem cell23_659763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 5, 3].length) (baseStart_659763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659763 prefixEnd_659763 := by exact prefixLift 659763
  have htrace : WordTrace (prefixWord ++ tailWord_659763) baseStart_659763 baseEnd_659763 := by
    simpa [prefixWord, tailWord_659763, baseEnd_659763] using wordTrace_append hprefix tailTrace_659763
  have hstable : (prefixWord ++ tailWord_659763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659763).length < 2 ^ (prefixWord ++ tailWord_659763).sum := by decide
  have hdescent : baseEnd_659763 < baseStart_659763 := by decide
  rcases family_descends (prefixWord ++ tailWord_659763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659793 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 1, 2, 5]
def baseStart_659793 : Nat := 118140960795 + 659793 * 2 ^ 59
def prefixEnd_659793 : Nat := 4983230072969 + 3 ^ 40 * 659793 * 2
def baseEnd_659793 : Nat := 338790941472042290553173

theorem tailTrace_659793 : CollatzResearch.WordTrace tailWord_659793 prefixEnd_659793 338790941472042290553173 := by
  unfold tailWord_659793
  simp only [CollatzResearch.WordTrace]
  refine ⟨24064627698690119518304033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16043085132460079678869355 24064627698690119518304033)
  ·
    refine ⟨18048470774017589638728025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24064627698690119518304033 18048470774017589638728025)
    ·
      refine ⟨13536353080513192229046019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18048470774017589638728025 13536353080513192229046019)
      ·
        refine ⟨20304529620769788343569029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13536353080513192229046019 20304529620769788343569029)
        ·
          refine ⟨3807099303894335314419193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20304529620769788343569029 3807099303894335314419193)
          ·
            refine ⟨2855324477920751485814395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3807099303894335314419193 2855324477920751485814395)
            ·
              refine ⟨4282986716881127228721593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2855324477920751485814395 4282986716881127228721593)
              ·
                refine ⟨3212240037660845421541195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4282986716881127228721593 3212240037660845421541195)
                ·
                  refine ⟨4818360056491268132311793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3212240037660845421541195 4818360056491268132311793)
                  ·
                    refine ⟨3613770042368451099233845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4818360056491268132311793 3613770042368451099233845)
                    ·
                      refine ⟨338790941472042290553173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3613770042368451099233845 338790941472042290553173)
                      ·
                        rfl

theorem cell23_659793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_659793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659793 prefixEnd_659793 := by exact prefixLift 659793
  have htrace : WordTrace (prefixWord ++ tailWord_659793) baseStart_659793 baseEnd_659793 := by
    simpa [prefixWord, tailWord_659793, baseEnd_659793] using wordTrace_append hprefix tailTrace_659793
  have hstable : (prefixWord ++ tailWord_659793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659793).length < 2 ^ (prefixWord ++ tailWord_659793).sum := by decide
  have hdescent : baseEnd_659793 < baseStart_659793 := by decide
  rcases family_descends (prefixWord ++ tailWord_659793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659804 : List Nat := [2, 2, 4, 3, 1, 1, 1, 4, 5]
def baseStart_659804 : Nat := 118140960795 + 659804 * 2 ^ 59
def prefixEnd_659804 : Nat := 4983230072969 + 3 ^ 40 * 659804 * 2
def baseEnd_659804 : Nat := 37644065528804638612847

theorem tailTrace_659804 : CollatzResearch.WordTrace tailWord_659804 prefixEnd_659804 37644065528804638612847 := by
  unfold tailWord_659804
  simp only [CollatzResearch.WordTrace]
  refine ⟨12032514450825134198477233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16043352601100178931302977 12032514450825134198477233)
  ·
    refine ⟨9024385838118850648857925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12032514450825134198477233 9024385838118850648857925)
    ·
      refine ⟨1692072344647284496660861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9024385838118850648857925 1692072344647284496660861)
      ·
        refine ⟨634527129242731686247823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1692072344647284496660861 634527129242731686247823)
        ·
          refine ⟨951790693864097529371735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634527129242731686247823 951790693864097529371735)
          ·
            refine ⟨1427686040796146294057603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 951790693864097529371735 1427686040796146294057603)
            ·
              refine ⟨2141529061194219441086405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1427686040796146294057603 2141529061194219441086405)
              ·
                refine ⟨401536698973916145203701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2141529061194219441086405 401536698973916145203701)
                ·
                  refine ⟨37644065528804638612847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 401536698973916145203701 37644065528804638612847)
                  ·
                    rfl

theorem cell23_659804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 4, 5].length) (baseStart_659804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659804 prefixEnd_659804 := by exact prefixLift 659804
  have htrace : WordTrace (prefixWord ++ tailWord_659804) baseStart_659804 baseEnd_659804 := by
    simpa [prefixWord, tailWord_659804, baseEnd_659804] using wordTrace_append hprefix tailTrace_659804
  have hstable : (prefixWord ++ tailWord_659804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659804).length < 2 ^ (prefixWord ++ tailWord_659804).sum := by decide
  have hdescent : baseEnd_659804 < baseStart_659804 := by decide
  rcases family_descends (prefixWord ++ tailWord_659804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659810 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_659810 : Nat := 118140960795 + 659810 * 2 ^ 59
def prefixEnd_659810 : Nat := 4983230072969 + 3 ^ 40 * 659810 * 2
def baseEnd_659810 : Nat := 338799670643168724040595

theorem tailTrace_659810 : CollatzResearch.WordTrace tailWord_659810 prefixEnd_659810 338799670643168724040595 := by
  unfold tailWord_659810
  simp only [CollatzResearch.WordTrace]
  refine ⟨6016311934907132855418221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16043498493085687614448589 6016311934907132855418221)
  ·
    refine ⟨2256116975590174820781833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6016311934907132855418221 2256116975590174820781833)
    ·
      refine ⟨1692087731692631115586375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2256116975590174820781833 1692087731692631115586375)
      ·
        refine ⟨2538131597538946673379563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1692087731692631115586375 2538131597538946673379563)
        ·
          refine ⟨3807197396308420010069345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2538131597538946673379563 3807197396308420010069345)
          ·
            refine ⟨2855398047231315007552009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3807197396308420010069345 2855398047231315007552009)
            ·
              refine ⟨2141548535423486255664007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2855398047231315007552009 2141548535423486255664007)
              ·
                refine ⟨3212322803135229383496011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2141548535423486255664007 3212322803135229383496011)
                ·
                  refine ⟨4818484204702844075244017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3212322803135229383496011 4818484204702844075244017)
                  ·
                    refine ⟨3613863153527133056433013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4818484204702844075244017 3613863153527133056433013)
                    ·
                      refine ⟨338799670643168724040595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3613863153527133056433013 338799670643168724040595)
                      ·
                        rfl

theorem cell23_659810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_659810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659810 prefixEnd_659810 := by exact prefixLift 659810
  have htrace : WordTrace (prefixWord ++ tailWord_659810) baseStart_659810 baseEnd_659810 := by
    simpa [prefixWord, tailWord_659810, baseEnd_659810] using wordTrace_append hprefix tailTrace_659810
  have hstable : (prefixWord ++ tailWord_659810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659810).length < 2 ^ (prefixWord ++ tailWord_659810).sum := by decide
  have hdescent : baseEnd_659810 < baseStart_659810 := by decide
  rcases family_descends (prefixWord ++ tailWord_659810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659837 : List Nat := [1, 4, 1, 1, 2, 5, 1, 1, 2, 1, 4]
def baseStart_659837 : Nat := 118140960795 + 659837 * 2 ^ 59
def prefixEnd_659837 : Nat := 4983230072969 + 3 ^ 40 * 659837 * 2
def baseEnd_659837 : Nat := 338813534620840118402971

theorem tailTrace_659837 : CollatzResearch.WordTrace tailWord_659837 prefixEnd_659837 338813534620840118402971 := by
  unfold tailWord_659837
  simp only [CollatzResearch.WordTrace]
  refine ⟨24066232510530715032905765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16044155007020476688603843 24066232510530715032905765)
  ·
    refine ⟨4512418595724509068669831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24066232510530715032905765 4512418595724509068669831)
    ·
      refine ⟨6768627893586763603004747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4512418595724509068669831 6768627893586763603004747)
      ·
        refine ⟨10152941840380145404507121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6768627893586763603004747 10152941840380145404507121)
        ·
          refine ⟨7614706380285109053380341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10152941840380145404507121 7614706380285109053380341)
          ·
            refine ⟨713878723151728973754407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7614706380285109053380341 713878723151728973754407)
            ·
              refine ⟨1070818084727593460631611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713878723151728973754407 1070818084727593460631611)
              ·
                refine ⟨1606227127091390190947417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1070818084727593460631611 1606227127091390190947417)
                ·
                  refine ⟨1204670345318542643210563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1606227127091390190947417 1204670345318542643210563)
                  ·
                    refine ⟨1807005517977813964815845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1204670345318542643210563 1807005517977813964815845)
                    ·
                      refine ⟨338813534620840118402971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1807005517977813964815845 338813534620840118402971)
                      ·
                        rfl

theorem cell23_659837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_659837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659837 prefixEnd_659837 := by exact prefixLift 659837
  have htrace : WordTrace (prefixWord ++ tailWord_659837) baseStart_659837 baseEnd_659837 := by
    simpa [prefixWord, tailWord_659837, baseEnd_659837] using wordTrace_append hprefix tailTrace_659837
  have hstable : (prefixWord ++ tailWord_659837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659837).length < 2 ^ (prefixWord ++ tailWord_659837).sum := by decide
  have hdescent : baseEnd_659837 < baseStart_659837 := by decide
  rcases family_descends (prefixWord ++ tailWord_659837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659863 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 6]
def baseStart_659863 : Nat := 118140960795 + 659863 * 2 ^ 59
def prefixEnd_659863 : Nat := 4983230072969 + 3 ^ 40 * 659863 * 2
def baseEnd_659863 : Nat := 338826885117857016677851

theorem tailTrace_659863 : CollatzResearch.WordTrace tailWord_659863 prefixEnd_659863 338826885117857016677851 := by
  unfold tailWord_659863
  simp only [CollatzResearch.WordTrace]
  refine ⟨24067180808436521473352243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16044787205624347648901495 24067180808436521473352243)
  ·
    refine ⟨36100771212654782210028365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24067180808436521473352243 36100771212654782210028365)
    ·
      refine ⟨13537789204745543328760637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36100771212654782210028365 13537789204745543328760637)
      ·
        refine ⟨5076670951779578748285239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13537789204745543328760637 5076670951779578748285239)
        ·
          refine ⟨7615006427669368122427859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5076670951779578748285239 7615006427669368122427859)
          ·
            refine ⟨11422509641504052183641789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7615006427669368122427859 11422509641504052183641789)
            ·
              refine ⟨4283441115564019568865671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11422509641504052183641789 4283441115564019568865671)
              ·
                refine ⟨6425161673346029353298507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4283441115564019568865671 6425161673346029353298507)
                ·
                  refine ⟨9637742510019044029947761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6425161673346029353298507 9637742510019044029947761)
                  ·
                    refine ⟨7228306882514283022460821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9637742510019044029947761 7228306882514283022460821)
                    ·
                      refine ⟨338826885117857016677851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7228306882514283022460821 338826885117857016677851)
                      ·
                        rfl

theorem cell23_659863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_659863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659863 prefixEnd_659863 := by exact prefixLift 659863
  have htrace : WordTrace (prefixWord ++ tailWord_659863) baseStart_659863 baseEnd_659863 := by
    simpa [prefixWord, tailWord_659863, baseEnd_659863] using wordTrace_append hprefix tailTrace_659863
  have hstable : (prefixWord ++ tailWord_659863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659863).length < 2 ^ (prefixWord ++ tailWord_659863).sum := by decide
  have hdescent : baseEnd_659863 < baseStart_659863 := by decide
  rcases family_descends (prefixWord ++ tailWord_659863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659864 : List Nat := [2, 1, 2, 5, 1, 1, 2, 4, 1, 4]
def baseStart_659864 : Nat := 118140960795 + 659864 * 2 ^ 59
def prefixEnd_659864 : Nat := 4983230072969 + 3 ^ 40 * 659864 * 2
def baseEnd_659864 : Nat := 112942466199503837588449

theorem tailTrace_659864 : CollatzResearch.WordTrace tailWord_659864 prefixEnd_659864 112942466199503837588449 := by
  unfold tailWord_659864
  simp only [CollatzResearch.WordTrace]
  refine ⟨12033608640716449322069323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16044811520955265762759097 12033608640716449322069323)
  ·
    refine ⟨18050412961074673983103985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12033608640716449322069323 18050412961074673983103985)
    ·
      refine ⟨13537809720806005487327989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18050412961074673983103985 13537809720806005487327989)
      ·
        refine ⟨1269169661325563014436999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13537809720806005487327989 1269169661325563014436999)
        ·
          refine ⟨1903754491988344521655499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1269169661325563014436999 1903754491988344521655499)
          ·
            refine ⟨2855631737982516782483249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1903754491988344521655499 2855631737982516782483249)
            ·
              refine ⟨2141723803486887586862437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2855631737982516782483249 2141723803486887586862437)
              ·
                refine ⟨401573213153791422536707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2141723803486887586862437 401573213153791422536707)
                ·
                  refine ⟨602359819730687133805061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 401573213153791422536707 602359819730687133805061)
                  ·
                    refine ⟨112942466199503837588449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 602359819730687133805061 112942466199503837588449)
                    ·
                      rfl

theorem cell23_659864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 1, 4].length) (baseStart_659864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659864 prefixEnd_659864 := by exact prefixLift 659864
  have htrace : WordTrace (prefixWord ++ tailWord_659864) baseStart_659864 baseEnd_659864 := by
    simpa [prefixWord, tailWord_659864, baseEnd_659864] using wordTrace_append hprefix tailTrace_659864
  have hstable : (prefixWord ++ tailWord_659864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659864).length < 2 ^ (prefixWord ++ tailWord_659864).sum := by decide
  have hdescent : baseEnd_659864 < baseStart_659864 := by decide
  rcases family_descends (prefixWord ++ tailWord_659864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659897 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 1, 5, 2]
def baseStart_659897 : Nat := 118140960795 + 659897 * 2 ^ 59
def prefixEnd_659897 : Nat := 4983230072969 + 3 ^ 40 * 659897 * 2
def baseEnd_659897 : Nat := 338844343460109883652695

theorem tailTrace_659897 : CollatzResearch.WordTrace tailWord_659897 prefixEnd_659897 338844343460109883652695 := by
  unfold tailWord_659897
  simp only [CollatzResearch.WordTrace]
  refine ⟨24068420890313345280089945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16045613926875563520059963 24068420890313345280089945)
  ·
    refine ⟨18051315667735008960067459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24068420890313345280089945 18051315667735008960067459)
    ·
      refine ⟨27076973501602513440101189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18051315667735008960067459 27076973501602513440101189)
      ·
        refine ⟨5076932531550471270018973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27076973501602513440101189 5076932531550471270018973)
        ·
          refine ⟨1903849699331426726257115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5076932531550471270018973 1903849699331426726257115)
          ·
            refine ⟨2855774548997140089385673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1903849699331426726257115 2855774548997140089385673)
            ·
              refine ⟨2141830911747855067039255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2855774548997140089385673 2141830911747855067039255)
              ·
                refine ⟨3212746367621782600558883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2141830911747855067039255 3212746367621782600558883)
                ·
                  refine ⟨4819119551432673900838325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3212746367621782600558883 4819119551432673900838325)
                  ·
                    refine ⟨451792457946813178203593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4819119551432673900838325 451792457946813178203593)
                    ·
                      refine ⟨338844343460109883652695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 451792457946813178203593 338844343460109883652695)
                      ·
                        rfl

theorem cell23_659897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_659897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659897 prefixEnd_659897 := by exact prefixLift 659897
  have htrace : WordTrace (prefixWord ++ tailWord_659897) baseStart_659897 baseEnd_659897 := by
    simpa [prefixWord, tailWord_659897, baseEnd_659897] using wordTrace_append hprefix tailTrace_659897
  have hstable : (prefixWord ++ tailWord_659897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659897).length < 2 ^ (prefixWord ++ tailWord_659897).sum := by decide
  have hdescent : baseEnd_659897 < baseStart_659897 := by decide
  rcases family_descends (prefixWord ++ tailWord_659897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659930 : List Nat := [3, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5]
def baseStart_659930 : Nat := 118140960795 + 659930 * 2 ^ 59
def prefixEnd_659930 : Nat := 4983230072969 + 3 ^ 40 * 659930 * 2
def baseEnd_659930 : Nat := 338861288321708254540043

theorem tailTrace_659930 : CollatzResearch.WordTrace tailWord_659930 prefixEnd_659930 338861288321708254540043 := by
  unfold tailWord_659930
  simp only [CollatzResearch.WordTrace]
  refine ⟨6017406124798447979010311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16046416332795861277360829 6017406124798447979010311)
  ·
    refine ⟨9026109187197671968515467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6017406124798447979010311 9026109187197671968515467)
    ·
      refine ⟨13539163780796507952773201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9026109187197671968515467 13539163780796507952773201)
      ·
        refine ⟨10154372835597380964579901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13539163780796507952773201 10154372835597380964579901)
        ·
          refine ⟨3807889813349017861717463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10154372835597380964579901 3807889813349017861717463)
          ·
            refine ⟨5711834720023526792576195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3807889813349017861717463 5711834720023526792576195)
            ·
              refine ⟨8567752080035290188864293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5711834720023526792576195 8567752080035290188864293)
              ·
                refine ⟨1606453515006616910412055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8567752080035290188864293 1606453515006616910412055)
                ·
                  refine ⟨2409680272509925365618083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1606453515006616910412055 2409680272509925365618083)
                  ·
                    refine ⟨3614520408764888048427125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2409680272509925365618083 3614520408764888048427125)
                    ·
                      refine ⟨338861288321708254540043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3614520408764888048427125 338861288321708254540043)
                      ·
                        rfl

theorem cell23_659930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_659930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659930 prefixEnd_659930 := by exact prefixLift 659930
  have htrace : WordTrace (prefixWord ++ tailWord_659930) baseStart_659930 baseEnd_659930 := by
    simpa [prefixWord, tailWord_659930, baseEnd_659930] using wordTrace_append hprefix tailTrace_659930
  have hstable : (prefixWord ++ tailWord_659930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659930).length < 2 ^ (prefixWord ++ tailWord_659930).sum := by decide
  have hdescent : baseEnd_659930 < baseStart_659930 := by decide
  rcases family_descends (prefixWord ++ tailWord_659930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659937 : List Nat := [1, 2, 3, 1, 2, 2, 3, 3, 2, 4]
def baseStart_659937 : Nat := 118140960795 + 659937 * 2 ^ 59
def prefixEnd_659937 : Nat := 4983230072969 + 3 ^ 40 * 659937 * 2
def baseEnd_659937 : Nat := 112954960895429909050837

theorem tailTrace_659937 : CollatzResearch.WordTrace tailWord_659937 prefixEnd_659937 112954960895429909050837 := by
  unfold tailWord_659937
  simp only [CollatzResearch.WordTrace]
  refine ⟨24069879810168432111546065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16046586540112288074364043 24069879810168432111546065)
  ·
    refine ⟨18052409857626324083659549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24069879810168432111546065 18052409857626324083659549)
    ·
      refine ⟨6769653696609871531372331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18052409857626324083659549 6769653696609871531372331)
      ·
        refine ⟨10154480544914807297058497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6769653696609871531372331 10154480544914807297058497)
        ·
          refine ⟨7615860408686105472793873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10154480544914807297058497 7615860408686105472793873)
          ·
            refine ⟨5711895306514579104595405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7615860408686105472793873 5711895306514579104595405)
            ·
              refine ⟨2141960739942967164223277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5711895306514579104595405 2141960739942967164223277)
              ·
                refine ⟨803235277478612686583729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2141960739942967164223277 803235277478612686583729)
                ·
                  refine ⟨602426458108959514937797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 803235277478612686583729 602426458108959514937797)
                  ·
                    refine ⟨112954960895429909050837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 602426458108959514937797 112954960895429909050837)
                    ·
                      rfl

theorem cell23_659937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_659937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659937 prefixEnd_659937 := by exact prefixLift 659937
  have htrace : WordTrace (prefixWord ++ tailWord_659937) baseStart_659937 baseEnd_659937 := by
    simpa [prefixWord, tailWord_659937, baseEnd_659937] using wordTrace_append hprefix tailTrace_659937
  have hstable : (prefixWord ++ tailWord_659937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659937).length < 2 ^ (prefixWord ++ tailWord_659937).sum := by decide
  have hdescent : baseEnd_659937 < baseStart_659937 := by decide
  rcases family_descends (prefixWord ++ tailWord_659937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659941 : List Nat := [1, 3, 1, 5, 3, 1, 1, 2, 1, 5]
def baseStart_659941 : Nat := 118140960795 + 659941 * 2 ^ 59
def prefixEnd_659941 : Nat := 4983230072969 + 3 ^ 40 * 659941 * 2
def baseEnd_659941 : Nat := 112955645536302570500831

theorem tailTrace_659941 : CollatzResearch.WordTrace tailWord_659941 prefixEnd_659941 112955645536302570500831 := by
  unfold tailWord_659941
  simp only [CollatzResearch.WordTrace]
  refine ⟨24070025702153940794691677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16046683801435960529794451 24070025702153940794691677)
  ·
    refine ⟨9026259638307727798009379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24070025702153940794691677 9026259638307727798009379)
    ·
      refine ⟨13539389457461591697014069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9026259638307727798009379 13539389457461591697014069)
      ·
        refine ⟨1269317761637024221595069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13539389457461591697014069 1269317761637024221595069)
        ·
          refine ⟨475994160613884083098151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1269317761637024221595069 475994160613884083098151)
          ·
            refine ⟨713991240920826124647227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475994160613884083098151 713991240920826124647227)
            ·
              refine ⟨1070986861381239186970841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713991240920826124647227 1070986861381239186970841)
              ·
                refine ⟨803240146035929390228131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1070986861381239186970841 803240146035929390228131)
                ·
                  refine ⟨1204860219053894085342197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803240146035929390228131 1204860219053894085342197)
                  ·
                    refine ⟨112955645536302570500831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1204860219053894085342197 112955645536302570500831)
                    ·
                      rfl

theorem cell23_659941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 1, 5].length) (baseStart_659941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659941 prefixEnd_659941 := by exact prefixLift 659941
  have htrace : WordTrace (prefixWord ++ tailWord_659941) baseStart_659941 baseEnd_659941 := by
    simpa [prefixWord, tailWord_659941, baseEnd_659941] using wordTrace_append hprefix tailTrace_659941
  have hstable : (prefixWord ++ tailWord_659941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659941).length < 2 ^ (prefixWord ++ tailWord_659941).sum := by decide
  have hdescent : baseEnd_659941 < baseStart_659941 := by decide
  rcases family_descends (prefixWord ++ tailWord_659941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659944 : List Nat := [2, 1, 4, 1, 1, 5, 1, 2, 1, 1, 4]
def baseStart_659944 : Nat := 118140960795 + 659944 * 2 ^ 59
def prefixEnd_659944 : Nat := 4983230072969 + 3 ^ 40 * 659944 * 2
def baseEnd_659944 : Nat := 338868477050871199764979

theorem tailTrace_659944 : CollatzResearch.WordTrace tailWord_659944 prefixEnd_659944 338868477050871199764979 := by
  unfold tailWord_659944
  simp only [CollatzResearch.WordTrace]
  refine ⟨12035067560571536153525443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16046756747428714871367257 12035067560571536153525443)
  ·
    refine ⟨18052601340857304230288165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12035067560571536153525443 18052601340857304230288165)
    ·
      refine ⟨3384862751410744543179031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18052601340857304230288165 3384862751410744543179031)
      ·
        refine ⟨5077294127116116814768547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3384862751410744543179031 5077294127116116814768547)
        ·
          refine ⟨7615941190674175222152821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5077294127116116814768547 7615941190674175222152821)
          ·
            refine ⟨713994486625703927076827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7615941190674175222152821 713994486625703927076827)
            ·
              refine ⟨1070991729938555890615241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713994486625703927076827 1070991729938555890615241)
              ·
                refine ⟨803243797453916917961431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1070991729938555890615241 803243797453916917961431)
                ·
                  refine ⟨1204865696180875376942147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803243797453916917961431 1204865696180875376942147)
                  ·
                    refine ⟨1807298544271313065413221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1204865696180875376942147 1807298544271313065413221)
                    ·
                      refine ⟨338868477050871199764979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1807298544271313065413221 338868477050871199764979)
                      ·
                        rfl

theorem cell23_659944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_659944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659944 prefixEnd_659944 := by exact prefixLift 659944
  have htrace : WordTrace (prefixWord ++ tailWord_659944) baseStart_659944 baseEnd_659944 := by
    simpa [prefixWord, tailWord_659944, baseEnd_659944] using wordTrace_append hprefix tailTrace_659944
  have hstable : (prefixWord ++ tailWord_659944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659944).length < 2 ^ (prefixWord ++ tailWord_659944).sum := by decide
  have hdescent : baseEnd_659944 < baseStart_659944 := by decide
  rcases family_descends (prefixWord ++ tailWord_659944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659950 : List Nat := [4, 1, 2, 1, 2, 2, 2, 9]
def baseStart_659950 : Nat := 118140960795 + 659950 * 2 ^ 59
def prefixEnd_659950 : Nat := 4983230072969 + 3 ^ 40 * 659950 * 2
def baseEnd_659950 : Nat := 12550798442029562084813

theorem tailTrace_659950 : CollatzResearch.WordTrace tailWord_659950 prefixEnd_659950 12550798442029562084813 := by
  unfold tailWord_659950
  simp only [CollatzResearch.WordTrace]
  refine ⟨3008794244890166916471163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16046902639414223554512869 3008794244890166916471163)
  ·
    refine ⟨4513191367335250374706745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3008794244890166916471163 4513191367335250374706745)
    ·
      refine ⟨3384893525501437781030059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4513191367335250374706745 3384893525501437781030059)
      ·
        refine ⟨5077340288252156671545089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3384893525501437781030059 5077340288252156671545089)
        ·
          refine ⟨3808005216189117503658817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5077340288252156671545089 3808005216189117503658817)
          ·
            refine ⟨2856003912141838127744113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3808005216189117503658817 2856003912141838127744113)
            ·
              refine ⟨2142002934106378595808085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2856003912141838127744113 2142002934106378595808085)
              ·
                refine ⟨12550798442029562084813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2142002934106378595808085 12550798442029562084813)
                ·
                  rfl

theorem cell23_659950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 9].length) (baseStart_659950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659950 prefixEnd_659950 := by exact prefixLift 659950
  have htrace : WordTrace (prefixWord ++ tailWord_659950) baseStart_659950 baseEnd_659950 := by
    simpa [prefixWord, tailWord_659950, baseEnd_659950] using wordTrace_append hprefix tailTrace_659950
  have hstable : (prefixWord ++ tailWord_659950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659950).length < 2 ^ (prefixWord ++ tailWord_659950).sum := by decide
  have hdescent : baseEnd_659950 < baseStart_659950 := by decide
  rcases family_descends (prefixWord ++ tailWord_659950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659963 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 3, 9]
def baseStart_659963 : Nat := 118140960795 + 659963 * 2 ^ 59
def prefixEnd_659963 : Nat := 4983230072969 + 3 ^ 40 * 659963 * 2
def baseEnd_659963 : Nat := 112959411061102208475797

theorem tailTrace_659963 : CollatzResearch.WordTrace tailWord_659963 prefixEnd_659963 112959411061102208475797 := by
  unfold tailWord_659963
  simp only [CollatzResearch.WordTrace]
  refine ⟨24070828108074238551992543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16047218738716159034661695 24070828108074238551992543)
  ·
    refine ⟨36106242162111357827988815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24070828108074238551992543 36106242162111357827988815)
    ·
      refine ⟨54159363243167036741983223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36106242162111357827988815 54159363243167036741983223)
      ·
        refine ⟨81239044864750555112974835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54159363243167036741983223 81239044864750555112974835)
        ·
          refine ⟨121858567297125832669462253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81239044864750555112974835 121858567297125832669462253)
          ·
            refine ⟨45696962736422187251048345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121858567297125832669462253 45696962736422187251048345)
            ·
              refine ⟨34272722052316640438286259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45696962736422187251048345 34272722052316640438286259)
              ·
                refine ⟨51409083078474960657429389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34272722052316640438286259 51409083078474960657429389)
                ·
                  refine ⟨19278406154428110246536021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51409083078474960657429389 19278406154428110246536021)
                  ·
                    refine ⟨112959411061102208475797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 19278406154428110246536021 112959411061102208475797)
                    ·
                      rfl

theorem cell23_659963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 9].length) (baseStart_659963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659963 prefixEnd_659963 := by exact prefixLift 659963
  have htrace : WordTrace (prefixWord ++ tailWord_659963) baseStart_659963 baseEnd_659963 := by
    simpa [prefixWord, tailWord_659963, baseEnd_659963] using wordTrace_append hprefix tailTrace_659963
  have hstable : (prefixWord ++ tailWord_659963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659963).length < 2 ^ (prefixWord ++ tailWord_659963).sum := by decide
  have hdescent : baseEnd_659963 < baseStart_659963 := by decide
  rcases family_descends (prefixWord ++ tailWord_659963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659980 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 2, 7]
def baseStart_659980 : Nat := 118140960795 + 659980 * 2 ^ 59
def prefixEnd_659980 : Nat := 4983230072969 + 3 ^ 40 * 659980 * 2
def baseEnd_659980 : Nat := 112962320784811019638271

theorem tailTrace_659980 : CollatzResearch.WordTrace tailWord_659980 prefixEnd_659980 112962320784811019638271 := by
  unfold tailWord_659980
  simp only [CollatzResearch.WordTrace]
  refine ⟨12035724074506325227680697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16047632099341766970240929 12035724074506325227680697)
  ·
    refine ⟨9026793055879743920760523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12035724074506325227680697 9026793055879743920760523)
    ·
      refine ⟨13540189583819615881140785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9026793055879743920760523 13540189583819615881140785)
      ·
        refine ⟨10155142187864711910855589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13540189583819615881140785 10155142187864711910855589)
        ·
          refine ⟨1904089160224633483285423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10155142187864711910855589 1904089160224633483285423)
          ·
            refine ⟨2856133740336950224928135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1904089160224633483285423 2856133740336950224928135)
            ·
              refine ⟨4284200610505425337392203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2856133740336950224928135 4284200610505425337392203)
              ·
                refine ⟨6426300915758138006088305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4284200610505425337392203 6426300915758138006088305)
                ·
                  refine ⟨4819725686818603504566229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6426300915758138006088305 4819725686818603504566229)
                  ·
                    refine ⟨112962320784811019638271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4819725686818603504566229 112962320784811019638271)
                    ·
                      rfl

theorem cell23_659980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_659980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659980 prefixEnd_659980 := by exact prefixLift 659980
  have htrace : WordTrace (prefixWord ++ tailWord_659980) baseStart_659980 baseEnd_659980 := by
    simpa [prefixWord, tailWord_659980, baseEnd_659980] using wordTrace_append hprefix tailTrace_659980
  have hstable : (prefixWord ++ tailWord_659980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659980).length < 2 ^ (prefixWord ++ tailWord_659980).sum := by decide
  have hdescent : baseEnd_659980 < baseStart_659980 := by decide
  rcases family_descends (prefixWord ++ tailWord_659980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659981 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_659981 : Nat := 118140960795 + 659981 * 2 ^ 59
def prefixEnd_659981 : Nat := 4983230072969 + 3 ^ 40 * 659981 * 2
def baseEnd_659981 : Nat := 338887475835087555002309

theorem tailTrace_659981 : CollatzResearch.WordTrace tailWord_659981 prefixEnd_659981 338887475835087555002309 := by
  unfold tailWord_659981
  simp only [CollatzResearch.WordTrace]
  refine ⟨24071484622009027626147797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16047656414672685084098531 24071484622009027626147797)
  ·
    refine ⟨564175420828336584987839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 24071484622009027626147797 564175420828336584987839)
    ·
      refine ⟨846263131242504877481759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 564175420828336584987839 846263131242504877481759)
      ·
        refine ⟨1269394696863757316222639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 846263131242504877481759 1269394696863757316222639)
        ·
          refine ⟨1904092045295635974333959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1269394696863757316222639 1904092045295635974333959)
          ·
            refine ⟨2856138067943453961500939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1904092045295635974333959 2856138067943453961500939)
            ·
              refine ⟨4284207101915180942251409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2856138067943453961500939 4284207101915180942251409)
              ·
                refine ⟨3213155326436385706688557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4284207101915180942251409 3213155326436385706688557)
                ·
                  refine ⟨1204933247413644640008209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3213155326436385706688557 1204933247413644640008209)
                  ·
                    refine ⟨903699935560233480006157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1204933247413644640008209 903699935560233480006157)
                    ·
                      refine ⟨338887475835087555002309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 903699935560233480006157 338887475835087555002309)
                      ·
                        rfl

theorem cell23_659981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_659981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659981 prefixEnd_659981 := by exact prefixLift 659981
  have htrace : WordTrace (prefixWord ++ tailWord_659981) baseStart_659981 baseEnd_659981 := by
    simpa [prefixWord, tailWord_659981, baseEnd_659981] using wordTrace_append hprefix tailTrace_659981
  have hstable : (prefixWord ++ tailWord_659981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659981).length < 2 ^ (prefixWord ++ tailWord_659981).sum := by decide
  have hdescent : baseEnd_659981 < baseStart_659981 := by decide
  rcases family_descends (prefixWord ++ tailWord_659981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659987 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 5, 3, 2]
def baseStart_659987 : Nat := 118140960795 + 659987 * 2 ^ 59
def prefixEnd_659987 : Nat := 4983230072969 + 3 ^ 40 * 659987 * 2
def baseEnd_659987 : Nat := 338890556719014531527281

theorem tailTrace_659987 : CollatzResearch.WordTrace tailWord_659987 prefixEnd_659987 338890556719014531527281 := by
  unfold tailWord_659987
  simp only [CollatzResearch.WordTrace]
  refine ⟨24071703459987290650866215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16047802306658193767244143 24071703459987290650866215)
  ·
    refine ⟨36107555189980935976299323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24071703459987290650866215 36107555189980935976299323)
    ·
      refine ⟨54161332784971403964448985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36107555189980935976299323 54161332784971403964448985)
      ·
        refine ⟨40620999588728552973336739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54161332784971403964448985 40620999588728552973336739)
        ·
          refine ⟨60931499383092829460005109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40620999588728552973336739 60931499383092829460005109)
          ·
            refine ⟨5712328067164952761875479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60931499383092829460005109 5712328067164952761875479)
            ·
              refine ⟨8568492100747429142813219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5712328067164952761875479 8568492100747429142813219)
              ·
                refine ⟨12852738151121143714219829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8568492100747429142813219 12852738151121143714219829)
                ·
                  refine ⟨1204944201667607223208109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12852738151121143714219829 1204944201667607223208109)
                  ·
                    refine ⟨451854075625352708703041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1204944201667607223208109 451854075625352708703041)
                    ·
                      refine ⟨338890556719014531527281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 451854075625352708703041 338890556719014531527281)
                      ·
                        rfl

theorem cell23_659987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 5, 3, 2].length) (baseStart_659987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659987 prefixEnd_659987 := by exact prefixLift 659987
  have htrace : WordTrace (prefixWord ++ tailWord_659987) baseStart_659987 baseEnd_659987 := by
    simpa [prefixWord, tailWord_659987, baseEnd_659987] using wordTrace_append hprefix tailTrace_659987
  have hstable : (prefixWord ++ tailWord_659987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659987).length < 2 ^ (prefixWord ++ tailWord_659987).sum := by decide
  have hdescent : baseEnd_659987 < baseStart_659987 := by decide
  rcases family_descends (prefixWord ++ tailWord_659987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_659994 : List Nat := [3, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3]
def baseStart_659994 : Nat := 118140960795 + 659994 * 2 ^ 59
def prefixEnd_659994 : Nat := 4983230072969 + 3 ^ 40 * 659994 * 2
def baseEnd_659994 : Nat := 338894151083596004139749

theorem tailTrace_659994 : CollatzResearch.WordTrace tailWord_659994 prefixEnd_659994 338894151083596004139749 := by
  unfold tailWord_659994
  simp only [CollatzResearch.WordTrace]
  refine ⟨6017989692740482711592759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16047972513974620564247357 6017989692740482711592759)
  ·
    refine ⟨9026984539110724067389139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6017989692740482711592759 9026984539110724067389139)
    ·
      refine ⟨13540476808666086101083709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9026984539110724067389139 13540476808666086101083709)
      ·
        refine ⟨5077678803249782287906391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13540476808666086101083709 5077678803249782287906391)
        ·
          refine ⟨7616518204874673431859587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5077678803249782287906391 7616518204874673431859587)
          ·
            refine ⟨11424777307312010147789381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7616518204874673431859587 11424777307312010147789381)
            ·
              refine ⟨2142145745121001902710509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11424777307312010147789381 2142145745121001902710509)
              ·
                refine ⟨803304654420375713516441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2142145745121001902710509 803304654420375713516441)
                ·
                  refine ⟨602478490815281785137331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 803304654420375713516441 602478490815281785137331)
                  ·
                    refine ⟨903717736222922677705997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 602478490815281785137331 903717736222922677705997)
                    ·
                      refine ⟨338894151083596004139749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 903717736222922677705997 338894151083596004139749)
                      ·
                        rfl

theorem cell23_659994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_659994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_659994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_659994 prefixEnd_659994 := by exact prefixLift 659994
  have htrace : WordTrace (prefixWord ++ tailWord_659994) baseStart_659994 baseEnd_659994 := by
    simpa [prefixWord, tailWord_659994, baseEnd_659994] using wordTrace_append hprefix tailTrace_659994
  have hstable : (prefixWord ++ tailWord_659994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_659994).length < 2 ^ (prefixWord ++ tailWord_659994).sum := by decide
  have hdescent : baseEnd_659994 < baseStart_659994 := by decide
  rcases family_descends (prefixWord ++ tailWord_659994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660097 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 1, 2, 5]
def baseStart_660097 : Nat := 118140960795 + 660097 * 2 ^ 59
def prefixEnd_660097 : Nat := 4983230072969 + 3 ^ 40 * 660097 * 2
def baseEnd_660097 : Nat := 338947039591009101151775

theorem tailTrace_660097 : CollatzResearch.WordTrace tailWord_660097 prefixEnd_660097 338947039591009101151775 := by
  unfold tailWord_660097
  simp only [CollatzResearch.WordTrace]
  refine ⟨24075715489588779437370545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16050476993059186291580363 24075715489588779437370545)
  ·
    refine ⟨18056786617191584578027909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24075715489588779437370545 18056786617191584578027909)
    ·
      refine ⟨3385647490723422108380233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18056786617191584578027909 3385647490723422108380233)
      ·
        refine ⟨2539235618042566581285175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3385647490723422108380233 2539235618042566581285175)
        ·
          refine ⟨3808853427063849871927763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2539235618042566581285175 3808853427063849871927763)
          ·
            refine ⟨5713280140595774807891645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3808853427063849871927763 5713280140595774807891645)
            ·
              refine ⟨2142480052723415552959367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5713280140595774807891645 2142480052723415552959367)
              ·
                refine ⟨3213720079085123329439051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2142480052723415552959367 3213720079085123329439051)
                ·
                  refine ⟨4820580118627684994158577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3213720079085123329439051 4820580118627684994158577)
                  ·
                    refine ⟨3615435088970763745618933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4820580118627684994158577 3615435088970763745618933)
                    ·
                      refine ⟨338947039591009101151775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3615435088970763745618933 338947039591009101151775)
                      ·
                        rfl

theorem cell23_660097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_660097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660097 prefixEnd_660097 := by exact prefixLift 660097
  have htrace : WordTrace (prefixWord ++ tailWord_660097) baseStart_660097 baseEnd_660097 := by
    simpa [prefixWord, tailWord_660097, baseEnd_660097] using wordTrace_append hprefix tailTrace_660097
  have hstable : (prefixWord ++ tailWord_660097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660097).length < 2 ^ (prefixWord ++ tailWord_660097).sum := by decide
  have hdescent : baseEnd_660097 < baseStart_660097 := by decide
  rcases family_descends (prefixWord ++ tailWord_660097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660124 : List Nat := [2, 2, 3, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_660124 : Nat := 118140960795 + 660124 * 2 ^ 59
def prefixEnd_660124 : Nat := 4983230072969 + 3 ^ 40 * 660124 * 2
def baseEnd_660124 : Nat := 338960903568680495514151

theorem tailTrace_660124 : CollatzResearch.WordTrace tailWord_660124 prefixEnd_660124 338960903568680495514151 := by
  unfold tailWord_660124
  simp only [CollatzResearch.WordTrace]
  refine ⟨12038350130245481524301713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16051133506993975365735617 12038350130245481524301713)
  ·
    refine ⟨9028762597684111143226285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12038350130245481524301713 9028762597684111143226285)
    ·
      refine ⟨3385785974131541678709857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9028762597684111143226285 3385785974131541678709857)
      ·
        refine ⟨2539339480598656259032393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3385785974131541678709857 2539339480598656259032393)
        ·
          refine ⟨1904504610448992194274295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2539339480598656259032393 1904504610448992194274295)
          ·
            refine ⟨2856756915673488291411443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1904504610448992194274295 2856756915673488291411443)
            ·
              refine ⟨4285135373510232437117165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2856756915673488291411443 4285135373510232437117165)
              ·
                refine ⟨1606925765066337163918937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4285135373510232437117165 1606925765066337163918937)
                ·
                  refine ⟨1205194323799752872939203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1606925765066337163918937 1205194323799752872939203)
                  ·
                    refine ⟨1807791485699629309408805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1205194323799752872939203 1807791485699629309408805)
                    ·
                      refine ⟨338960903568680495514151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1807791485699629309408805 338960903568680495514151)
                      ·
                        rfl

theorem cell23_660124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_660124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660124 prefixEnd_660124 := by exact prefixLift 660124
  have htrace : WordTrace (prefixWord ++ tailWord_660124) baseStart_660124 baseEnd_660124 := by
    simpa [prefixWord, tailWord_660124, baseEnd_660124] using wordTrace_append hprefix tailTrace_660124
  have hstable : (prefixWord ++ tailWord_660124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660124).length < 2 ^ (prefixWord ++ tailWord_660124).sum := by decide
  have hdescent : baseEnd_660124 < baseStart_660124 := by decide
  rcases family_descends (prefixWord ++ tailWord_660124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660147 : List Nat := [1, 1, 1, 2, 3, 4, 1, 4, 6]
def baseStart_660147 : Nat := 118140960795 + 660147 * 2 ^ 59
def prefixEnd_660147 : Nat := 4983230072969 + 3 ^ 40 * 660147 * 2
def baseEnd_660147 : Nat := 37663634847081545058505

theorem tailTrace_660147 : CollatzResearch.WordTrace tailWord_660147 prefixEnd_660147 37663634847081545058505 := by
  unfold tailWord_660147
  simp only [CollatzResearch.WordTrace]
  refine ⟨24077539139407637976690695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16051692759605091984460463 24077539139407637976690695)
  ·
    refine ⟨36116308709111456965036043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24077539139407637976690695 36116308709111456965036043)
    ·
      refine ⟨54174463063667185447554065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36116308709111456965036043 54174463063667185447554065)
      ·
        refine ⟨40630847297750389085665549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54174463063667185447554065 40630847297750389085665549)
        ·
          refine ⟨15236567736656395907124581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40630847297750389085665549 15236567736656395907124581)
          ·
            refine ⟨2856856450623074232585859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15236567736656395907124581 2856856450623074232585859)
            ·
              refine ⟨4285284675934611348878789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2856856450623074232585859 4285284675934611348878789)
              ·
                refine ⟨803490876737739627914773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4285284675934611348878789 803490876737739627914773)
                ·
                  refine ⟨37663634847081545058505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 803490876737739627914773 37663634847081545058505)
                  ·
                    rfl

theorem cell23_660147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 4, 6].length) (baseStart_660147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660147 prefixEnd_660147 := by exact prefixLift 660147
  have htrace : WordTrace (prefixWord ++ tailWord_660147) baseStart_660147 baseEnd_660147 := by
    simpa [prefixWord, tailWord_660147, baseEnd_660147] using wordTrace_append hprefix tailTrace_660147
  have hstable : (prefixWord ++ tailWord_660147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660147).length < 2 ^ (prefixWord ++ tailWord_660147).sum := by decide
  have hdescent : baseEnd_660147 < baseStart_660147 := by decide
  rcases family_descends (prefixWord ++ tailWord_660147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660164 : List Nat := [2, 3, 3, 1, 1, 2, 2, 3, 6]
def baseStart_660164 : Nat := 118140960795 + 660164 * 2 ^ 59
def prefixEnd_660164 : Nat := 4983230072969 + 3 ^ 40 * 660164 * 2
def baseEnd_660164 : Nat := 37664604754984482112663

theorem tailTrace_660164 : CollatzResearch.WordTrace tailWord_660164 prefixEnd_660164 37664604754984482112663 := by
  unfold tailWord_660164
  simp only [CollatzResearch.WordTrace]
  refine ⟨12039079590173024940029773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16052106120230699920039697 12039079590173024940029773)
  ·
    refine ⟨4514654846314884352511165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12039079590173024940029773 4514654846314884352511165)
    ·
      refine ⟨1692995567368081632191687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4514654846314884352511165 1692995567368081632191687)
      ·
        refine ⟨2539493351052122448287531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1692995567368081632191687 2539493351052122448287531)
        ·
          refine ⟨3809240026578183672431297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2539493351052122448287531 3809240026578183672431297)
          ·
            refine ⟨2856930019933637754323473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3809240026578183672431297 2856930019933637754323473)
            ·
              refine ⟨2142697514950228315742605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2856930019933637754323473 2142697514950228315742605)
              ·
                refine ⟨803511568106335618403477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2142697514950228315742605 803511568106335618403477)
                ·
                  refine ⟨37664604754984482112663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 803511568106335618403477 37664604754984482112663)
                  ·
                    rfl

theorem cell23_660164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 3, 6].length) (baseStart_660164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660164 prefixEnd_660164 := by exact prefixLift 660164
  have htrace : WordTrace (prefixWord ++ tailWord_660164) baseStart_660164 baseEnd_660164 := by
    simpa [prefixWord, tailWord_660164, baseEnd_660164] using wordTrace_append hprefix tailTrace_660164
  have hstable : (prefixWord ++ tailWord_660164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660164).length < 2 ^ (prefixWord ++ tailWord_660164).sum := by decide
  have hdescent : baseEnd_660164 < baseStart_660164 := by decide
  rcases family_descends (prefixWord ++ tailWord_660164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660177 : List Nat := [1, 2, 2, 1, 2, 3, 1, 3, 3, 5]
def baseStart_660177 : Nat := 118140960795 + 660177 * 2 ^ 59
def prefixEnd_660177 : Nat := 4983230072969 + 3 ^ 40 * 660177 * 2
def baseEnd_660177 : Nat := 112996039347789596050469

theorem tailTrace_660177 : CollatzResearch.WordTrace tailWord_660177 prefixEnd_660177 112996039347789596050469 := by
  unfold tailWord_660177
  simp only [CollatzResearch.WordTrace]
  refine ⟨24078633329298953100282785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16052422219532635400188523 24078633329298953100282785)
  ·
    refine ⟨18058974996974214825212089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24078633329298953100282785 18058974996974214825212089)
    ·
      refine ⟨13544231247730661118909067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18058974996974214825212089 13544231247730661118909067)
      ·
        refine ⟨20316346871595991678363601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13544231247730661118909067 20316346871595991678363601)
        ·
          refine ⟨15237260153696993758772701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20316346871595991678363601 15237260153696993758772701)
          ·
            refine ⟨5713972557636372659539763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15237260153696993758772701 5713972557636372659539763)
            ·
              refine ⟨8570958836454558989309645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5713972557636372659539763 8570958836454558989309645)
              ·
                refine ⟨3214109563670459620991117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8570958836454558989309645 3214109563670459620991117)
                ·
                  refine ⟨1205291086376422357871669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3214109563670459620991117 1205291086376422357871669)
                  ·
                    refine ⟨112996039347789596050469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1205291086376422357871669 112996039347789596050469)
                    ·
                      rfl

theorem cell23_660177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 3, 3, 5].length) (baseStart_660177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660177 prefixEnd_660177 := by exact prefixLift 660177
  have htrace : WordTrace (prefixWord ++ tailWord_660177) baseStart_660177 baseEnd_660177 := by
    simpa [prefixWord, tailWord_660177, baseEnd_660177] using wordTrace_append hprefix tailTrace_660177
  have hstable : (prefixWord ++ tailWord_660177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660177).length < 2 ^ (prefixWord ++ tailWord_660177).sum := by decide
  have hdescent : baseEnd_660177 < baseStart_660177 := by decide
  rcases family_descends (prefixWord ++ tailWord_660177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660178 : List Nat := [3, 2, 2, 2, 3, 2, 1, 1, 2, 2, 3]
def baseStart_660178 : Nat := 118140960795 + 660178 * 2 ^ 59
def prefixEnd_660178 : Nat := 4983230072969 + 3 ^ 40 * 660178 * 2
def baseEnd_660178 : Nat := 338988631524023284238903

theorem tailTrace_660178 : CollatzResearch.WordTrace tailWord_660178 prefixEnd_660178 338988631524023284238903 := by
  unfold tailWord_660178
  simp only [CollatzResearch.WordTrace]
  refine ⟨6019667450573832567767297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16052446534863553514046125 6019667450573832567767297)
  ·
    refine ⟨4514750587930374425825473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6019667450573832567767297 4514750587930374425825473)
    ·
      refine ⟨3386062940947780819369105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4514750587930374425825473 3386062940947780819369105)
      ·
        refine ⟨2539547205710835614526829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3386062940947780819369105 2539547205710835614526829)
        ·
          refine ⟨952330202141563355447561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2539547205710835614526829 952330202141563355447561)
          ·
            refine ⟨714247651606172516585671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 952330202141563355447561 714247651606172516585671)
            ·
              refine ⟨1071371477409258774878507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714247651606172516585671 1071371477409258774878507)
              ·
                refine ⟨1607057216113888162317761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1071371477409258774878507 1607057216113888162317761)
                ·
                  refine ⟨1205292912085416121738321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1607057216113888162317761 1205292912085416121738321)
                  ·
                    refine ⟨903969684064062091303741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1205292912085416121738321 903969684064062091303741)
                    ·
                      refine ⟨338988631524023284238903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 903969684064062091303741 338988631524023284238903)
                      ·
                        rfl

theorem cell23_660178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_660178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660178 prefixEnd_660178 := by exact prefixLift 660178
  have htrace : WordTrace (prefixWord ++ tailWord_660178) baseStart_660178 baseEnd_660178 := by
    simpa [prefixWord, tailWord_660178, baseEnd_660178] using wordTrace_append hprefix tailTrace_660178
  have hstable : (prefixWord ++ tailWord_660178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660178).length < 2 ^ (prefixWord ++ tailWord_660178).sum := by decide
  have hdescent : baseEnd_660178 < baseStart_660178 := by decide
  rcases family_descends (prefixWord ++ tailWord_660178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660231 : List Nat := [1, 1, 4, 4, 1, 1, 1, 4, 1, 1, 4]
def baseStart_660231 : Nat := 118140960795 + 660231 * 2 ^ 59
def prefixEnd_660231 : Nat := 4983230072969 + 3 ^ 40 * 660231 * 2
def baseEnd_660231 : Nat := 339015845998711576876159

theorem tailTrace_660231 : CollatzResearch.WordTrace tailWord_660231 prefixEnd_660231 339015845998711576876159 := by
  unfold tailWord_660231
  simp only [CollatzResearch.WordTrace]
  refine ⟨24080602871103320322748547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16053735247402213548499031 24080602871103320322748547)
  ·
    refine ⟨36120904306654980484122821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24080602871103320322748547 36120904306654980484122821)
    ·
      refine ⟨6772669557497808840773029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36120904306654980484122821 6772669557497808840773029)
      ·
        refine ⟨1269875542030839157644943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6772669557497808840773029 1269875542030839157644943)
        ·
          refine ⟨1904813313046258736467415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1269875542030839157644943 1904813313046258736467415)
          ·
            refine ⟨2857219969569388104701123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1904813313046258736467415 2857219969569388104701123)
            ·
              refine ⟨4285829954354082157051685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2857219969569388104701123 4285829954354082157051685)
              ·
                refine ⟨803593116441390404447191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4285829954354082157051685 803593116441390404447191)
                ·
                  refine ⟨1205389674662085606670787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803593116441390404447191 1205389674662085606670787)
                  ·
                    refine ⟨1808084511993128410006181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1205389674662085606670787 1808084511993128410006181)
                    ·
                      refine ⟨339015845998711576876159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1808084511993128410006181 339015845998711576876159)
                      ·
                        rfl

theorem cell23_660231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_660231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660231 prefixEnd_660231 := by exact prefixLift 660231
  have htrace : WordTrace (prefixWord ++ tailWord_660231) baseStart_660231 baseEnd_660231 := by
    simpa [prefixWord, tailWord_660231, baseEnd_660231] using wordTrace_append hprefix tailTrace_660231
  have hstable : (prefixWord ++ tailWord_660231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660231).length < 2 ^ (prefixWord ++ tailWord_660231).sum := by decide
  have hdescent : baseEnd_660231 < baseStart_660231 := by decide
  rcases family_descends (prefixWord ++ tailWord_660231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660285 : List Nat := [1, 4, 1, 4, 2, 2, 1, 2, 1, 2, 3]
def baseStart_660285 : Nat := 118140960795 + 660285 * 2 ^ 59
def prefixEnd_660285 : Nat := 4983230072969 + 3 ^ 40 * 660285 * 2
def baseEnd_660285 : Nat := 339043573954054365600911

theorem tailTrace_660285 : CollatzResearch.WordTrace tailWord_660285 prefixEnd_660285 339043573954054365600911 := by
  unfold tailWord_660285
  simp only [CollatzResearch.WordTrace]
  refine ⟨24082572412907687545214309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16055048275271791696809539 24082572412907687545214309)
  ·
    refine ⟨4515482327420191414727683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24082572412907687545214309 4515482327420191414727683)
    ·
      refine ⟨6773223491130287122091525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4515482327420191414727683 6773223491130287122091525)
      ·
        refine ⟨1269979404586928835392161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6773223491130287122091525 1269979404586928835392161)
        ·
          refine ⟨952484553440196626544121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1269979404586928835392161 952484553440196626544121)
          ·
            refine ⟨714363415080147469908091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 952484553440196626544121 714363415080147469908091)
            ·
              refine ⟨1071545122620221204862137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714363415080147469908091 1071545122620221204862137)
              ·
                refine ⟨803658841965165903646603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1071545122620221204862137 803658841965165903646603)
                ·
                  refine ⟨1205488262947748855469905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803658841965165903646603 1205488262947748855469905)
                  ·
                    refine ⟨904116197210811641602429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1205488262947748855469905 904116197210811641602429)
                    ·
                      refine ⟨339043573954054365600911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 904116197210811641602429 339043573954054365600911)
                      ·
                        rfl

theorem cell23_660285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_660285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660285 prefixEnd_660285 := by exact prefixLift 660285
  have htrace : WordTrace (prefixWord ++ tailWord_660285) baseStart_660285 baseEnd_660285 := by
    simpa [prefixWord, tailWord_660285, baseEnd_660285] using wordTrace_append hprefix tailTrace_660285
  have hstable : (prefixWord ++ tailWord_660285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660285).length < 2 ^ (prefixWord ++ tailWord_660285).sum := by decide
  have hdescent : baseEnd_660285 < baseStart_660285 := by decide
  rcases family_descends (prefixWord ++ tailWord_660285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660291 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 3, 3, 2]
def baseStart_660291 : Nat := 118140960795 + 660291 * 2 ^ 59
def prefixEnd_660291 : Nat := 4983230072969 + 3 ^ 40 * 660291 * 2
def baseEnd_660291 : Nat := 339046654837981342125883

theorem tailTrace_660291 : CollatzResearch.WordTrace tailWord_660291 prefixEnd_660291 339046654837981342125883 := by
  unfold tailWord_660291
  simp only [CollatzResearch.WordTrace]
  refine ⟨24082791250885950569932727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16055194167257300379955151 24082791250885950569932727)
  ·
    refine ⟨36124186876328925854899091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24082791250885950569932727 36124186876328925854899091)
    ·
      refine ⟨54186280314493388782348637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36124186876328925854899091 54186280314493388782348637)
      ·
        refine ⟨20319855117935020793380739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54186280314493388782348637 20319855117935020793380739)
        ·
          refine ⟨30479782676902531190071109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20319855117935020793380739 30479782676902531190071109)
          ·
            refine ⟨5714959251919224598138333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30479782676902531190071109 5714959251919224598138333)
            ·
              refine ⟨2143109719469709224301875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5714959251919224598138333 2143109719469709224301875)
              ·
                refine ⟨3214664579204563836452813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2143109719469709224301875 3214664579204563836452813)
                ·
                  refine ⟨1205499217201711438669805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3214664579204563836452813 1205499217201711438669805)
                  ·
                    refine ⟨452062206450641789501177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1205499217201711438669805 452062206450641789501177)
                    ·
                      refine ⟨339046654837981342125883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 452062206450641789501177 339046654837981342125883)
                      ·
                        rfl

theorem cell23_660291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 3, 3, 2].length) (baseStart_660291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660291 prefixEnd_660291 := by exact prefixLift 660291
  have htrace : WordTrace (prefixWord ++ tailWord_660291) baseStart_660291 baseEnd_660291 := by
    simpa [prefixWord, tailWord_660291, baseEnd_660291] using wordTrace_append hprefix tailTrace_660291
  have hstable : (prefixWord ++ tailWord_660291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660291).length < 2 ^ (prefixWord ++ tailWord_660291).sum := by decide
  have hdescent : baseEnd_660291 < baseStart_660291 := by decide
  rcases family_descends (prefixWord ++ tailWord_660291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660361 : List Nat := [1, 2, 1, 1, 5, 2, 1, 5, 5]
def baseStart_660361 : Nat := 118140960795 + 660361 * 2 ^ 59
def prefixEnd_660361 : Nat := 4983230072969 + 3 ^ 40 * 660361 * 2
def baseEnd_660361 : Nat := 37675844275977340916729

theorem tailTrace_660361 : CollatzResearch.WordTrace tailWord_660361 prefixEnd_660361 37675844275977340916729 := by
  unfold tailWord_660361
  simp only [CollatzResearch.WordTrace]
  refine ⟨24085344360632352524980937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16056896240421568349987291 24085344360632352524980937)
  ·
    refine ⟨18064008270474264393735703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24085344360632352524980937 18064008270474264393735703)
    ·
      refine ⟨27096012405711396590603555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18064008270474264393735703 27096012405711396590603555)
      ·
        refine ⟨40644018608567094885905333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27096012405711396590603555 40644018608567094885905333)
        ·
          refine ⟨3810376744553165145553625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40644018608567094885905333 3810376744553165145553625)
          ·
            refine ⟨2857782558414873859165219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3810376744553165145553625 2857782558414873859165219)
            ·
              refine ⟨4286673837622310788747829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2857782558414873859165219 4286673837622310788747829)
              ·
                refine ⟨401875672277091636445109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4286673837622310788747829 401875672277091636445109)
                ·
                  refine ⟨37675844275977340916729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 401875672277091636445109 37675844275977340916729)
                  ·
                    rfl

theorem cell23_660361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 5].length) (baseStart_660361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660361 prefixEnd_660361 := by exact prefixLift 660361
  have htrace : WordTrace (prefixWord ++ tailWord_660361) baseStart_660361 baseEnd_660361 := by
    simpa [prefixWord, tailWord_660361, baseEnd_660361] using wordTrace_append hprefix tailTrace_660361
  have hstable : (prefixWord ++ tailWord_660361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660361).length < 2 ^ (prefixWord ++ tailWord_660361).sum := by decide
  have hdescent : baseEnd_660361 < baseStart_660361 := by decide
  rcases family_descends (prefixWord ++ tailWord_660361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660384 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 5]
def baseStart_660384 : Nat := 118140960795 + 660384 * 2 ^ 59
def prefixEnd_660384 : Nat := 4983230072969 + 3 ^ 40 * 660384 * 2
def baseEnd_660384 : Nat := 339094408538849478262955

theorem tailTrace_660384 : CollatzResearch.WordTrace tailWord_660384 prefixEnd_660384 339094408538849478262955 := by
  unfold tailWord_660384
  simp only [CollatzResearch.WordTrace]
  refine ⟨12043091619774513726534103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16057455493032684968712137 12043091619774513726534103)
  ·
    refine ⟨18064637429661770589801155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12043091619774513726534103 18064637429661770589801155)
    ·
      refine ⟨27096956144492655884701733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18064637429661770589801155 27096956144492655884701733)
      ·
        refine ⟨5080679277092372978381575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27096956144492655884701733 5080679277092372978381575)
        ·
          refine ⟨7621018915638559467572363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5080679277092372978381575 7621018915638559467572363)
          ·
            refine ⟨11431528373457839201358545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7621018915638559467572363 11431528373457839201358545)
            ·
              refine ⟨8573646280093379401018909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11431528373457839201358545 8573646280093379401018909)
              ·
                refine ⟨3215117355035017275382091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8573646280093379401018909 3215117355035017275382091)
                ·
                  refine ⟨4822676032552525913073137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3215117355035017275382091 4822676032552525913073137)
                  ·
                    refine ⟨3617007024414394434804853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4822676032552525913073137 3617007024414394434804853)
                    ·
                      refine ⟨339094408538849478262955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3617007024414394434804853 339094408538849478262955)
                      ·
                        rfl

theorem cell23_660384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_660384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660384 prefixEnd_660384 := by exact prefixLift 660384
  have htrace : WordTrace (prefixWord ++ tailWord_660384) baseStart_660384 baseEnd_660384 := by
    simpa [prefixWord, tailWord_660384, baseEnd_660384] using wordTrace_append hprefix tailTrace_660384
  have hstable : (prefixWord ++ tailWord_660384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660384).length < 2 ^ (prefixWord ++ tailWord_660384).sum := by decide
  have hdescent : baseEnd_660384 < baseStart_660384 := by decide
  rcases family_descends (prefixWord ++ tailWord_660384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660429 : List Nat := [1, 6, 3, 1, 2, 1, 1, 1, 7]
def baseStart_660429 : Nat := 118140960795 + 660429 * 2 ^ 59
def prefixEnd_660429 : Nat := 4983230072969 + 3 ^ 40 * 660429 * 2
def baseEnd_660429 : Nat := 37679723907589089133361

theorem tailTrace_660429 : CollatzResearch.WordTrace tailWord_660429 prefixEnd_660429 37679723907589089133361 := by
  unfold tailWord_660429
  simp only [CollatzResearch.WordTrace]
  refine ⟨24087824524386000138456341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16058549682924000092304227 24087824524386000138456341)
  ·
    refine ⟨1129116774580593756490141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 24087824524386000138456341 1129116774580593756490141)
    ·
      refine ⟨423418790467722658683803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1129116774580593756490141 423418790467722658683803)
      ·
        refine ⟨635128185701583988025705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423418790467722658683803 635128185701583988025705)
        ·
          refine ⟨476346139276187991019279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 635128185701583988025705 476346139276187991019279)
          ·
            refine ⟨714519208914281986528919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476346139276187991019279 714519208914281986528919)
            ·
              refine ⟨1071778813371422979793379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714519208914281986528919 1071778813371422979793379)
              ·
                refine ⟨1607668220057134469690069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1071778813371422979793379 1607668220057134469690069)
                ·
                  refine ⟨37679723907589089133361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1607668220057134469690069 37679723907589089133361)
                  ·
                    rfl

theorem cell23_660429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_660429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660429 prefixEnd_660429 := by exact prefixLift 660429
  have htrace : WordTrace (prefixWord ++ tailWord_660429) baseStart_660429 baseEnd_660429 := by
    simpa [prefixWord, tailWord_660429, baseEnd_660429] using wordTrace_append hprefix tailTrace_660429
  have hstable : (prefixWord ++ tailWord_660429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660429).length < 2 ^ (prefixWord ++ tailWord_660429).sum := by decide
  have hdescent : baseEnd_660429 < baseStart_660429 := by decide
  rcases family_descends (prefixWord ++ tailWord_660429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660431 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 3]
def baseStart_660431 : Nat := 118140960795 + 660431 * 2 ^ 59
def prefixEnd_660431 : Nat := 4983230072969 + 3 ^ 40 * 660431 * 2
def baseEnd_660431 : Nat := 339118542129610794375239

theorem tailTrace_660431 : CollatzResearch.WordTrace tailWord_660431 prefixEnd_660431 339118542129610794375239 := by
  unfold tailWord_660431
  simp only [CollatzResearch.WordTrace]
  refine ⟨24087897470378754480029147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16058598313585836320019431 24087897470378754480029147)
  ·
    refine ⟨36131846205568131720043721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24087897470378754480029147 36131846205568131720043721)
    ·
      refine ⟨27098884654176098790032791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36131846205568131720043721 27098884654176098790032791)
      ·
        refine ⟨40648326981264148185049187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27098884654176098790032791 40648326981264148185049187)
        ·
          refine ⟨60972490471896222277573781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40648326981264148185049187 60972490471896222277573781)
          ·
            refine ⟨2858085490870135419261271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60972490471896222277573781 2858085490870135419261271)
            ·
              refine ⟨4287128236305203128891907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2858085490870135419261271 4287128236305203128891907)
              ·
                refine ⟨6430692354457804693337861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4287128236305203128891907 6430692354457804693337861)
                ·
                  refine ⟨1205754816460838380000849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6430692354457804693337861 1205754816460838380000849)
                  ·
                    refine ⟨904316112345628785000637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1205754816460838380000849 904316112345628785000637)
                    ·
                      refine ⟨339118542129610794375239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 904316112345628785000637 339118542129610794375239)
                      ·
                        rfl

theorem cell23_660431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 4, 2, 3].length) (baseStart_660431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660431 prefixEnd_660431 := by exact prefixLift 660431
  have htrace : WordTrace (prefixWord ++ tailWord_660431) baseStart_660431 baseEnd_660431 := by
    simpa [prefixWord, tailWord_660431, baseEnd_660431] using wordTrace_append hprefix tailTrace_660431
  have hstable : (prefixWord ++ tailWord_660431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660431).length < 2 ^ (prefixWord ++ tailWord_660431).sum := by decide
  have hdescent : baseEnd_660431 < baseStart_660431 := by decide
  rcases family_descends (prefixWord ++ tailWord_660431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660451 : List Nat := [1, 1, 1, 6, 1, 1, 3, 3, 6]
def baseStart_660451 : Nat := 118140960795 + 660451 * 2 ^ 59
def prefixEnd_660451 : Nat := 4983230072969 + 3 ^ 40 * 660451 * 2
def baseEnd_660451 : Nat := 37680979082522301791683

theorem tailTrace_660451 : CollatzResearch.WordTrace tailWord_660451 prefixEnd_660451 37680979082522301791683 := by
  unfold tailWord_660451
  simp only [CollatzResearch.WordTrace]
  refine ⟨24088626930306297895757207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16059084620204198597171471 24088626930306297895757207)
  ·
    refine ⟨36132940395459446843635811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24088626930306297895757207 36132940395459446843635811)
    ·
      refine ⟨54199410593189170265453717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36132940395459446843635811 54199410593189170265453717)
      ·
        refine ⟨2540597371555742356193143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54199410593189170265453717 2540597371555742356193143)
        ·
          refine ⟨3810896057333613534289715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2540597371555742356193143 3810896057333613534289715)
          ·
            refine ⟨5716344086000420301434573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3810896057333613534289715 5716344086000420301434573)
            ·
              refine ⟨2143629032250157613037965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5716344086000420301434573 2143629032250157613037965)
              ·
                refine ⟨803860887093809104889237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2143629032250157613037965 803860887093809104889237)
                ·
                  refine ⟨37680979082522301791683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 803860887093809104889237 37680979082522301791683)
                  ·
                    rfl

theorem cell23_660451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 6].length) (baseStart_660451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660451 prefixEnd_660451 := by exact prefixLift 660451
  have htrace : WordTrace (prefixWord ++ tailWord_660451) baseStart_660451 baseEnd_660451 := by
    simpa [prefixWord, tailWord_660451, baseEnd_660451] using wordTrace_append hprefix tailTrace_660451
  have hstable : (prefixWord ++ tailWord_660451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660451).length < 2 ^ (prefixWord ++ tailWord_660451).sum := by decide
  have hdescent : baseEnd_660451 < baseStart_660451 := by decide
  rcases family_descends (prefixWord ++ tailWord_660451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660474 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7]
def baseStart_660474 : Nat := 118140960795 + 660474 * 2 ^ 59
def prefixEnd_660474 : Nat := 4983230072969 + 3 ^ 40 * 660474 * 2
def baseEnd_660474 : Nat := 339140621797754126137541

theorem tailTrace_660474 : CollatzResearch.WordTrace tailWord_660474 prefixEnd_660474 339140621797754126137541 := by
  unfold tailWord_660474
  simp only [CollatzResearch.WordTrace]
  refine ⟨6022366452305743205961119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16059643872815315215896317 6022366452305743205961119)
  ·
    refine ⟨9033549678458614808941679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6022366452305743205961119 9033549678458614808941679)
    ·
      refine ⟨13550324517687922213412519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9033549678458614808941679 13550324517687922213412519)
      ·
        refine ⟨20325486776531883320118779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13550324517687922213412519 20325486776531883320118779)
        ·
          refine ⟨30488230164797824980178169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20325486776531883320118779 30488230164797824980178169)
          ·
            refine ⟨22866172623598368735133627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30488230164797824980178169 22866172623598368735133627)
            ·
              refine ⟨34299258935397553102700441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22866172623598368735133627 34299258935397553102700441)
              ·
                refine ⟨25724444201548164827025331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34299258935397553102700441 25724444201548164827025331)
                ·
                  refine ⟨38586666302322247240537997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25724444201548164827025331 38586666302322247240537997)
                  ·
                    refine ⟨14469999863370842715201749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38586666302322247240537997 14469999863370842715201749)
                    ·
                      refine ⟨339140621797754126137541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14469999863370842715201749 339140621797754126137541)
                      ·
                        rfl

theorem cell23_660474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_660474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660474 prefixEnd_660474 := by exact prefixLift 660474
  have htrace : WordTrace (prefixWord ++ tailWord_660474) baseStart_660474 baseEnd_660474 := by
    simpa [prefixWord, tailWord_660474, baseEnd_660474] using wordTrace_append hprefix tailTrace_660474
  have hstable : (prefixWord ++ tailWord_660474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660474).length < 2 ^ (prefixWord ++ tailWord_660474).sum := by decide
  have hdescent : baseEnd_660474 < baseStart_660474 := by decide
  rcases family_descends (prefixWord ++ tailWord_660474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660511 : List Nat := [1, 1, 2, 4, 1, 3, 1, 3, 1, 6]
def baseStart_660511 : Nat := 118140960795 + 660511 * 2 ^ 59
def prefixEnd_660511 : Nat := 4983230072969 + 3 ^ 40 * 660511 * 2
def baseEnd_660511 : Nat := 113053206860656827124957

theorem tailTrace_660511 : CollatzResearch.WordTrace tailWord_660511 prefixEnd_660511 113053206860656827124957 := by
  unfold tailWord_660511
  simp only [CollatzResearch.WordTrace]
  refine ⟨24090815310088928142941387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16060543540059285428627591 24090815310088928142941387)
  ·
    refine ⟨36136222965133392214412081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24090815310088928142941387 36136222965133392214412081)
    ·
      refine ⟨27102167223850044160809061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36136222965133392214412081 27102167223850044160809061)
      ·
        refine ⟨5081656354471883280151699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27102167223850044160809061 5081656354471883280151699)
        ·
          refine ⟨7622484531707824920227549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5081656354471883280151699 7622484531707824920227549)
          ·
            refine ⟨2858431699390434345085331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7622484531707824920227549 2858431699390434345085331)
            ·
              refine ⟨4287647549085651517627997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2858431699390434345085331 4287647549085651517627997)
              ·
                refine ⟨1607867830907119319110499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4287647549085651517627997 1607867830907119319110499)
                ·
                  refine ⟨2411801746360678978665749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1607867830907119319110499 2411801746360678978665749)
                  ·
                    refine ⟨113053206860656827124957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2411801746360678978665749 113053206860656827124957)
                    ·
                      rfl

theorem cell23_660511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 1, 6].length) (baseStart_660511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660511 prefixEnd_660511 := by exact prefixLift 660511
  have htrace : WordTrace (prefixWord ++ tailWord_660511) baseStart_660511 baseEnd_660511 := by
    simpa [prefixWord, tailWord_660511, baseEnd_660511] using wordTrace_append hprefix tailTrace_660511
  have hstable : (prefixWord ++ tailWord_660511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660511).length < 2 ^ (prefixWord ++ tailWord_660511).sum := by decide
  have hdescent : baseEnd_660511 < baseStart_660511 := by decide
  rcases family_descends (prefixWord ++ tailWord_660511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660512 : List Nat := [2, 1, 1, 7, 1, 1, 1, 2, 3, 1, 3]
def baseStart_660512 : Nat := 118140960795 + 660512 * 2 ^ 59
def prefixEnd_660512 : Nat := 4983230072969 + 3 ^ 40 * 660512 * 2
def baseEnd_660512 : Nat := 339160134062624977462367

theorem tailTrace_660512 : CollatzResearch.WordTrace tailWord_660512 prefixEnd_660512 339160134062624977462367 := by
  unfold tailWord_660512
  simp only [CollatzResearch.WordTrace]
  refine ⟨12045425891542652656863895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16060567855390203542485193 12045425891542652656863895)
  ·
    refine ⟨18068138837313978985295843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12045425891542652656863895 18068138837313978985295843)
    ·
      refine ⟨27102208255970968477943765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18068138837313978985295843 27102208255970968477943765)
      ·
        refine ⟨635208005999319573701807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 27102208255970968477943765 635208005999319573701807)
        ·
          refine ⟨952812008998979360552711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635208005999319573701807 952812008998979360552711)
          ·
            refine ⟨1429218013498469040829067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952812008998979360552711 1429218013498469040829067)
            ·
              refine ⟨2143827020247703561243601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1429218013498469040829067 2143827020247703561243601)
              ·
                refine ⟨1607870265185777670932701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2143827020247703561243601 1607870265185777670932701)
                ·
                  refine ⟨602951349444666626599763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1607870265185777670932701 602951349444666626599763)
                  ·
                    refine ⟨904427024166999939899645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 602951349444666626599763 904427024166999939899645)
                    ·
                      refine ⟨339160134062624977462367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 904427024166999939899645 339160134062624977462367)
                      ·
                        rfl

theorem cell23_660512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_660512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660512 prefixEnd_660512 := by exact prefixLift 660512
  have htrace : WordTrace (prefixWord ++ tailWord_660512) baseStart_660512 baseEnd_660512 := by
    simpa [prefixWord, tailWord_660512, baseEnd_660512] using wordTrace_append hprefix tailTrace_660512
  have hstable : (prefixWord ++ tailWord_660512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660512).length < 2 ^ (prefixWord ++ tailWord_660512).sum := by decide
  have hdescent : baseEnd_660512 < baseStart_660512 := by decide
  rcases family_descends (prefixWord ++ tailWord_660512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660532 : List Nat := [2, 5, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_660532 : Nat := 118140960795 + 660532 * 2 ^ 59
def prefixEnd_660532 : Nat := 4983230072969 + 3 ^ 40 * 660532 * 2
def baseEnd_660532 : Nat := 113056801225238299737425

theorem tailTrace_660532 : CollatzResearch.WordTrace tailWord_660532 prefixEnd_660532 113056801225238299737425 := by
  unfold tailWord_660532
  simp only [CollatzResearch.WordTrace]
  refine ⟨12045790621506424364727925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16061054162008565819637233 12045790621506424364727925)
  ·
    refine ⟨1129292870766227284193243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12045790621506424364727925 1129292870766227284193243)
    ·
      refine ⟨1693939306149340926289865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1129292870766227284193243 1693939306149340926289865)
      ·
        refine ⟨1270454479612005694717399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1693939306149340926289865 1270454479612005694717399)
        ·
          refine ⟨1905681719418008542076099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1270454479612005694717399 1905681719418008542076099)
          ·
            refine ⟨2858522579127012813114149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1905681719418008542076099 2858522579127012813114149)
            ·
              refine ⟨535972983586314902458903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2858522579127012813114149 535972983586314902458903)
              ·
                refine ⟨803959475379472353688355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535972983586314902458903 803959475379472353688355)
                ·
                  refine ⟨1205939213069208530532533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 803959475379472353688355 1205939213069208530532533)
                  ·
                    refine ⟨113056801225238299737425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1205939213069208530532533 113056801225238299737425)
                    ·
                      rfl

theorem cell23_660532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_660532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660532 prefixEnd_660532 := by exact prefixLift 660532
  have htrace : WordTrace (prefixWord ++ tailWord_660532) baseStart_660532 baseEnd_660532 := by
    simpa [prefixWord, tailWord_660532, baseEnd_660532] using wordTrace_append hprefix tailTrace_660532
  have hstable : (prefixWord ++ tailWord_660532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660532).length < 2 ^ (prefixWord ++ tailWord_660532).sum := by decide
  have hdescent : baseEnd_660532 < baseStart_660532 := by decide
  rcases family_descends (prefixWord ++ tailWord_660532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660541 : List Nat := [1, 4, 1, 3, 1, 3, 10]
def baseStart_660541 : Nat := 118140960795 + 660541 * 2 ^ 59
def prefixEnd_660541 : Nat := 4983230072969 + 3 ^ 40 * 660541 * 2
def baseEnd_660541 : Nat := 4187345987674140296293

theorem tailTrace_660541 : CollatzResearch.WordTrace tailWord_660541 prefixEnd_660541 4187345987674140296293 := by
  unfold tailWord_660541
  simp only [CollatzResearch.WordTrace]
  refine ⟨24091909499980243266533477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16061272999986828844355651 24091909499980243266533477)
  ·
    refine ⟨4517233031246295612475027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24091909499980243266533477 4517233031246295612475027)
    ·
      refine ⟨6775849546869443418712541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4517233031246295612475027 6775849546869443418712541)
      ·
        refine ⟨2540943580076041282017203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6775849546869443418712541 2540943580076041282017203)
        ·
          refine ⟨3811415370114061923025805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2540943580076041282017203 3811415370114061923025805)
          ·
            refine ⟨1429280763792773221134677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3811415370114061923025805 1429280763792773221134677)
            ·
              refine ⟨4187345987674140296293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1429280763792773221134677 4187345987674140296293)
              ·
                rfl

theorem cell23_660541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 10].length) (baseStart_660541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660541 prefixEnd_660541 := by exact prefixLift 660541
  have htrace : WordTrace (prefixWord ++ tailWord_660541) baseStart_660541 baseEnd_660541 := by
    simpa [prefixWord, tailWord_660541, baseEnd_660541] using wordTrace_append hprefix tailTrace_660541
  have hstable : (prefixWord ++ tailWord_660541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660541).length < 2 ^ (prefixWord ++ tailWord_660541).sum := by decide
  have hdescent : baseEnd_660541 < baseStart_660541 := by decide
  rcases family_descends (prefixWord ++ tailWord_660541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660545 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 4, 4]
def baseStart_660545 : Nat := 118140960795 + 660545 * 2 ^ 59
def prefixEnd_660545 : Nat := 4983230072969 + 3 ^ 40 * 660545 * 2
def baseEnd_660545 : Nat := 113059026308074449449905

theorem tailTrace_660545 : CollatzResearch.WordTrace tailWord_660545 prefixEnd_660545 113059026308074449449905 := by
  unfold tailWord_660545
  simp only [CollatzResearch.WordTrace]
  refine ⟨24092055391965751949679089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16061370261310501299786059 24092055391965751949679089)
  ·
    refine ⟨18069041543974313962259317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24092055391965751949679089 18069041543974313962259317)
    ·
      refine ⟨1693972644747591933961811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18069041543974313962259317 1693972644747591933961811)
      ·
        refine ⟨2540958967121387900942717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1693972644747591933961811 2540958967121387900942717)
        ·
          refine ⟨952859612670520462853519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2540958967121387900942717 952859612670520462853519)
          ·
            refine ⟨1429289419005780694280279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952859612670520462853519 1429289419005780694280279)
            ·
              refine ⟨2143934128508671041420419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1429289419005780694280279 2143934128508671041420419)
              ·
                refine ⟨3215901192763006562130629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2143934128508671041420419 3215901192763006562130629)
                ·
                  refine ⟨602981473643063730399493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3215901192763006562130629 602981473643063730399493)
                  ·
                    refine ⟨113059026308074449449905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 602981473643063730399493 113059026308074449449905)
                    ·
                      rfl

theorem cell23_660545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_660545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660545 prefixEnd_660545 := by exact prefixLift 660545
  have htrace : WordTrace (prefixWord ++ tailWord_660545) baseStart_660545 baseEnd_660545 := by
    simpa [prefixWord, tailWord_660545, baseEnd_660545] using wordTrace_append hprefix tailTrace_660545
  have hstable : (prefixWord ++ tailWord_660545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660545).length < 2 ^ (prefixWord ++ tailWord_660545).sum := by decide
  have hdescent : baseEnd_660545 < baseStart_660545 := by decide
  rcases family_descends (prefixWord ++ tailWord_660545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660552 : List Nat := [2, 1, 3, 1, 1, 1, 3, 6, 1, 2, 2]
def baseStart_660552 : Nat := 118140960795 + 660552 * 2 ^ 59
def prefixEnd_660552 : Nat := 4983230072969 + 3 ^ 40 * 660552 * 2
def baseEnd_660552 : Nat := 339180673288804820962183

theorem tailTrace_660552 : CollatzResearch.WordTrace tailWord_660552 prefixEnd_660552 339180673288804820962183 := by
  unfold tailWord_660552
  simp only [CollatzResearch.WordTrace]
  refine ⟨12046155351470196072591955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16061540468626928096789273 12046155351470196072591955)
  ·
    refine ⟨18069233027205294108887933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12046155351470196072591955 18069233027205294108887933)
    ·
      refine ⟨6775962385201985290832975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18069233027205294108887933 6775962385201985290832975)
      ·
        refine ⟨10163943577802977936249463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6775962385201985290832975 10163943577802977936249463)
        ·
          refine ⟨15245915366704466904374195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10163943577802977936249463 15245915366704466904374195)
          ·
            refine ⟨22868873050056700356561293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15245915366704466904374195 22868873050056700356561293)
            ·
              refine ⟨8575827393771262633710485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22868873050056700356561293 8575827393771262633710485)
              ·
                refine ⟨401991909083027935955179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8575827393771262633710485 401991909083027935955179)
                ·
                  refine ⟨602987863624541903932769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 401991909083027935955179 602987863624541903932769)
                  ·
                    refine ⟨452240897718406427949577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 602987863624541903932769 452240897718406427949577)
                    ·
                      refine ⟨339180673288804820962183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 452240897718406427949577 339180673288804820962183)
                      ·
                        rfl

theorem cell23_660552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 1, 2, 2].length) (baseStart_660552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660552 prefixEnd_660552 := by exact prefixLift 660552
  have htrace : WordTrace (prefixWord ++ tailWord_660552) baseStart_660552 baseEnd_660552 := by
    simpa [prefixWord, tailWord_660552, baseEnd_660552] using wordTrace_append hprefix tailTrace_660552
  have hstable : (prefixWord ++ tailWord_660552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660552).length < 2 ^ (prefixWord ++ tailWord_660552).sum := by decide
  have hdescent : baseEnd_660552 < baseStart_660552 := by decide
  rcases family_descends (prefixWord ++ tailWord_660552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660562 : List Nat := [3, 2, 2, 1, 3, 2, 3, 1, 2, 4]
def baseStart_660562 : Nat := 118140960795 + 660562 * 2 ^ 59
def prefixEnd_660562 : Nat := 4983230072969 + 3 ^ 40 * 660562 * 2
def baseEnd_660562 : Nat := 113061936031783260612379

theorem tailTrace_660562 : CollatzResearch.WordTrace tailWord_660562 prefixEnd_660562 113061936031783260612379 := by
  unfold tailWord_660562
  simp only [CollatzResearch.WordTrace]
  refine ⟨6023168858226040963261985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16061783621936109235365293 6023168858226040963261985)
  ·
    refine ⟨4517376643669530722446489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6023168858226040963261985 4517376643669530722446489)
    ·
      refine ⟨3388032482752148041834867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4517376643669530722446489 3388032482752148041834867)
      ·
        refine ⟨5082048724128222062752301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3388032482752148041834867 5082048724128222062752301)
        ·
          refine ⟨1905768271548083273532113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5082048724128222062752301 1905768271548083273532113)
          ·
            refine ⟨1429326203661062455149085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1905768271548083273532113 1429326203661062455149085)
            ·
              refine ⟨535997326372898420680907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1429326203661062455149085 535997326372898420680907)
              ·
                refine ⟨803995989559347631021361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535997326372898420680907 803995989559347631021361)
                ·
                  refine ⟨602996992169510723266021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 803995989559347631021361 602996992169510723266021)
                  ·
                    refine ⟨113061936031783260612379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 602996992169510723266021 113061936031783260612379)
                    ·
                      rfl

theorem cell23_660562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_660562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660562 prefixEnd_660562 := by exact prefixLift 660562
  have htrace : WordTrace (prefixWord ++ tailWord_660562) baseStart_660562 baseEnd_660562 := by
    simpa [prefixWord, tailWord_660562, baseEnd_660562] using wordTrace_append hprefix tailTrace_660562
  have hstable : (prefixWord ++ tailWord_660562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660562).length < 2 ^ (prefixWord ++ tailWord_660562).sum := by decide
  have hdescent : baseEnd_660562 < baseStart_660562 := by decide
  rcases family_descends (prefixWord ++ tailWord_660562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660581 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 1, 4, 5]
def baseStart_660581 : Nat := 118140960795 + 660581 * 2 ^ 59
def prefixEnd_660581 : Nat := 4983230072969 + 3 ^ 40 * 660581 * 2
def baseEnd_660581 : Nat := 339195564227785207499549

theorem tailTrace_660581 : CollatzResearch.WordTrace tailWord_660581 prefixEnd_660581 339195564227785207499549 := by
  unfold tailWord_660581
  simp only [CollatzResearch.WordTrace]
  refine ⟨24093368419835330097989597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16062245613223553398659731 24093368419835330097989597)
  ·
    refine ⟨9035013157438248786746099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24093368419835330097989597 9035013157438248786746099)
    ·
      refine ⟨13552519736157373180119149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9035013157438248786746099 13552519736157373180119149)
      ·
        refine ⟨5082194901059014942544681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13552519736157373180119149 5082194901059014942544681)
        ·
          refine ⟨3811646175794261206908511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5082194901059014942544681 3811646175794261206908511)
          ·
            refine ⟨5717469263691391810362767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3811646175794261206908511 5717469263691391810362767)
            ·
              refine ⟨8576203895537087715544151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5717469263691391810362767 8576203895537087715544151)
              ·
                refine ⟨12864305843305631573316227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8576203895537087715544151 12864305843305631573316227)
                ·
                  refine ⟨19296458764958447359974341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12864305843305631573316227 19296458764958447359974341)
                  ·
                    refine ⟨3618086018429708879995189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19296458764958447359974341 3618086018429708879995189)
                    ·
                      refine ⟨339195564227785207499549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3618086018429708879995189 339195564227785207499549)
                      ·
                        rfl

theorem cell23_660581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_660581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660581 prefixEnd_660581 := by exact prefixLift 660581
  have htrace : WordTrace (prefixWord ++ tailWord_660581) baseStart_660581 baseEnd_660581 := by
    simpa [prefixWord, tailWord_660581, baseEnd_660581] using wordTrace_append hprefix tailTrace_660581
  have hstable : (prefixWord ++ tailWord_660581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660581).length < 2 ^ (prefixWord ++ tailWord_660581).sum := by decide
  have hdescent : baseEnd_660581 < baseStart_660581 := by decide
  rcases family_descends (prefixWord ++ tailWord_660581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660586 : List Nat := [3, 1, 3, 2, 2, 3, 1, 3, 1, 2, 2]
def baseStart_660586 : Nat := 118140960795 + 660586 * 2 ^ 59
def prefixEnd_660586 : Nat := 4983230072969 + 3 ^ 40 * 660586 * 2
def baseEnd_660586 : Nat := 339198131631057687937027

theorem tailTrace_660586 : CollatzResearch.WordTrace tailWord_660586 prefixEnd_660586 339198131631057687937027 := by
  unfold tailWord_660586
  simp only [CollatzResearch.WordTrace]
  refine ⟨6023387696204303987980403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16062367189878143967947741 6023387696204303987980403)
  ·
    refine ⟨9035081544306455981970605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6023387696204303987980403 9035081544306455981970605)
    ·
      refine ⟨3388155579114920993238977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9035081544306455981970605 3388155579114920993238977)
      ·
        refine ⟨2541116684336190744929233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3388155579114920993238977 2541116684336190744929233)
        ·
          refine ⟨1905837513252143058696925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2541116684336190744929233 1905837513252143058696925)
          ·
            refine ⟨714689067469553647011347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1905837513252143058696925 714689067469553647011347)
            ·
              refine ⟨1072033601204330470517021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 714689067469553647011347 1072033601204330470517021)
              ·
                refine ⟨402012600451623926443883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1072033601204330470517021 402012600451623926443883)
                ·
                  refine ⟨603018900677435889665825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 402012600451623926443883 603018900677435889665825)
                  ·
                    refine ⟨452264175508076917249369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 603018900677435889665825 452264175508076917249369)
                    ·
                      refine ⟨339198131631057687937027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 452264175508076917249369 339198131631057687937027)
                      ·
                        rfl

theorem cell23_660586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_660586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660586 prefixEnd_660586 := by exact prefixLift 660586
  have htrace : WordTrace (prefixWord ++ tailWord_660586) baseStart_660586 baseEnd_660586 := by
    simpa [prefixWord, tailWord_660586, baseEnd_660586] using wordTrace_append hprefix tailTrace_660586
  have hstable : (prefixWord ++ tailWord_660586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660586).length < 2 ^ (prefixWord ++ tailWord_660586).sum := by decide
  have hdescent : baseEnd_660586 < baseStart_660586 := by decide
  rcases family_descends (prefixWord ++ tailWord_660586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660598 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_660598 : Nat := 118140960795 + 660598 * 2 ^ 59
def prefixEnd_660598 : Nat := 4983230072969 + 3 ^ 40 * 660598 * 2
def baseEnd_660598 : Nat := 339204293398911640986971

theorem tailTrace_660598 : CollatzResearch.WordTrace tailWord_660598 prefixEnd_660598 339204293398911640986971 := by
  unfold tailWord_660598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1505874278798358875084903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16062658973849161334238965 1505874278798358875084903)
  ·
    refine ⟨2258811418197538312627355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1505874278798358875084903 2258811418197538312627355)
    ·
      refine ⟨3388217127296307468941033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2258811418197538312627355 3388217127296307468941033)
      ·
        refine ⟨2541162845472230601705775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3388217127296307468941033 2541162845472230601705775)
        ·
          refine ⟨3811744268208345902558663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2541162845472230601705775 3811744268208345902558663)
          ·
            refine ⟨5717616402312518853837995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3811744268208345902558663 5717616402312518853837995)
            ·
              refine ⟨8576424603468778280756993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5717616402312518853837995 8576424603468778280756993)
              ·
                refine ⟨6432318452601583710567745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8576424603468778280756993 6432318452601583710567745)
                ·
                  refine ⟨4824238839451187782925809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6432318452601583710567745 4824238839451187782925809)
                  ·
                    refine ⟨3618179129588390837194357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4824238839451187782925809 3618179129588390837194357)
                    ·
                      refine ⟨339204293398911640986971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3618179129588390837194357 339204293398911640986971)
                      ·
                        rfl

theorem cell23_660598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_660598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660598 prefixEnd_660598 := by exact prefixLift 660598
  have htrace : WordTrace (prefixWord ++ tailWord_660598) baseStart_660598 baseEnd_660598 := by
    simpa [prefixWord, tailWord_660598, baseEnd_660598] using wordTrace_append hprefix tailTrace_660598
  have hstable : (prefixWord ++ tailWord_660598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660598).length < 2 ^ (prefixWord ++ tailWord_660598).sum := by decide
  have hdescent : baseEnd_660598 < baseStart_660598 := by decide
  rcases family_descends (prefixWord ++ tailWord_660598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660611 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 5]
def baseStart_660611 : Nat := 118140960795 + 660611 * 2 ^ 59
def prefixEnd_660611 : Nat := 4983230072969 + 3 ^ 40 * 660611 * 2
def baseEnd_660611 : Nat := 339210968647420090124411

theorem tailTrace_660611 : CollatzResearch.WordTrace tailWord_660611 prefixEnd_660611 339210968647420090124411 := by
  unfold tailWord_660611
  simp only [CollatzResearch.WordTrace]
  refine ⟨24094462609726645221581687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16062975073151096814387791 24094462609726645221581687)
  ·
    refine ⟨36141693914589967832372531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24094462609726645221581687 36141693914589967832372531)
    ·
      refine ⟨54212540871884951748558797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36141693914589967832372531 54212540871884951748558797)
      ·
        refine ⟨20329702826956856905709549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54212540871884951748558797 20329702826956856905709549)
        ·
          refine ⟨7623638560108821339641081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20329702826956856905709549 7623638560108821339641081)
          ·
            refine ⟨5717728920081616004730811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7623638560108821339641081 5717728920081616004730811)
            ·
              refine ⟨8576593380122424007096217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5717728920081616004730811 8576593380122424007096217)
              ·
                refine ⟨6432445035091818005322163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8576593380122424007096217 6432445035091818005322163)
                ·
                  refine ⟨9648667552637727007983245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6432445035091818005322163 9648667552637727007983245)
                  ·
                    refine ⟨3618250332239147627993717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9648667552637727007983245 3618250332239147627993717)
                    ·
                      refine ⟨339210968647420090124411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3618250332239147627993717 339210968647420090124411)
                      ·
                        rfl

theorem cell23_660611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_660611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660611 prefixEnd_660611 := by exact prefixLift 660611
  have htrace : WordTrace (prefixWord ++ tailWord_660611) baseStart_660611 baseEnd_660611 := by
    simpa [prefixWord, tailWord_660611, baseEnd_660611] using wordTrace_append hprefix tailTrace_660611
  have hstable : (prefixWord ++ tailWord_660611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660611).length < 2 ^ (prefixWord ++ tailWord_660611).sum := by decide
  have hdescent : baseEnd_660611 < baseStart_660611 := by decide
  rcases family_descends (prefixWord ++ tailWord_660611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660665 : List Nat := [1, 2, 1, 4, 1, 4, 1, 4, 5]
def baseStart_660665 : Nat := 118140960795 + 660665 * 2 ^ 59
def prefixEnd_660665 : Nat := 4983230072969 + 3 ^ 40 * 660665 * 2
def baseEnd_660665 : Nat := 37693188511418097649907

theorem tailTrace_660665 : CollatzResearch.WordTrace tailWord_660665 prefixEnd_660665 37693188511418097649907 := by
  unfold tailWord_660665
  simp only [CollatzResearch.WordTrace]
  refine ⟨24096432151531012444047449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16064288101020674962698299 24096432151531012444047449)
  ·
    refine ⟨18072324113648259333035587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24096432151531012444047449 18072324113648259333035587)
    ·
      refine ⟨27108486170472388999553381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18072324113648259333035587 27108486170472388999553381)
      ·
        refine ⟨5082841156963572937416259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27108486170472388999553381 5082841156963572937416259)
        ·
          refine ⟨7624261735445359406124389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5082841156963572937416259 7624261735445359406124389)
          ·
            refine ⟨1429549075396004888648323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7624261735445359406124389 1429549075396004888648323)
            ·
              refine ⟨2144323613094007332972485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1429549075396004888648323 2144323613094007332972485)
              ·
                refine ⟨402060677455126374932341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2144323613094007332972485 402060677455126374932341)
                ·
                  refine ⟨37693188511418097649907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 402060677455126374932341 37693188511418097649907)
                  ·
                    rfl

theorem cell23_660665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 4, 5].length) (baseStart_660665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660665 prefixEnd_660665 := by exact prefixLift 660665
  have htrace : WordTrace (prefixWord ++ tailWord_660665) baseStart_660665 baseEnd_660665 := by
    simpa [prefixWord, tailWord_660665, baseEnd_660665] using wordTrace_append hprefix tailTrace_660665
  have hstable : (prefixWord ++ tailWord_660665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660665).length < 2 ^ (prefixWord ++ tailWord_660665).sum := by decide
  have hdescent : baseEnd_660665 < baseStart_660665 := by decide
  rcases family_descends (prefixWord ++ tailWord_660665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660691 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 2, 8]
def baseStart_660691 : Nat := 118140960795 + 660691 * 2 ^ 59
def prefixEnd_660691 : Nat := 4983230072969 + 3 ^ 40 * 660691 * 2
def baseEnd_660691 : Nat := 113084015699926592374681

theorem tailTrace_660691 : CollatzResearch.WordTrace tailWord_660691 prefixEnd_660691 113084015699926592374681 := by
  unfold tailWord_660691
  simp only [CollatzResearch.WordTrace]
  refine ⟨24097380449436818884493927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16064920299624545922995951 24097380449436818884493927)
  ·
    refine ⟨36146070674155228326740891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24097380449436818884493927 36146070674155228326740891)
    ·
      refine ⟨54219106011232842490111337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36146070674155228326740891 54219106011232842490111337)
      ·
        refine ⟨40664329508424631867583503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54219106011232842490111337 40664329508424631867583503)
        ·
          refine ⟨60996494262636947801375255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40664329508424631867583503 60996494262636947801375255)
          ·
            refine ⟨91494741393955421702062883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60996494262636947801375255 91494741393955421702062883)
            ·
              refine ⟨137242112090933132553094325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91494741393955421702062883 137242112090933132553094325)
              ·
                refine ⟨12866448008524981176852593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137242112090933132553094325 12866448008524981176852593)
                ·
                  refine ⟨9649836006393735882639445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12866448008524981176852593 9649836006393735882639445)
                  ·
                    refine ⟨113084015699926592374681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9649836006393735882639445 113084015699926592374681)
                    ·
                      rfl

theorem cell23_660691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 2, 8].length) (baseStart_660691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660691 prefixEnd_660691 := by exact prefixLift 660691
  have htrace : WordTrace (prefixWord ++ tailWord_660691) baseStart_660691 baseEnd_660691 := by
    simpa [prefixWord, tailWord_660691, baseEnd_660691] using wordTrace_append hprefix tailTrace_660691
  have hstable : (prefixWord ++ tailWord_660691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660691).length < 2 ^ (prefixWord ++ tailWord_660691).sum := by decide
  have hdescent : baseEnd_660691 < baseStart_660691 := by decide
  rcases family_descends (prefixWord ++ tailWord_660691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660715 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 2, 4, 2]
def baseStart_660715 : Nat := 118140960795 + 660715 * 2 ^ 59
def prefixEnd_660715 : Nat := 4983230072969 + 3 ^ 40 * 660715 * 2
def baseEnd_660715 : Nat := 339264370635487683223933

theorem tailTrace_660715 : CollatzResearch.WordTrace tailWord_660715 prefixEnd_660715 339264370635487683223933 := by
  unfold tailWord_660715
  simp only [CollatzResearch.WordTrace]
  refine ⟨24098255801349870983367599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16065503867566580655578399 24098255801349870983367599)
  ·
    refine ⟨36147383702024806475051399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24098255801349870983367599 36147383702024806475051399)
    ·
      refine ⟨54221075553037209712577099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36147383702024806475051399 54221075553037209712577099)
      ·
        refine ⟨81331613329555814568865649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54221075553037209712577099 81331613329555814568865649)
        ·
          refine ⟨60998709997166860926649237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81331613329555814568865649 60998709997166860926649237)
          ·
            refine ⟨2859314531117196605936683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60998709997166860926649237 2859314531117196605936683)
            ·
              refine ⟨4288971796675794908905025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2859314531117196605936683 4288971796675794908905025)
              ·
                refine ⟨3216728847506846181678769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4288971796675794908905025 3216728847506846181678769)
                ·
                  refine ⟨2412546635630134636259077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3216728847506846181678769 2412546635630134636259077)
                  ·
                    refine ⟨452352494180650244298577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2412546635630134636259077 452352494180650244298577)
                    ·
                      refine ⟨339264370635487683223933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 452352494180650244298577 339264370635487683223933)
                      ·
                        rfl

theorem cell23_660715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 4, 2].length) (baseStart_660715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660715 prefixEnd_660715 := by exact prefixLift 660715
  have htrace : WordTrace (prefixWord ++ tailWord_660715) baseStart_660715 baseEnd_660715 := by
    simpa [prefixWord, tailWord_660715, baseEnd_660715] using wordTrace_append hprefix tailTrace_660715
  have hstable : (prefixWord ++ tailWord_660715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660715).length < 2 ^ (prefixWord ++ tailWord_660715).sum := by decide
  have hdescent : baseEnd_660715 < baseStart_660715 := by decide
  rcases family_descends (prefixWord ++ tailWord_660715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660718 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_660718 : Nat := 118140960795 + 660718 * 2 ^ 59
def prefixEnd_660718 : Nat := 4983230072969 + 3 ^ 40 * 660718 * 2
def baseEnd_660718 : Nat := 339265911077451171486419

theorem tailTrace_660718 : CollatzResearch.WordTrace tailWord_660718 prefixEnd_660718 339265911077451171486419 := by
  unfold tailWord_660718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3012295652542375311965851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16065576813559334997151205 3012295652542375311965851)
  ·
    refine ⟨4518443478813562967948777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3012295652542375311965851 4518443478813562967948777)
    ·
      refine ⟨3388832609110172225961583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4518443478813562967948777 3388832609110172225961583)
      ·
        refine ⟨5083248913665258338942375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3388832609110172225961583 5083248913665258338942375)
        ·
          refine ⟨7624873370497887508413563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5083248913665258338942375 7624873370497887508413563)
          ·
            refine ⟨11437310055746831262620345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7624873370497887508413563 11437310055746831262620345)
            ·
              refine ⟨8577982541810123446965259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11437310055746831262620345 8577982541810123446965259)
              ·
                refine ⟨12866973812715185170447889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8577982541810123446965259 12866973812715185170447889)
                ·
                  refine ⟨9650230359536388877835917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12866973812715185170447889 9650230359536388877835917)
                  ·
                    refine ⟨3618836384826145829188469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9650230359536388877835917 3618836384826145829188469)
                    ·
                      refine ⟨339265911077451171486419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3618836384826145829188469 339265911077451171486419)
                      ·
                        rfl

theorem cell23_660718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_660718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660718 prefixEnd_660718 := by exact prefixLift 660718
  have htrace : WordTrace (prefixWord ++ tailWord_660718) baseStart_660718 baseEnd_660718 := by
    simpa [prefixWord, tailWord_660718, baseEnd_660718] using wordTrace_append hprefix tailTrace_660718
  have hstable : (prefixWord ++ tailWord_660718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660718).length < 2 ^ (prefixWord ++ tailWord_660718).sum := by decide
  have hdescent : baseEnd_660718 < baseStart_660718 := by decide
  rcases family_descends (prefixWord ++ tailWord_660718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660776 : List Nat := [2, 1, 5, 1, 2, 2, 3, 2, 1, 4]
def baseStart_660776 : Nat := 118140960795 + 660776 * 2 ^ 59
def prefixEnd_660776 : Nat := 4983230072969 + 3 ^ 40 * 660776 * 2
def baseEnd_660776 : Nat := 113098564318470648187051

theorem tailTrace_660776 : CollatzResearch.WordTrace tailWord_660776 prefixEnd_660776 113098564318470648187051 := by
  unfold tailWord_660776
  simp only [CollatzResearch.WordTrace]
  refine ⟨12050240327064439200669091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16066987102752585600892121 12050240327064439200669091)
  ·
    refine ⟨18075360490596658801003637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12050240327064439200669091 18075360490596658801003637)
    ·
      refine ⟨1694565045993436762594091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18075360490596658801003637 1694565045993436762594091)
      ·
        refine ⟨2541847568990155143891137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1694565045993436762594091 2541847568990155143891137)
        ·
          refine ⟨1906385676742616357918353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2541847568990155143891137 1906385676742616357918353)
          ·
            refine ⟨1429789257556962268438765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1906385676742616357918353 1429789257556962268438765)
            ·
              refine ⟨536170971583860850664537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1429789257556962268438765 536170971583860850664537)
              ·
                refine ⟨402128228687895637998403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 536170971583860850664537 402128228687895637998403)
                ·
                  refine ⟨603192343031843456997605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 402128228687895637998403 603192343031843456997605)
                  ·
                    refine ⟨113098564318470648187051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 603192343031843456997605 113098564318470648187051)
                    ·
                      rfl

theorem cell23_660776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_660776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660776 prefixEnd_660776 := by exact prefixLift 660776
  have htrace : WordTrace (prefixWord ++ tailWord_660776) baseStart_660776 baseEnd_660776 := by
    simpa [prefixWord, tailWord_660776, baseEnd_660776] using wordTrace_append hprefix tailTrace_660776
  have hstable : (prefixWord ++ tailWord_660776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660776).length < 2 ^ (prefixWord ++ tailWord_660776).sum := by decide
  have hdescent : baseEnd_660776 < baseStart_660776 := by decide
  rcases family_descends (prefixWord ++ tailWord_660776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660805 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 2, 6, 2]
def baseStart_660805 : Nat := 118140960795 + 660805 * 2 ^ 59
def prefixEnd_660805 : Nat := 4983230072969 + 3 ^ 40 * 660805 * 2
def baseEnd_660805 : Nat := 339310583894392331098519

theorem tailTrace_660805 : CollatzResearch.WordTrace tailWord_660805 prefixEnd_660805 339310583894392331098519 := by
  unfold tailWord_660805
  simp only [CollatzResearch.WordTrace]
  refine ⟨24101538371023816354143869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16067692247349210902762579 24101538371023816354143869)
  ·
    refine ⟨9038076889133931132803951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24101538371023816354143869 9038076889133931132803951)
    ·
      refine ⟨13557115333700896699205927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9038076889133931132803951 13557115333700896699205927)
      ·
        refine ⟨20335673000551345048808891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13557115333700896699205927 20335673000551345048808891)
        ·
          refine ⟨30503509500827017573213337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20335673000551345048808891 30503509500827017573213337)
          ·
            refine ⟨22877632125620263179910003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30503509500827017573213337 22877632125620263179910003)
            ·
              refine ⟨34316448188430394769865005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22877632125620263179910003 34316448188430394769865005)
              ·
                refine ⟨12868668070661398038699377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34316448188430394769865005 12868668070661398038699377)
                ·
                  refine ⟨9651501052996048529024533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12868668070661398038699377 9651501052996048529024533)
                  ·
                    refine ⟨452414111859189774798025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9651501052996048529024533 452414111859189774798025)
                    ·
                      refine ⟨339310583894392331098519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 452414111859189774798025 339310583894392331098519)
                      ·
                        rfl

theorem cell23_660805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 6, 2].length) (baseStart_660805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660805 prefixEnd_660805 := by exact prefixLift 660805
  have htrace : WordTrace (prefixWord ++ tailWord_660805) baseStart_660805 baseEnd_660805 := by
    simpa [prefixWord, tailWord_660805, baseEnd_660805] using wordTrace_append hprefix tailTrace_660805
  have hstable : (prefixWord ++ tailWord_660805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660805).length < 2 ^ (prefixWord ++ tailWord_660805).sum := by decide
  have hdescent : baseEnd_660805 < baseStart_660805 := by decide
  rcases family_descends (prefixWord ++ tailWord_660805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660825 : List Nat := [1, 2, 1, 2, 2, 2, 5, 1, 1, 1, 5]
def baseStart_660825 : Nat := 118140960795 + 660825 * 2 ^ 59
def prefixEnd_660825 : Nat := 4983230072969 + 3 ^ 40 * 660825 * 2
def baseEnd_660825 : Nat := 339320853507482252848427

theorem tailTrace_660825 : CollatzResearch.WordTrace tailWord_660825 prefixEnd_660825 339320853507482252848427 := by
  unfold tailWord_660825
  simp only [CollatzResearch.WordTrace]
  refine ⟨24102267830951359769871929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16068178553967573179914619 24102267830951359769871929)
  ·
    refine ⟨18076700873213519827403947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24102267830951359769871929 18076700873213519827403947)
    ·
      refine ⟨27115051309820279741105921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18076700873213519827403947 27115051309820279741105921)
      ·
        refine ⟨20336288482365209805829441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27115051309820279741105921 20336288482365209805829441)
        ·
          refine ⟨15252216361773907354372081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20336288482365209805829441 15252216361773907354372081)
          ·
            refine ⟨11439162271330430515779061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15252216361773907354372081 11439162271330430515779061)
            ·
              refine ⟨1072421462937227860854287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11439162271330430515779061 1072421462937227860854287)
              ·
                refine ⟨1608632194405841791281431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1072421462937227860854287 1608632194405841791281431)
                ·
                  refine ⟨2412948291608762686922147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1608632194405841791281431 2412948291608762686922147)
                  ·
                    refine ⟨3619422437413144030383221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2412948291608762686922147 3619422437413144030383221)
                    ·
                      refine ⟨339320853507482252848427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3619422437413144030383221 339320853507482252848427)
                      ·
                        rfl

theorem cell23_660825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_660825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660825 prefixEnd_660825 := by exact prefixLift 660825
  have htrace : WordTrace (prefixWord ++ tailWord_660825) baseStart_660825 baseEnd_660825 := by
    simpa [prefixWord, tailWord_660825, baseEnd_660825] using wordTrace_append hprefix tailTrace_660825
  have hstable : (prefixWord ++ tailWord_660825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660825).length < 2 ^ (prefixWord ++ tailWord_660825).sum := by decide
  have hdescent : baseEnd_660825 < baseStart_660825 := by decide
  rcases family_descends (prefixWord ++ tailWord_660825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660828 : List Nat := [2, 2, 4, 15]
def baseStart_660828 : Nat := 118140960795 + 660828 * 2 ^ 59
def prefixEnd_660828 : Nat := 4983230072969 + 3 ^ 40 * 660828 * 2
def baseEnd_660828 : Nat := 155154272496317211299

theorem tailTrace_660828 : CollatzResearch.WordTrace tailWord_660828 prefixEnd_660828 155154272496317211299 := by
  unfold tailWord_660828
  simp only [CollatzResearch.WordTrace]
  refine ⟨12051188624970245641115569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16068251499960327521487425 12051188624970245641115569)
  ·
    refine ⟨9038391468727684230836677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12051188624970245641115569 9038391468727684230836677)
    ·
      refine ⟨1694698400386440793281877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9038391468727684230836677 1694698400386440793281877)
      ·
        refine ⟨155154272496317211299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 1694698400386440793281877 155154272496317211299)
        ·
          rfl

theorem cell23_660828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 15].length) (baseStart_660828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660828 prefixEnd_660828 := by exact prefixLift 660828
  have htrace : WordTrace (prefixWord ++ tailWord_660828) baseStart_660828 baseEnd_660828 := by
    simpa [prefixWord, tailWord_660828, baseEnd_660828] using wordTrace_append hprefix tailTrace_660828
  have hstable : (prefixWord ++ tailWord_660828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660828).length < 2 ^ (prefixWord ++ tailWord_660828).sum := by decide
  have hdescent : baseEnd_660828 < baseStart_660828 := by decide
  rcases family_descends (prefixWord ++ tailWord_660828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660832 : List Nat := [2, 1, 1, 3, 4, 1, 1, 4, 2, 4]
def baseStart_660832 : Nat := 118140960795 + 660832 * 2 ^ 59
def prefixEnd_660832 : Nat := 4983230072969 + 3 ^ 40 * 660832 * 2
def baseEnd_660832 : Nat := 113108149290687908486965

theorem tailTrace_660832 : CollatzResearch.WordTrace tailWord_660832 prefixEnd_660832 113108149290687908486965 := by
  unfold tailWord_660832
  simp only [CollatzResearch.WordTrace]
  refine ⟨12051261570962999982688375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16068348761283999976917833 12051261570962999982688375)
  ·
    refine ⟨18076892356444499974032563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12051261570962999982688375 18076892356444499974032563)
    ·
      refine ⟨27115338534666749961048845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18076892356444499974032563 27115338534666749961048845)
      ·
        refine ⟨10168251950500031235393317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27115338534666749961048845 10168251950500031235393317)
        ·
          refine ⟨1906547240718755856636247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10168251950500031235393317 1906547240718755856636247)
          ·
            refine ⟨2859820861078133784954371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1906547240718755856636247 2859820861078133784954371)
            ·
              refine ⟨4289731291617200677431557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2859820861078133784954371 4289731291617200677431557)
              ·
                refine ⟨804324617178225127018417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4289731291617200677431557 804324617178225127018417)
                ·
                  refine ⟨603243462883668845263813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 804324617178225127018417 603243462883668845263813)
                  ·
                    refine ⟨113108149290687908486965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 603243462883668845263813 113108149290687908486965)
                    ·
                      rfl

theorem cell23_660832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 2, 4].length) (baseStart_660832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660832 prefixEnd_660832 := by exact prefixLift 660832
  have htrace : WordTrace (prefixWord ++ tailWord_660832) baseStart_660832 baseEnd_660832 := by
    simpa [prefixWord, tailWord_660832, baseEnd_660832] using wordTrace_append hprefix tailTrace_660832
  have hstable : (prefixWord ++ tailWord_660832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660832).length < 2 ^ (prefixWord ++ tailWord_660832).sum := by decide
  have hdescent : baseEnd_660832 < baseStart_660832 := by decide
  rcases family_descends (prefixWord ++ tailWord_660832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660845 : List Nat := [1, 5, 1, 1, 1, 3, 3, 8]
def baseStart_660845 : Nat := 118140960795 + 660845 * 2 ^ 59
def prefixEnd_660845 : Nat := 4983230072969 + 3 ^ 40 * 660845 * 2
def baseEnd_660845 : Nat := 12567819374836006466605

theorem tailTrace_660845 : CollatzResearch.WordTrace tailWord_660845 prefixEnd_660845 12567819374836006466605 := by
  unfold tailWord_660845
  simp only [CollatzResearch.WordTrace]
  refine ⟨24102997290878903185599989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16068664860585935457066659 24102997290878903185599989)
  ·
    refine ⟨2259655996019897173649999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24102997290878903185599989 2259655996019897173649999)
    ·
      refine ⟨3389483994029845760474999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2259655996019897173649999 3389483994029845760474999)
      ·
        refine ⟨5084225991044768640712499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3389483994029845760474999 5084225991044768640712499)
        ·
          refine ⟨7626338986567152961068749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5084225991044768640712499 7626338986567152961068749)
          ·
            refine ⟨2859877119962682360400781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7626338986567152961068749 2859877119962682360400781)
            ·
              refine ⟨1072453919986005885150293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2859877119962682360400781 1072453919986005885150293)
              ·
                refine ⟨12567819374836006466605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1072453919986005885150293 12567819374836006466605)
                ·
                  rfl

theorem cell23_660845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 8].length) (baseStart_660845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660845 prefixEnd_660845 := by exact prefixLift 660845
  have htrace : WordTrace (prefixWord ++ tailWord_660845) baseStart_660845 baseEnd_660845 := by
    simpa [prefixWord, tailWord_660845, baseEnd_660845] using wordTrace_append hprefix tailTrace_660845
  have hstable : (prefixWord ++ tailWord_660845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660845).length < 2 ^ (prefixWord ++ tailWord_660845).sum := by decide
  have hdescent : baseEnd_660845 < baseStart_660845 := by decide
  rcases family_descends (prefixWord ++ tailWord_660845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660872 : List Nat := [2, 1, 3, 3, 1, 2, 2, 2, 1, 3, 3]
def baseStart_660872 : Nat := 118140960795 + 660872 * 2 ^ 59
def prefixEnd_660872 : Nat := 4983230072969 + 3 ^ 40 * 660872 * 2
def baseEnd_660872 : Nat := 339344987098243568960711

theorem tailTrace_660872 : CollatzResearch.WordTrace tailWord_660872 prefixEnd_660872 339344987098243568960711 := by
  unfold tailWord_660872
  simp only [CollatzResearch.WordTrace]
  refine ⟨12051991030890543398416435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16069321374520724531221913 12051991030890543398416435)
  ·
    refine ⟨18077986546335815097624653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12051991030890543398416435 18077986546335815097624653)
    ·
      refine ⟨6779244954875930661609245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18077986546335815097624653 6779244954875930661609245)
      ·
        refine ⟨2542216858078473998103467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6779244954875930661609245 2542216858078473998103467)
        ·
          refine ⟨3813325287117710997155201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2542216858078473998103467 3813325287117710997155201)
          ·
            refine ⟨2859993965338283247866401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3813325287117710997155201 2859993965338283247866401)
            ·
              refine ⟨2144995474003712435899801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2859993965338283247866401 2144995474003712435899801)
              ·
                refine ⟨1608746605502784326924851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2144995474003712435899801 1608746605502784326924851)
                ·
                  refine ⟨2413119908254176490387277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1608746605502784326924851 2413119908254176490387277)
                  ·
                    refine ⟨904919965595316183895229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2413119908254176490387277 904919965595316183895229)
                    ·
                      refine ⟨339344987098243568960711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 904919965595316183895229 339344987098243568960711)
                      ·
                        rfl

theorem cell23_660872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_660872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660872 prefixEnd_660872 := by exact prefixLift 660872
  have htrace : WordTrace (prefixWord ++ tailWord_660872) baseStart_660872 baseEnd_660872 := by
    simpa [prefixWord, tailWord_660872, baseEnd_660872] using wordTrace_append hprefix tailTrace_660872
  have hstable : (prefixWord ++ tailWord_660872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660872).length < 2 ^ (prefixWord ++ tailWord_660872).sum := by decide
  have hdescent : baseEnd_660872 < baseStart_660872 := by decide
  rcases family_descends (prefixWord ++ tailWord_660872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660873 : List Nat := [1, 2, 1, 1, 7, 1, 2, 3, 1, 2, 2]
def baseStart_660873 : Nat := 118140960795 + 660873 * 2 ^ 59
def prefixEnd_660873 : Nat := 4983230072969 + 3 ^ 40 * 660873 * 2
def baseEnd_660873 : Nat := 339345500578898065048207

theorem tailTrace_660873 : CollatzResearch.WordTrace tailWord_660873 prefixEnd_660873 339345500578898065048207 := by
  unfold tailWord_660873
  simp only [CollatzResearch.WordTrace]
  refine ⟨24104018534777463967619273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16069345689851642645079515 24104018534777463967619273)
  ·
    refine ⟨18078013901083097975714455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24104018534777463967619273 18078013901083097975714455)
    ·
      refine ⟨27117020851624646963571683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18078013901083097975714455 27117020851624646963571683)
      ·
        refine ⟨40675531277436970445357525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27117020851624646963571683 40675531277436970445357525)
        ·
          refine ⟨953332764314928994813067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 40675531277436970445357525 953332764314928994813067)
          ·
            refine ⟨1429999146472393492219601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953332764314928994813067 1429999146472393492219601)
            ·
              refine ⟨1072499359854295119164701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1429999146472393492219601 1072499359854295119164701)
              ·
                refine ⟨402187259945360669686763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1072499359854295119164701 402187259945360669686763)
                ·
                  refine ⟨603280889918041004530145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 402187259945360669686763 603280889918041004530145)
                  ·
                    refine ⟨452460667438530753397609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 603280889918041004530145 452460667438530753397609)
                    ·
                      refine ⟨339345500578898065048207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 452460667438530753397609 339345500578898065048207)
                      ·
                        rfl

theorem cell23_660873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 1, 2, 2].length) (baseStart_660873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660873 prefixEnd_660873 := by exact prefixLift 660873
  have htrace : WordTrace (prefixWord ++ tailWord_660873) baseStart_660873 baseEnd_660873 := by
    simpa [prefixWord, tailWord_660873, baseEnd_660873] using wordTrace_append hprefix tailTrace_660873
  have hstable : (prefixWord ++ tailWord_660873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660873).length < 2 ^ (prefixWord ++ tailWord_660873).sum := by decide
  have hdescent : baseEnd_660873 < baseStart_660873 := by decide
  rcases family_descends (prefixWord ++ tailWord_660873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660889 : List Nat := [1, 2, 1, 2, 1, 5, 3, 2, 2, 1, 3]
def baseStart_660889 : Nat := 118140960795 + 660889 * 2 ^ 59
def prefixEnd_660889 : Nat := 4983230072969 + 3 ^ 40 * 660889 * 2
def baseEnd_660889 : Nat := 339353716269370002448133

theorem tailTrace_660889 : CollatzResearch.WordTrace tailWord_660889 prefixEnd_660889 339353716269370002448133 := by
  unfold tailWord_660889
  simp only [CollatzResearch.WordTrace]
  refine ⟨24104602102719498700201721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16069734735146332466801147 24104602102719498700201721)
  ·
    refine ⟨18078451577039624025151291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24104602102719498700201721 18078451577039624025151291)
    ·
      refine ⟨27117677365559436037726937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18078451577039624025151291 27117677365559436037726937)
      ·
        refine ⟨20338258024169577028295203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27117677365559436037726937 20338258024169577028295203)
        ·
          refine ⟨30507387036254365542442805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20338258024169577028295203 30507387036254365542442805)
          ·
            refine ⟨2860067534648846769604013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30507387036254365542442805 2860067534648846769604013)
            ·
              refine ⟨1072525325493317538601505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2860067534648846769604013 1072525325493317538601505)
              ·
                refine ⟨804393994119988153951129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1072525325493317538601505 804393994119988153951129)
                ·
                  refine ⟨603295495589991115463347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 804393994119988153951129 603295495589991115463347)
                  ·
                    refine ⟨904943243384986673195021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 603295495589991115463347 904943243384986673195021)
                    ·
                      refine ⟨339353716269370002448133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 904943243384986673195021 339353716269370002448133)
                      ·
                        rfl

theorem cell23_660889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 2, 1, 3].length) (baseStart_660889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660889 prefixEnd_660889 := by exact prefixLift 660889
  have htrace : WordTrace (prefixWord ++ tailWord_660889) baseStart_660889 baseEnd_660889 := by
    simpa [prefixWord, tailWord_660889, baseEnd_660889] using wordTrace_append hprefix tailTrace_660889
  have hstable : (prefixWord ++ tailWord_660889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660889).length < 2 ^ (prefixWord ++ tailWord_660889).sum := by decide
  have hdescent : baseEnd_660889 < baseStart_660889 := by decide
  rcases family_descends (prefixWord ++ tailWord_660889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660912 : List Nat := [2, 1, 1, 1, 2, 1, 1, 7, 1, 4, 2]
def baseStart_660912 : Nat := 118140960795 + 660912 * 2 ^ 59
def prefixEnd_660912 : Nat := 4983230072969 + 3 ^ 40 * 660912 * 2
def baseEnd_660912 : Nat := 339365526324423412460527

theorem tailTrace_660912 : CollatzResearch.WordTrace tailWord_660912 prefixEnd_660912 339365526324423412460527 := by
  unfold tailWord_660912
  simp only [CollatzResearch.WordTrace]
  refine ⟨12052720490818086814144495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16070293987757449085525993 12052720490818086814144495)
  ·
    refine ⟨18079080736227130221216743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12052720490818086814144495 18079080736227130221216743)
    ·
      refine ⟨27118621104340695331825115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18079080736227130221216743 27118621104340695331825115)
      ·
        refine ⟨40677931656511042997737673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27118621104340695331825115 40677931656511042997737673)
        ·
          refine ⟨30508448742383282248303255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40677931656511042997737673 30508448742383282248303255)
          ·
            refine ⟨45762673113574923372454883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30508448742383282248303255 45762673113574923372454883)
            ·
              refine ⟨68644009670362385058682325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45762673113574923372454883 68644009670362385058682325)
              ·
                refine ⟨1608843976649118399812867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 68644009670362385058682325 1608843976649118399812867)
                ·
                  refine ⟨2413265964973677599719301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1608843976649118399812867 2413265964973677599719301)
                  ·
                    refine ⟨452487368432564549947369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2413265964973677599719301 452487368432564549947369)
                    ·
                      refine ⟨339365526324423412460527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 452487368432564549947369 339365526324423412460527)
                      ·
                        rfl

theorem cell23_660912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 1, 4, 2].length) (baseStart_660912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660912 prefixEnd_660912 := by exact prefixLift 660912
  have htrace : WordTrace (prefixWord ++ tailWord_660912) baseStart_660912 baseEnd_660912 := by
    simpa [prefixWord, tailWord_660912, baseEnd_660912] using wordTrace_append hprefix tailTrace_660912
  have hstable : (prefixWord ++ tailWord_660912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660912).length < 2 ^ (prefixWord ++ tailWord_660912).sum := by decide
  have hdescent : baseEnd_660912 < baseStart_660912 := by decide
  rcases family_descends (prefixWord ++ tailWord_660912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660915 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 3]
def baseStart_660915 : Nat := 118140960795 + 660915 * 2 ^ 59
def prefixEnd_660915 : Nat := 4983230072969 + 3 ^ 40 * 660915 * 2
def baseEnd_660915 : Nat := 339367066766386900723013

theorem tailTrace_660915 : CollatzResearch.WordTrace tailWord_660915 prefixEnd_660915 339367066766386900723013 := by
  unfold tailWord_660915
  simp only [CollatzResearch.WordTrace]
  refine ⟨24105550400625305140648199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16070366933750203427098799 24105550400625305140648199)
  ·
    refine ⟨36158325600937957710972299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24105550400625305140648199 36158325600937957710972299)
    ·
      refine ⟨54237488401406936566458449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36158325600937957710972299 54237488401406936566458449)
      ·
        refine ⟨40678116301055202424843837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54237488401406936566458449 40678116301055202424843837)
        ·
          refine ⟨15254293612895700909316439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40678116301055202424843837 15254293612895700909316439)
          ·
            refine ⟨22881440419343551363974659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15254293612895700909316439 22881440419343551363974659)
            ·
              refine ⟨34322160629015327045961989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22881440419343551363974659 34322160629015327045961989)
              ·
                refine ⟨6435405117940373821117873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34322160629015327045961989 6435405117940373821117873)
                ·
                  refine ⟨4826553838455280365838405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6435405117940373821117873 4826553838455280365838405)
                  ·
                    refine ⟨904978844710365068594701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4826553838455280365838405 904978844710365068594701)
                    ·
                      refine ⟨339367066766386900723013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 904978844710365068594701 339367066766386900723013)
                      ·
                        rfl

theorem cell23_660915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 3].length) (baseStart_660915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660915 prefixEnd_660915 := by exact prefixLift 660915
  have htrace : WordTrace (prefixWord ++ tailWord_660915) baseStart_660915 baseEnd_660915 := by
    simpa [prefixWord, tailWord_660915, baseEnd_660915] using wordTrace_append hprefix tailTrace_660915
  have hstable : (prefixWord ++ tailWord_660915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660915).length < 2 ^ (prefixWord ++ tailWord_660915).sum := by decide
  have hdescent : baseEnd_660915 < baseStart_660915 := by decide
  rcases family_descends (prefixWord ++ tailWord_660915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660932 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_660932 : Nat := 118140960795 + 660932 * 2 ^ 59
def prefixEnd_660932 : Nat := 4983230072969 + 3 ^ 40 * 660932 * 2
def baseEnd_660932 : Nat := 339375795937513334210435

theorem tailTrace_660932 : CollatzResearch.WordTrace tailWord_660932 prefixEnd_660932 339375795937513334210435 := by
  unfold tailWord_660932
  simp only [CollatzResearch.WordTrace]
  refine ⟨12053085220781858522008525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16070780294375811362678033 12053085220781858522008525)
  ·
    refine ⟨4519906957793196945753197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12053085220781858522008525 4519906957793196945753197)
    ·
      refine ⟨1694965109172448854657449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4519906957793196945753197 1694965109172448854657449)
      ·
        refine ⟨1271223831879336640993087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1694965109172448854657449 1271223831879336640993087)
        ·
          refine ⟨1906835747819004961489631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1271223831879336640993087 1906835747819004961489631)
          ·
            refine ⟨2860253621728507442234447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1906835747819004961489631 2860253621728507442234447)
            ·
              refine ⟨4290380432592761163351671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2860253621728507442234447 4290380432592761163351671)
              ·
                refine ⟨6435570648889141745027507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4290380432592761163351671 6435570648889141745027507)
                ·
                  refine ⟨9653355973333712617541261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6435570648889141745027507 9653355973333712617541261)
                  ·
                    refine ⟨3620008490000142231577973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9653355973333712617541261 3620008490000142231577973)
                    ·
                      refine ⟨339375795937513334210435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3620008490000142231577973 339375795937513334210435)
                      ·
                        rfl

theorem cell23_660932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_660932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660932 prefixEnd_660932 := by exact prefixLift 660932
  have htrace : WordTrace (prefixWord ++ tailWord_660932) baseStart_660932 baseEnd_660932 := by
    simpa [prefixWord, tailWord_660932, baseEnd_660932] using wordTrace_append hprefix tailTrace_660932
  have hstable : (prefixWord ++ tailWord_660932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660932).length < 2 ^ (prefixWord ++ tailWord_660932).sum := by decide
  have hdescent : baseEnd_660932 < baseStart_660932 := by decide
  rcases family_descends (prefixWord ++ tailWord_660932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660952 : List Nat := [2, 1, 2, 2, 2, 1, 2, 6, 5]
def baseStart_660952 : Nat := 118140960795 + 660952 * 2 ^ 59
def prefixEnd_660952 : Nat := 4983230072969 + 3 ^ 40 * 660952 * 2
def baseEnd_660952 : Nat := 37709562838955917328927

theorem tailTrace_660952 : CollatzResearch.WordTrace tailWord_660952 prefixEnd_660952 37709562838955917328927 := by
  unfold tailWord_660952
  simp only [CollatzResearch.WordTrace]
  refine ⟨12053449950745630229872555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16071266600994173639830073 12053449950745630229872555)
  ·
    refine ⟨18080174926118445344808833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12053449950745630229872555 18080174926118445344808833)
    ·
      refine ⟨13560131194588834008606625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18080174926118445344808833 13560131194588834008606625)
      ·
        refine ⟨10170098395941625506454969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13560131194588834008606625 10170098395941625506454969)
        ·
          refine ⟨7627573796956219129841227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10170098395941625506454969 7627573796956219129841227)
          ·
            refine ⟨11441360695434328694761841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7627573796956219129841227 11441360695434328694761841)
            ·
              refine ⟨8581020521575746521071381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11441360695434328694761841 8581020521575746521071381)
              ·
                refine ⟨402235336948863118175221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8581020521575746521071381 402235336948863118175221)
                ·
                  refine ⟨37709562838955917328927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 402235336948863118175221 37709562838955917328927)
                  ·
                    rfl

theorem cell23_660952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 5].length) (baseStart_660952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660952 prefixEnd_660952 := by exact prefixLift 660952
  have htrace : WordTrace (prefixWord ++ tailWord_660952) baseStart_660952 baseEnd_660952 := by
    simpa [prefixWord, tailWord_660952, baseEnd_660952] using wordTrace_append hprefix tailTrace_660952
  have hstable : (prefixWord ++ tailWord_660952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660952).length < 2 ^ (prefixWord ++ tailWord_660952).sum := by decide
  have hdescent : baseEnd_660952 < baseStart_660952 := by decide
  rcases family_descends (prefixWord ++ tailWord_660952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660963 : List Nat := [1, 1, 1, 6, 2, 1, 4, 1, 2, 2, 2]
def baseStart_660963 : Nat := 118140960795 + 660963 * 2 ^ 59
def prefixEnd_660963 : Nat := 4983230072969 + 3 ^ 40 * 660963 * 2
def baseEnd_660963 : Nat := 339391713837802712922793

theorem tailTrace_660963 : CollatzResearch.WordTrace tailWord_660963 prefixEnd_660963 339391713837802712922793 := by
  unfold tailWord_660963
  simp only [CollatzResearch.WordTrace]
  refine ⟨24107301104451409338395543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16071534069634272892263695 24107301104451409338395543)
  ·
    refine ⟨36160951656677114007593315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24107301104451409338395543 36160951656677114007593315)
    ·
      refine ⟨54241427485015671011389973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36160951656677114007593315 54241427485015671011389973)
      ·
        refine ⟨2542566913360109578658905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 54241427485015671011389973 2542566913360109578658905)
        ·
          refine ⟨1906925185020082183994179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2542566913360109578658905 1906925185020082183994179)
          ·
            refine ⟨2860387777530123275991269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1906925185020082183994179 2860387777530123275991269)
            ·
              refine ⟨536322708286898114248363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2860387777530123275991269 536322708286898114248363)
              ·
                refine ⟨804484062430347171372545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536322708286898114248363 804484062430347171372545)
                ·
                  refine ⟨603363046822760378529409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 804484062430347171372545 603363046822760378529409)
                  ·
                    refine ⟨452522285117070283897057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 603363046822760378529409 452522285117070283897057)
                    ·
                      refine ⟨339391713837802712922793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 452522285117070283897057 339391713837802712922793)
                      ·
                        rfl

theorem cell23_660963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_660963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660963 prefixEnd_660963 := by exact prefixLift 660963
  have htrace : WordTrace (prefixWord ++ tailWord_660963) baseStart_660963 baseEnd_660963 := by
    simpa [prefixWord, tailWord_660963, baseEnd_660963] using wordTrace_append hprefix tailTrace_660963
  have hstable : (prefixWord ++ tailWord_660963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660963).length < 2 ^ (prefixWord ++ tailWord_660963).sum := by decide
  have hdescent : baseEnd_660963 < baseStart_660963 := by decide
  rcases family_descends (prefixWord ++ tailWord_660963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_660972 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 4, 5, 2]
def baseStart_660972 : Nat := 118140960795 + 660972 * 2 ^ 59
def prefixEnd_660972 : Nat := 4983230072969 + 3 ^ 40 * 660972 * 2
def baseEnd_660972 : Nat := 339396335163693177710251

theorem tailTrace_660972 : CollatzResearch.WordTrace tailWord_660972 prefixEnd_660972 339396335163693177710251 := by
  unfold tailWord_660972
  simp only [CollatzResearch.WordTrace]
  refine ⟨12053814680709401937736585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16071752907612535916982113 12053814680709401937736585)
  ·
    refine ⟨9040361010532051453302439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12053814680709401937736585 9040361010532051453302439)
    ·
      refine ⟨13560541515798077179953659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9040361010532051453302439 13560541515798077179953659)
      ·
        refine ⟨20340812273697115769930489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13560541515798077179953659 20340812273697115769930489)
        ·
          refine ⟨15255609205272836827447867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20340812273697115769930489 15255609205272836827447867)
          ·
            refine ⟨22883413807909255241171801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15255609205272836827447867 22883413807909255241171801)
            ·
              refine ⟨17162560355931941430878851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22883413807909255241171801 17162560355931941430878851)
              ·
                refine ⟨25743840533897912146318277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17162560355931941430878851 25743840533897912146318277)
                ·
                  refine ⟨4826970100105858527434677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25743840533897912146318277 4826970100105858527434677)
                  ·
                    refine ⟨452528446884924236947001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4826970100105858527434677 452528446884924236947001)
                    ·
                      refine ⟨339396335163693177710251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 452528446884924236947001 339396335163693177710251)
                      ·
                        rfl

theorem cell23_660972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 5, 2].length) (baseStart_660972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_660972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_660972 prefixEnd_660972 := by exact prefixLift 660972
  have htrace : WordTrace (prefixWord ++ tailWord_660972) baseStart_660972 baseEnd_660972 := by
    simpa [prefixWord, tailWord_660972, baseEnd_660972] using wordTrace_append hprefix tailTrace_660972
  have hstable : (prefixWord ++ tailWord_660972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_660972).length < 2 ^ (prefixWord ++ tailWord_660972).sum := by decide
  have hdescent : baseEnd_660972 < baseStart_660972 := by decide
  rcases family_descends (prefixWord ++ tailWord_660972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661003 : List Nat := [1, 1, 1, 1, 9, 1, 2, 2, 5]
def baseStart_661003 : Nat := 118140960795 + 661003 * 2 ^ 59
def prefixEnd_661003 : Nat := 4983230072969 + 3 ^ 40 * 661003 * 2
def baseEnd_661003 : Nat := 37712472562664728491401

theorem tailTrace_661003 : CollatzResearch.WordTrace tailWord_661003 prefixEnd_661003 37712472562664728491401 := by
  unfold tailWord_661003
  simp only [CollatzResearch.WordTrace]
  refine ⟨24108760024306496169851663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16072506682870997446567775 24108760024306496169851663)
  ·
    refine ⟨36163140036459744254777495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24108760024306496169851663 36163140036459744254777495)
    ·
      refine ⟨54244710054689616382166243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36163140036459744254777495 54244710054689616382166243)
      ·
        refine ⟨81367065082034424573249365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54244710054689616382166243 81367065082034424573249365)
        ·
          refine ⟨476760146965045456483883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 81367065082034424573249365 476760146965045456483883)
          ·
            refine ⟨715140220447568184725825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476760146965045456483883 715140220447568184725825)
            ·
              refine ⟨536355165335676138544369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 715140220447568184725825 536355165335676138544369)
              ·
                refine ⟨402266374001757103908277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 536355165335676138544369 402266374001757103908277)
                ·
                  refine ⟨37712472562664728491401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 402266374001757103908277 37712472562664728491401)
                  ·
                    rfl

theorem cell23_661003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 5].length) (baseStart_661003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661003 prefixEnd_661003 := by exact prefixLift 661003
  have htrace : WordTrace (prefixWord ++ tailWord_661003) baseStart_661003 baseEnd_661003 := by
    simpa [prefixWord, tailWord_661003, baseEnd_661003] using wordTrace_append hprefix tailTrace_661003
  have hstable : (prefixWord ++ tailWord_661003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661003).length < 2 ^ (prefixWord ++ tailWord_661003).sum := by decide
  have hdescent : baseEnd_661003 < baseStart_661003 := by decide
  rcases family_descends (prefixWord ++ tailWord_661003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661075 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 10]
def baseStart_661075 : Nat := 118140960795 + 661075 * 2 ^ 59
def prefixEnd_661075 : Nat := 4983230072969 + 3 ^ 40 * 661075 * 2
def baseEnd_661075 : Nat := 339449223671106274722277

theorem tailTrace_661075 : CollatzResearch.WordTrace tailWord_661075 prefixEnd_661075 339449223671106274722277 := by
  unfold tailWord_661075
  simp only [CollatzResearch.WordTrace]
  refine ⟨24111386080045652466472679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16074257386697101644315119 24111386080045652466472679)
  ·
    refine ⟨36167079120068478699709019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24111386080045652466472679 36167079120068478699709019)
    ·
      refine ⟨54250618680102718049563529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36167079120068478699709019 54250618680102718049563529)
      ·
        refine ⟨40687964010077038537172647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54250618680102718049563529 40687964010077038537172647)
        ·
          refine ⟨61031946015115557805758971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40687964010077038537172647 61031946015115557805758971)
          ·
            refine ⟨91547919022673336708638457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61031946015115557805758971 91547919022673336708638457)
            ·
              refine ⟨68660939267005002531478843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91547919022673336708638457 68660939267005002531478843)
              ·
                refine ⟨102991408900507503797218265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68660939267005002531478843 102991408900507503797218265)
                ·
                  refine ⟨77243556675380627847913699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102991408900507503797218265 77243556675380627847913699)
                  ·
                    refine ⟨115865335013070941771870549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77243556675380627847913699 115865335013070941771870549)
                    ·
                      refine ⟨339449223671106274722277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 115865335013070941771870549 339449223671106274722277)
                      ·
                        rfl

theorem cell23_661075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_661075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661075 prefixEnd_661075 := by exact prefixLift 661075
  have htrace : WordTrace (prefixWord ++ tailWord_661075) baseStart_661075 baseEnd_661075 := by
    simpa [prefixWord, tailWord_661075, baseEnd_661075] using wordTrace_append hprefix tailTrace_661075
  have hstable : (prefixWord ++ tailWord_661075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661075).length < 2 ^ (prefixWord ++ tailWord_661075).sum := by decide
  have hdescent : baseEnd_661075 < baseStart_661075 := by decide
  rcases family_descends (prefixWord ++ tailWord_661075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661079 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 1, 5, 2]
def baseStart_661079 : Nat := 118140960795 + 661079 * 2 ^ 59
def prefixEnd_661079 : Nat := 4983230072969 + 3 ^ 40 * 661079 * 2
def baseEnd_661079 : Nat := 339451277593724259072259

theorem tailTrace_661079 : CollatzResearch.WordTrace tailWord_661079 prefixEnd_661079 339451277593724259072259 := by
  unfold tailWord_661079
  simp only [CollatzResearch.WordTrace]
  refine ⟨24111531972031161149618291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16074354648020774099745527 24111531972031161149618291)
  ·
    refine ⟨36167297958046741724427437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24111531972031161149618291 36167297958046741724427437)
    ·
      refine ⟨13562736734267528146660289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36167297958046741724427437 13562736734267528146660289)
      ·
        refine ⟨10172052550700646109995217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13562736734267528146660289 10172052550700646109995217)
        ·
          refine ⟨7629039413025484582496413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10172052550700646109995217 7629039413025484582496413)
          ·
            refine ⟨2860889779884556718436155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7629039413025484582496413 2860889779884556718436155)
            ·
              refine ⟨4291334669826835077654233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2860889779884556718436155 4291334669826835077654233)
              ·
                refine ⟨3218501002370126308240675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4291334669826835077654233 3218501002370126308240675)
                ·
                  refine ⟨4827751503555189462361013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3218501002370126308240675 4827751503555189462361013)
                  ·
                    refine ⟨452601703458299012096345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4827751503555189462361013 452601703458299012096345)
                    ·
                      refine ⟨339451277593724259072259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 452601703458299012096345 339451277593724259072259)
                      ·
                        rfl

theorem cell23_661079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_661079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661079 prefixEnd_661079 := by exact prefixLift 661079
  have htrace : WordTrace (prefixWord ++ tailWord_661079) baseStart_661079 baseEnd_661079 := by
    simpa [prefixWord, tailWord_661079, baseEnd_661079] using wordTrace_append hprefix tailTrace_661079
  have hstable : (prefixWord ++ tailWord_661079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661079).length < 2 ^ (prefixWord ++ tailWord_661079).sum := by decide
  have hdescent : baseEnd_661079 < baseStart_661079 := by decide
  rcases family_descends (prefixWord ++ tailWord_661079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661089 : List Nat := [1, 2, 3, 1, 1, 3, 4, 2, 1, 5]
def baseStart_661089 : Nat := 118140960795 + 661089 * 2 ^ 59
def prefixEnd_661089 : Nat := 4983230072969 + 3 ^ 40 * 661089 * 2
def baseEnd_661089 : Nat := 113152137466756406649071

theorem tailTrace_661089 : CollatzResearch.WordTrace tailWord_661089 prefixEnd_661089 113152137466756406649071 := by
  unfold tailWord_661089
  simp only [CollatzResearch.WordTrace]
  refine ⟨24111896701994932857482321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16074597801329955238321547 24111896701994932857482321)
  ·
    refine ⟨18083922526496199643111741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24111896701994932857482321 18083922526496199643111741)
    ·
      refine ⟨6781470947436074866166903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18083922526496199643111741 6781470947436074866166903)
      ·
        refine ⟨10172206421154112299250355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6781470947436074866166903 10172206421154112299250355)
        ·
          refine ⟨15258309631731168448875533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10172206421154112299250355 15258309631731168448875533)
          ·
            refine ⟨5721866111899188168328325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15258309631731168448875533 5721866111899188168328325)
            ·
              refine ⟨1072849895981097781561561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5721866111899188168328325 1072849895981097781561561)
              ·
                refine ⟨804637421985823336171171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1072849895981097781561561 804637421985823336171171)
                ·
                  refine ⟨1206956132978735004256757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 804637421985823336171171 1206956132978735004256757)
                  ·
                    refine ⟨113152137466756406649071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1206956132978735004256757 113152137466756406649071)
                    ·
                      rfl

theorem cell23_661089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_661089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661089 prefixEnd_661089 := by exact prefixLift 661089
  have htrace : WordTrace (prefixWord ++ tailWord_661089) baseStart_661089 baseEnd_661089 := by
    simpa [prefixWord, tailWord_661089, baseEnd_661089] using wordTrace_append hprefix tailTrace_661089
  have hstable : (prefixWord ++ tailWord_661089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661089).length < 2 ^ (prefixWord ++ tailWord_661089).sum := by decide
  have hdescent : baseEnd_661089 < baseStart_661089 := by decide
  rcases family_descends (prefixWord ++ tailWord_661089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661096 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 1, 5, 2]
def baseStart_661096 : Nat := 118140960795 + 661096 * 2 ^ 59
def prefixEnd_661096 : Nat := 4983230072969 + 3 ^ 40 * 661096 * 2
def baseEnd_661096 : Nat := 339460006764850692559681

theorem tailTrace_661096 : CollatzResearch.WordTrace tailWord_661096 prefixEnd_661096 339460006764850692559681 := by
  unfold tailWord_661096
  simp only [CollatzResearch.WordTrace]
  refine ⟨12056076006484786526493571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16074768008646382035324761 12056076006484786526493571)
  ·
    refine ⟨18084114009727179789740357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12056076006484786526493571 18084114009727179789740357)
    ·
      refine ⟨3390771376823846210576317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18084114009727179789740357 3390771376823846210576317)
      ·
        refine ⟨1271539266308942328966119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3390771376823846210576317 1271539266308942328966119)
        ·
          refine ⟨1907308899463413493449179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1271539266308942328966119 1907308899463413493449179)
          ·
            refine ⟨2860963349195120240173769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1907308899463413493449179 2860963349195120240173769)
            ·
              refine ⟨2145722511896340180130327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2860963349195120240173769 2145722511896340180130327)
              ·
                refine ⟨3218583767844510270195491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2145722511896340180130327 3218583767844510270195491)
                ·
                  refine ⟨4827875651766765405293237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3218583767844510270195491 4827875651766765405293237)
                  ·
                    refine ⟨452613342353134256746241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4827875651766765405293237 452613342353134256746241)
                    ·
                      refine ⟨339460006764850692559681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 452613342353134256746241 339460006764850692559681)
                      ·
                        rfl

theorem cell23_661096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_661096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661096 prefixEnd_661096 := by exact prefixLift 661096
  have htrace : WordTrace (prefixWord ++ tailWord_661096) baseStart_661096 baseEnd_661096 := by
    simpa [prefixWord, tailWord_661096, baseEnd_661096] using wordTrace_append hprefix tailTrace_661096
  have hstable : (prefixWord ++ tailWord_661096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661096).length < 2 ^ (prefixWord ++ tailWord_661096).sum := by decide
  have hdescent : baseEnd_661096 < baseStart_661096 := by decide
  rcases family_descends (prefixWord ++ tailWord_661096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661132 : List Nat := [2, 2, 1, 2, 1, 1, 6, 8]
def baseStart_661132 : Nat := 118140960795 + 661132 * 2 ^ 59
def prefixEnd_661132 : Nat := 4983230072969 + 3 ^ 40 * 661132 * 2
def baseEnd_661132 : Nat := 12573277484015279692945

theorem tailTrace_661132 : CollatzResearch.WordTrace tailWord_661132 prefixEnd_661132 12573277484015279692945 := by
  unfold tailWord_661132
  simp only [CollatzResearch.WordTrace]
  refine ⟨12056732520419575600648825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16075643360559434134198433 12056732520419575600648825)
  ·
    refine ⟨9042549390314681700486619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12056732520419575600648825 9042549390314681700486619)
    ·
      refine ⟨13563824085472022550729929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9042549390314681700486619 13563824085472022550729929)
      ·
        refine ⟨10172868064104016913047447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13563824085472022550729929 10172868064104016913047447)
        ·
          refine ⟨15259302096156025369571171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10172868064104016913047447 15259302096156025369571171)
          ·
            refine ⟨22888953144234038054356757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15259302096156025369571171 22888953144234038054356757)
            ·
              refine ⟨1072919678635970533797973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22888953144234038054356757 1072919678635970533797973)
              ·
                refine ⟨12573277484015279692945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1072919678635970533797973 12573277484015279692945)
                ·
                  rfl

theorem cell23_661132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 8].length) (baseStart_661132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661132 prefixEnd_661132 := by exact prefixLift 661132
  have htrace : WordTrace (prefixWord ++ tailWord_661132) baseStart_661132 baseEnd_661132 := by
    simpa [prefixWord, tailWord_661132, baseEnd_661132] using wordTrace_append hprefix tailTrace_661132
  have hstable : (prefixWord ++ tailWord_661132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661132).length < 2 ^ (prefixWord ++ tailWord_661132).sum := by decide
  have hdescent : baseEnd_661132 < baseStart_661132 := by decide
  rcases family_descends (prefixWord ++ tailWord_661132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661140 : List Nat := [2, 4, 2, 2, 3, 1, 1, 2, 1, 5]
def baseStart_661140 : Nat := 118140960795 + 661140 * 2 ^ 59
def prefixEnd_661140 : Nat := 4983230072969 + 3 ^ 40 * 661140 * 2
def baseEnd_661140 : Nat := 113160866637882840136493

theorem tailTrace_661140 : CollatzResearch.WordTrace tailWord_661140 prefixEnd_661140 113160866637882840136493 := by
  unfold tailWord_661140
  simp only [CollatzResearch.WordTrace]
  refine ⟨12056878412405084283794437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16075837883206779045059249 12056878412405084283794437)
  ·
    refine ⟨2260664702325953303211457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12056878412405084283794437 2260664702325953303211457)
    ·
      refine ⟨1695498526744464977408593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2260664702325953303211457 1695498526744464977408593)
      ·
        refine ⟨1271623895058348733056445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1695498526744464977408593 1271623895058348733056445)
        ·
          refine ⟨476858960646880774896167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1271623895058348733056445 476858960646880774896167)
          ·
            refine ⟨715288440970321162344251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 476858960646880774896167 715288440970321162344251)
            ·
              refine ⟨1072932661455481743516377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715288440970321162344251 1072932661455481743516377)
              ·
                refine ⟨804699496091611307637283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1072932661455481743516377 804699496091611307637283)
                ·
                  refine ⟨1207049244137416961455925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 804699496091611307637283 1207049244137416961455925)
                  ·
                    refine ⟨113160866637882840136493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1207049244137416961455925 113160866637882840136493)
                    ·
                      rfl

theorem cell23_661140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_661140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661140 prefixEnd_661140 := by exact prefixLift 661140
  have htrace : WordTrace (prefixWord ++ tailWord_661140) baseStart_661140 baseEnd_661140 := by
    simpa [prefixWord, tailWord_661140, baseEnd_661140] using wordTrace_append hprefix tailTrace_661140
  have hstable : (prefixWord ++ tailWord_661140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661140).length < 2 ^ (prefixWord ++ tailWord_661140).sum := by decide
  have hdescent : baseEnd_661140 < baseStart_661140 := by decide
  rcases family_descends (prefixWord ++ tailWord_661140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661166 : List Nat := [4, 1, 4, 1, 3, 10]
def baseStart_661166 : Nat := 118140960795 + 661166 * 2 ^ 59
def prefixEnd_661166 : Nat := 4983230072969 + 3 ^ 40 * 661166 * 2
def baseEnd_661166 : Nat := 1397102676587100488413

theorem tailTrace_661166 : CollatzResearch.WordTrace tailWord_661166 prefixEnd_661166 1397102676587100488413 := by
  unfold tailWord_661166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3014338140339496876004419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16076470081810650005356901 3014338140339496876004419)
  ·
    refine ⟨4521507210509245314006629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3014338140339496876004419 4521507210509245314006629)
    ·
      refine ⟨847782601970483496376243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4521507210509245314006629 847782601970483496376243)
      ·
        refine ⟨1271673902955725244564365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 847782601970483496376243 1271673902955725244564365)
        ·
          refine ⟨476877713608396966711637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1271673902955725244564365 476877713608396966711637)
          ·
            refine ⟨1397102676587100488413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 476877713608396966711637 1397102676587100488413)
            ·
              rfl

theorem cell23_661166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 10].length) (baseStart_661166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661166 prefixEnd_661166 := by exact prefixLift 661166
  have htrace : WordTrace (prefixWord ++ tailWord_661166) baseStart_661166 baseEnd_661166 := by
    simpa [prefixWord, tailWord_661166, baseEnd_661166] using wordTrace_append hprefix tailTrace_661166
  have hstable : (prefixWord ++ tailWord_661166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661166).length < 2 ^ (prefixWord ++ tailWord_661166).sum := by decide
  have hdescent : baseEnd_661166 < baseStart_661166 := by decide
  rcases family_descends (prefixWord ++ tailWord_661166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661190 : List Nat := [6, 1, 2, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_661190 : Nat := 118140960795 + 661190 * 2 ^ 59
def prefixEnd_661190 : Nat := 4983230072969 + 3 ^ 40 * 661190 * 2
def baseEnd_661190 : Nat := 339508273946373324784249

theorem tailTrace_661190 : CollatzResearch.WordTrace tailWord_661190 prefixEnd_661190 339508273946373324784249 := by
  unfold tailWord_661190
  simp only [CollatzResearch.WordTrace]
  refine ⟨753611889832157097090907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16077053649752684737939349 753611889832157097090907)
  ·
    refine ⟨1130417834748235645636361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 753611889832157097090907 1130417834748235645636361)
    ·
      refine ⟨847813376061176734227271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1130417834748235645636361 847813376061176734227271)
      ·
        refine ⟨1271720064091765101340907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 847813376061176734227271 1271720064091765101340907)
        ·
          refine ⟨1907580096137647652011361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1271720064091765101340907 1907580096137647652011361)
          ·
            refine ⟨1430685072103235739008521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1907580096137647652011361 1430685072103235739008521)
            ·
              refine ⟨1073013804077426804256391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1430685072103235739008521 1073013804077426804256391)
              ·
                refine ⟨1609520706116140206384587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1073013804077426804256391 1609520706116140206384587)
                ·
                  refine ⟨2414281059174210309576881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1609520706116140206384587 2414281059174210309576881)
                  ·
                    refine ⟨1810710794380657732182661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2414281059174210309576881 1810710794380657732182661)
                    ·
                      refine ⟨339508273946373324784249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1810710794380657732182661 339508273946373324784249)
                      ·
                        rfl

theorem cell23_661190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_661190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661190 prefixEnd_661190 := by exact prefixLift 661190
  have htrace : WordTrace (prefixWord ++ tailWord_661190) baseStart_661190 baseEnd_661190 := by
    simpa [prefixWord, tailWord_661190, baseEnd_661190] using wordTrace_append hprefix tailTrace_661190
  have hstable : (prefixWord ++ tailWord_661190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661190).length < 2 ^ (prefixWord ++ tailWord_661190).sum := by decide
  have hdescent : baseEnd_661190 < baseStart_661190 := by decide
  rcases family_descends (prefixWord ++ tailWord_661190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661216 : List Nat := [2, 1, 1, 3, 1, 2, 4, 2, 1, 4, 2]
def baseStart_661216 : Nat := 118140960795 + 661216 * 2 ^ 59
def prefixEnd_661216 : Nat := 4983230072969 + 3 ^ 40 * 661216 * 2
def baseEnd_661216 : Nat := 339521624443390223059129

theorem tailTrace_661216 : CollatzResearch.WordTrace tailWord_661216 prefixEnd_661216 339521624443390223059129 := by
  unfold tailWord_661216
  simp only [CollatzResearch.WordTrace]
  refine ⟨12058264386267416773677751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16077685848356555698237001 12058264386267416773677751)
  ·
    refine ⟨18087396579401125160516627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12058264386267416773677751 18087396579401125160516627)
    ·
      refine ⟨27131094869101687740774941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18087396579401125160516627 27131094869101687740774941)
      ·
        refine ⟨10174160575913132902790603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27131094869101687740774941 10174160575913132902790603)
        ·
          refine ⟨15261240863869699354185905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10174160575913132902790603 15261240863869699354185905)
          ·
            refine ⟨11445930647902274515639429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15261240863869699354185905 11445930647902274515639429)
            ·
              refine ⟨2146111996481676471682393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11445930647902274515639429 2146111996481676471682393)
              ·
                refine ⟨1609583997361257353761795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2146111996481676471682393 1609583997361257353761795)
                ·
                  refine ⟨2414375996041886030642693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1609583997361257353761795 2414375996041886030642693)
                  ·
                    refine ⟨452695499257853630745505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2414375996041886030642693 452695499257853630745505)
                    ·
                      refine ⟨339521624443390223059129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 452695499257853630745505 339521624443390223059129)
                      ·
                        rfl

theorem cell23_661216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_661216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661216 prefixEnd_661216 := by exact prefixLift 661216
  have htrace : WordTrace (prefixWord ++ tailWord_661216) baseStart_661216 baseEnd_661216 := by
    simpa [prefixWord, tailWord_661216, baseEnd_661216] using wordTrace_append hprefix tailTrace_661216
  have hstable : (prefixWord ++ tailWord_661216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661216).length < 2 ^ (prefixWord ++ tailWord_661216).sum := by decide
  have hdescent : baseEnd_661216 < baseStart_661216 := by decide
  rcases family_descends (prefixWord ++ tailWord_661216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661232 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 9]
def baseStart_661232 : Nat := 118140960795 + 661232 * 2 ^ 59
def prefixEnd_661232 : Nat := 4983230072969 + 3 ^ 40 * 661232 * 2
def baseEnd_661232 : Nat := 339529840133862160459055

theorem tailTrace_661232 : CollatzResearch.WordTrace tailWord_661232 prefixEnd_661232 339529840133862160459055 := by
  unfold tailWord_661232
  simp only [CollatzResearch.WordTrace]
  refine ⟨12058556170238434139968975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16078074893651245519958633 12058556170238434139968975)
  ·
    refine ⟨18087834255357651209953463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12058556170238434139968975 18087834255357651209953463)
    ·
      refine ⟨27131751383036476814930195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18087834255357651209953463 27131751383036476814930195)
      ·
        refine ⟨40697627074554715222395293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27131751383036476814930195 40697627074554715222395293)
        ·
          refine ⟨15261610152958018208398235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40697627074554715222395293 15261610152958018208398235)
          ·
            refine ⟨22892415229437027312597353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15261610152958018208398235 22892415229437027312597353)
            ·
              refine ⟨17169311422077770484448015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22892415229437027312597353 17169311422077770484448015)
              ·
                refine ⟨25753967133116655726672023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17169311422077770484448015 25753967133116655726672023)
                ·
                  refine ⟨38630950699674983590008035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25753967133116655726672023 38630950699674983590008035)
                  ·
                    refine ⟨57946426049512475385012053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38630950699674983590008035 57946426049512475385012053)
                    ·
                      refine ⟨339529840133862160459055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 57946426049512475385012053 339529840133862160459055)
                      ·
                        rfl

theorem cell23_661232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_661232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661232 prefixEnd_661232 := by exact prefixLift 661232
  have htrace : WordTrace (prefixWord ++ tailWord_661232) baseStart_661232 baseEnd_661232 := by
    simpa [prefixWord, tailWord_661232, baseEnd_661232] using wordTrace_append hprefix tailTrace_661232
  have hstable : (prefixWord ++ tailWord_661232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661232).length < 2 ^ (prefixWord ++ tailWord_661232).sum := by decide
  have hdescent : baseEnd_661232 < baseStart_661232 := by decide
  rcases family_descends (prefixWord ++ tailWord_661232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661233 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 4, 2, 2]
def baseStart_661233 : Nat := 118140960795 + 661233 * 2 ^ 59
def prefixEnd_661233 : Nat := 4983230072969 + 3 ^ 40 * 661233 * 2
def baseEnd_661233 : Nat := 339530353614516656546551

theorem tailTrace_661233 : CollatzResearch.WordTrace tailWord_661233 prefixEnd_661233 339530353614516656546551 := by
  unfold tailWord_661233
  simp only [CollatzResearch.WordTrace]
  refine ⟨24117148813473245450724353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16078099208982163633816235 24117148813473245450724353)
  ·
    refine ⟨18087861610104934088043265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24117148813473245450724353 18087861610104934088043265)
    ·
      refine ⟨13565896207578700566032449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18087861610104934088043265 13565896207578700566032449)
      ·
        refine ⟨10174422155684025424524337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13565896207578700566032449 10174422155684025424524337)
        ·
          refine ⟨7630816616763019068393253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10174422155684025424524337 7630816616763019068393253)
          ·
            refine ⟨1430778115643066075323735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7630816616763019068393253 1430778115643066075323735)
            ·
              refine ⟨2146167173464599112985603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1430778115643066075323735 2146167173464599112985603)
              ·
                refine ⟨3219250760196898669478405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2146167173464599112985603 3219250760196898669478405)
                ·
                  refine ⟨603609517536918500527201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3219250760196898669478405 603609517536918500527201)
                  ·
                    refine ⟨452707138152688875395401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 603609517536918500527201 452707138152688875395401)
                    ·
                      refine ⟨339530353614516656546551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 452707138152688875395401 339530353614516656546551)
                      ·
                        rfl

theorem cell23_661233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_661233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661233 prefixEnd_661233 := by exact prefixLift 661233
  have htrace : WordTrace (prefixWord ++ tailWord_661233) baseStart_661233 baseEnd_661233 := by
    simpa [prefixWord, tailWord_661233, baseEnd_661233] using wordTrace_append hprefix tailTrace_661233
  have hstable : (prefixWord ++ tailWord_661233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661233).length < 2 ^ (prefixWord ++ tailWord_661233).sum := by decide
  have hdescent : baseEnd_661233 < baseStart_661233 := by decide
  rcases family_descends (prefixWord ++ tailWord_661233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661269 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 1, 7]
def baseStart_661269 : Nat := 118140960795 + 661269 * 2 ^ 59
def prefixEnd_661269 : Nat := 4983230072969 + 3 ^ 40 * 661269 * 2
def baseEnd_661269 : Nat := 113182946306026171898795

theorem tailTrace_661269 : CollatzResearch.WordTrace tailWord_661269 prefixEnd_661269 113182946306026171898795 := by
  unfold tailWord_661269
  simp only [CollatzResearch.WordTrace]
  refine ⟨24118461841342823599034861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16078974560895215732689907 24118461841342823599034861)
  ·
    refine ⟨9044423190503558849638073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24118461841342823599034861 9044423190503558849638073)
    ·
      refine ⟨6783317392877669137228555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9044423190503558849638073 6783317392877669137228555)
      ·
        refine ⟨10174976089316503705842833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6783317392877669137228555 10174976089316503705842833)
        ·
          refine ⟨7631232066987377779382125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10174976089316503705842833 7631232066987377779382125)
          ·
            refine ⟨2861712025120266667268297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7631232066987377779382125 2861712025120266667268297)
            ·
              refine ⟨2146284018840200000451223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2861712025120266667268297 2146284018840200000451223)
              ·
                refine ⟨3219426028260300000676835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2146284018840200000451223 3219426028260300000676835)
                ·
                  refine ⟨4829139042390450001015253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3219426028260300000676835 4829139042390450001015253)
                  ·
                    refine ⟨113182946306026171898795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4829139042390450001015253 113182946306026171898795)
                    ·
                      rfl

theorem cell23_661269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_661269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661269 prefixEnd_661269 := by exact prefixLift 661269
  have htrace : WordTrace (prefixWord ++ tailWord_661269) baseStart_661269 baseEnd_661269 := by
    simpa [prefixWord, tailWord_661269, baseEnd_661269] using wordTrace_append hprefix tailTrace_661269
  have hstable : (prefixWord ++ tailWord_661269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661269).length < 2 ^ (prefixWord ++ tailWord_661269).sum := by decide
  have hdescent : baseEnd_661269 < baseStart_661269 := by decide
  rcases family_descends (prefixWord ++ tailWord_661269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661279 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 5]
def baseStart_661279 : Nat := 118140960795 + 661279 * 2 ^ 59
def prefixEnd_661279 : Nat := 4983230072969 + 3 ^ 40 * 661279 * 2
def baseEnd_661279 : Nat := 339553973724623476571339

theorem tailTrace_661279 : CollatzResearch.WordTrace tailWord_661279 prefixEnd_661279 339553973724623476571339 := by
  unfold tailWord_661279
  simp only [CollatzResearch.WordTrace]
  refine ⟨24118826571306595306898891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16079217714204396871265927 24118826571306595306898891)
  ·
    refine ⟨36178239856959892960348337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24118826571306595306898891 36178239856959892960348337)
    ·
      refine ⟨27133679892719919720261253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36178239856959892960348337 27133679892719919720261253)
      ·
        refine ⟨5087564979884984947548985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27133679892719919720261253 5087564979884984947548985)
        ·
          refine ⟨3815673734913738710661739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5087564979884984947548985 3815673734913738710661739)
          ·
            refine ⟨5723510602370608065992609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3815673734913738710661739 5723510602370608065992609)
            ·
              refine ⟨4292632951777956049494457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5723510602370608065992609 4292632951777956049494457)
              ·
                refine ⟨3219474713833467037120843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4292632951777956049494457 3219474713833467037120843)
                ·
                  refine ⟨4829212070750200555681265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3219474713833467037120843 4829212070750200555681265)
                  ·
                    refine ⟨3621909053062650416760949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4829212070750200555681265 3621909053062650416760949)
                    ·
                      refine ⟨339553973724623476571339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3621909053062650416760949 339553973724623476571339)
                      ·
                        rfl

theorem cell23_661279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_661279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661279 prefixEnd_661279 := by exact prefixLift 661279
  have htrace : WordTrace (prefixWord ++ tailWord_661279) baseStart_661279 baseEnd_661279 := by
    simpa [prefixWord, tailWord_661279, baseEnd_661279] using wordTrace_append hprefix tailTrace_661279
  have hstable : (prefixWord ++ tailWord_661279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661279).length < 2 ^ (prefixWord ++ tailWord_661279).sum := by decide
  have hdescent : baseEnd_661279 < baseStart_661279 := by decide
  rcases family_descends (prefixWord ++ tailWord_661279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661319 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_661319 : Nat := 118140960795 + 661319 * 2 ^ 59
def prefixEnd_661319 : Nat := 4983230072969 + 3 ^ 40 * 661319 * 2
def baseEnd_661319 : Nat := 339574512950803320071155

theorem tailTrace_661319 : CollatzResearch.WordTrace tailWord_661319 prefixEnd_661319 339574512950803320071155 := by
  unfold tailWord_661319
  simp only [CollatzResearch.WordTrace]
  refine ⟨24120285491161682138355011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16080190327441121425570007 24120285491161682138355011)
  ·
    refine ⟨36180428236742523207532517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24120285491161682138355011 36180428236742523207532517)
    ·
      refine ⟨6783830294389223101412347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36180428236742523207532517 6783830294389223101412347)
      ·
        refine ⟨10175745441583834652118521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6783830294389223101412347 10175745441583834652118521)
        ·
          refine ⟨7631809081187875989088891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10175745441583834652118521 7631809081187875989088891)
          ·
            refine ⟨11447713621781813983633337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7631809081187875989088891 11447713621781813983633337)
            ·
              refine ⟨8585785216336360487725003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11447713621781813983633337 8585785216336360487725003)
              ·
                refine ⟨12878677824504540731587505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8585785216336360487725003 12878677824504540731587505)
                ·
                  refine ⟨9659008368378405548690629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12878677824504540731587505 9659008368378405548690629)
                  ·
                    refine ⟨1811064069070951040379493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9659008368378405548690629 1811064069070951040379493)
                    ·
                      refine ⟨339574512950803320071155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1811064069070951040379493 339574512950803320071155)
                      ·
                        rfl

theorem cell23_661319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_661319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661319 prefixEnd_661319 := by exact prefixLift 661319
  have htrace : WordTrace (prefixWord ++ tailWord_661319) baseStart_661319 baseEnd_661319 := by
    simpa [prefixWord, tailWord_661319, baseEnd_661319] using wordTrace_append hprefix tailTrace_661319
  have hstable : (prefixWord ++ tailWord_661319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661319).length < 2 ^ (prefixWord ++ tailWord_661319).sum := by decide
  have hdescent : baseEnd_661319 < baseStart_661319 := by decide
  rcases family_descends (prefixWord ++ tailWord_661319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661349 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 1, 2, 6]
def baseStart_661349 : Nat := 118140960795 + 661349 * 2 ^ 59
def prefixEnd_661349 : Nat := 4983230072969 + 3 ^ 40 * 661349 * 2
def baseEnd_661349 : Nat := 339589917370438202696017

theorem tailTrace_661349 : CollatzResearch.WordTrace tailWord_661349 prefixEnd_661349 339589917370438202696017 := by
  unfold tailWord_661349
  simp only [CollatzResearch.WordTrace]
  refine ⟨24121379681052997261947101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16080919787368664841298067 24121379681052997261947101)
  ·
    refine ⟨9045517380394873973230163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24121379681052997261947101 9045517380394873973230163)
    ·
      refine ⟨13568276070592310959845245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9045517380394873973230163 13568276070592310959845245)
      ·
        refine ⟨5088103526472116609941967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13568276070592310959845245 5088103526472116609941967)
        ·
          refine ⟨7632155289708174914912951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5088103526472116609941967 7632155289708174914912951)
          ·
            refine ⟨11448232934562262372369427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7632155289708174914912951 11448232934562262372369427)
            ·
              refine ⟨17172349401843393558554141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11448232934562262372369427 17172349401843393558554141)
              ·
                refine ⟨6439631025691272584457803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17172349401843393558554141 6439631025691272584457803)
                ·
                  refine ⟨9659446538536908876686705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6439631025691272584457803 9659446538536908876686705)
                  ·
                    refine ⟨7244584903902681657515029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9659446538536908876686705 7244584903902681657515029)
                    ·
                      refine ⟨339589917370438202696017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7244584903902681657515029 339589917370438202696017)
                      ·
                        rfl

theorem cell23_661349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_661349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661349 prefixEnd_661349 := by exact prefixLift 661349
  have htrace : WordTrace (prefixWord ++ tailWord_661349) baseStart_661349 baseEnd_661349 := by
    simpa [prefixWord, tailWord_661349, baseEnd_661349] using wordTrace_append hprefix tailTrace_661349
  have hstable : (prefixWord ++ tailWord_661349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661349).length < 2 ^ (prefixWord ++ tailWord_661349).sum := by decide
  have hdescent : baseEnd_661349 < baseStart_661349 := by decide
  rcases family_descends (prefixWord ++ tailWord_661349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661369 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 2, 1, 7]
def baseStart_661369 : Nat := 118140960795 + 661369 * 2 ^ 59
def prefixEnd_661369 : Nat := 4983230072969 + 3 ^ 40 * 661369 * 2
def baseEnd_661369 : Nat := 339600186983528124445925

theorem tailTrace_661369 : CollatzResearch.WordTrace tailWord_661369 prefixEnd_661369 339600186983528124445925 := by
  unfold tailWord_661369
  simp only [CollatzResearch.WordTrace]
  refine ⟨24122109140980540677675161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16081406093987027118450107 24122109140980540677675161)
  ·
    refine ⟨18091581855735405508256371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24122109140980540677675161 18091581855735405508256371)
    ·
      refine ⟨27137372783603108262384557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18091581855735405508256371 27137372783603108262384557)
      ·
        refine ⟨10176514793851165598394209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27137372783603108262384557 10176514793851165598394209)
        ·
          refine ⟨7632386095388374198795657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10176514793851165598394209 7632386095388374198795657)
          ·
            refine ⟨5724289571541280649096743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7632386095388374198795657 5724289571541280649096743)
            ·
              refine ⟨8586434357311920973645115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5724289571541280649096743 8586434357311920973645115)
              ·
                refine ⟨12879651535967881460467673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8586434357311920973645115 12879651535967881460467673)
                ·
                  refine ⟨9659738651975911095350755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12879651535967881460467673 9659738651975911095350755)
                  ·
                    refine ⟨14489607977963866643026133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9659738651975911095350755 14489607977963866643026133)
                    ·
                      refine ⟨339600186983528124445925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 14489607977963866643026133 339600186983528124445925)
                      ·
                        rfl

theorem cell23_661369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_661369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661369 prefixEnd_661369 := by exact prefixLift 661369
  have htrace : WordTrace (prefixWord ++ tailWord_661369) baseStart_661369 baseEnd_661369 := by
    simpa [prefixWord, tailWord_661369, baseEnd_661369] using wordTrace_append hprefix tailTrace_661369
  have hstable : (prefixWord ++ tailWord_661369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661369).length < 2 ^ (prefixWord ++ tailWord_661369).sum := by decide
  have hdescent : baseEnd_661369 < baseStart_661369 := by decide
  rcases family_descends (prefixWord ++ tailWord_661369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661376 : List Nat := [2, 1, 1, 2, 1, 2, 4, 4, 1, 5]
def baseStart_661376 : Nat := 118140960795 + 661376 * 2 ^ 59
def prefixEnd_661376 : Nat := 4983230072969 + 3 ^ 40 * 661376 * 2
def baseEnd_661376 : Nat := 113201260449369865686131

theorem tailTrace_661376 : CollatzResearch.WordTrace tailWord_661376 prefixEnd_661376 113201260449369865686131 := by
  unfold tailWord_661376
  simp only [CollatzResearch.WordTrace]
  refine ⟨12061182225977590436589991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16081576301303453915453321 12061182225977590436589991)
  ·
    refine ⟨18091773338966385654884987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12061182225977590436589991 18091773338966385654884987)
    ·
      refine ⟨27137660008449578482327481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18091773338966385654884987 27137660008449578482327481)
      ·
        refine ⟨20353245006337183861745611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27137660008449578482327481 20353245006337183861745611)
        ·
          refine ⟨30529867509505775792618417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20353245006337183861745611 30529867509505775792618417)
          ·
            refine ⟨22897400632129331844463813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30529867509505775792618417 22897400632129331844463813)
            ·
              refine ⟨4293262618524249720836965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22897400632129331844463813 4293262618524249720836965)
              ·
                refine ⟨804986740973296822656931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4293262618524249720836965 804986740973296822656931)
                ·
                  refine ⟨1207480111459945233985397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 804986740973296822656931 1207480111459945233985397)
                  ·
                    refine ⟨113201260449369865686131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1207480111459945233985397 113201260449369865686131)
                    ·
                      rfl

theorem cell23_661376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 4, 1, 5].length) (baseStart_661376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661376 prefixEnd_661376 := by exact prefixLift 661376
  have htrace : WordTrace (prefixWord ++ tailWord_661376) baseStart_661376 baseEnd_661376 := by
    simpa [prefixWord, tailWord_661376, baseEnd_661376] using wordTrace_append hprefix tailTrace_661376
  have hstable : (prefixWord ++ tailWord_661376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661376).length < 2 ^ (prefixWord ++ tailWord_661376).sum := by decide
  have hdescent : baseEnd_661376 < baseStart_661376 := by decide
  rcases family_descends (prefixWord ++ tailWord_661376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661377 : List Nat := [1, 2, 4, 4, 1, 2, 1, 1, 2, 2, 3]
def baseStart_661377 : Nat := 118140960795 + 661377 * 2 ^ 59
def prefixEnd_661377 : Nat := 4983230072969 + 3 ^ 40 * 661377 * 2
def baseEnd_661377 : Nat := 339604294828764093145889

theorem tailTrace_661377 : CollatzResearch.WordTrace tailWord_661377 prefixEnd_661377 339604294828764093145889 := by
  unfold tailWord_661377
  simp only [CollatzResearch.WordTrace]
  refine ⟨24122400924951558043966385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16081600616634372029310923 24122400924951558043966385)
  ·
    refine ⟨18091800693713668532974789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24122400924951558043966385 18091800693713668532974789)
    ·
      refine ⟨3392212630071312849932773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18091800693713668532974789 3392212630071312849932773)
      ·
        refine ⟨636039868138371159362395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3392212630071312849932773 636039868138371159362395)
        ·
          refine ⟨954059802207556739043593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636039868138371159362395 954059802207556739043593)
          ·
            refine ⟨715544851655667554282695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954059802207556739043593 715544851655667554282695)
            ·
              refine ⟨1073317277483501331424043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715544851655667554282695 1073317277483501331424043)
              ·
                refine ⟨1609975916225251997136065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1073317277483501331424043 1609975916225251997136065)
                ·
                  refine ⟨1207481937168938997852049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1609975916225251997136065 1207481937168938997852049)
                  ·
                    refine ⟨905611452876704248389037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1207481937168938997852049 905611452876704248389037)
                    ·
                      refine ⟨339604294828764093145889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 905611452876704248389037 339604294828764093145889)
                      ·
                        rfl

theorem cell23_661377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_661377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661377 prefixEnd_661377 := by exact prefixLift 661377
  have htrace : WordTrace (prefixWord ++ tailWord_661377) baseStart_661377 baseEnd_661377 := by
    simpa [prefixWord, tailWord_661377, baseEnd_661377] using wordTrace_append hprefix tailTrace_661377
  have hstable : (prefixWord ++ tailWord_661377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661377).length < 2 ^ (prefixWord ++ tailWord_661377).sum := by decide
  have hdescent : baseEnd_661377 < baseStart_661377 := by decide
  rcases family_descends (prefixWord ++ tailWord_661377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661393 : List Nat := [1, 2, 2, 1, 1, 1, 8, 1, 1, 5]
def baseStart_661393 : Nat := 118140960795 + 661393 * 2 ^ 59
def prefixEnd_661393 : Nat := 4983230072969 + 3 ^ 40 * 661393 * 2
def baseEnd_661393 : Nat := 113204170173078676848605

theorem tailTrace_661393 : CollatzResearch.WordTrace tailWord_661393 prefixEnd_661393 113204170173078676848605 := by
  unfold tailWord_661393
  simp only [CollatzResearch.WordTrace]
  refine ⟨24122984492893592776548833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16081989661929061851032555 24122984492893592776548833)
  ·
    refine ⟨18092238369670194582411625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24122984492893592776548833 18092238369670194582411625)
    ·
      refine ⟨13569178777252645936808719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18092238369670194582411625 13569178777252645936808719)
      ·
        refine ⟨20353768165878968905213079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13569178777252645936808719 20353768165878968905213079)
        ·
          refine ⟨30530652248818453357819619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20353768165878968905213079 30530652248818453357819619)
          ·
            refine ⟨45795978373227680036729429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30530652248818453357819619 45795978373227680036729429)
            ·
              refine ⟨536671621561261875430423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 45795978373227680036729429 536671621561261875430423)
              ·
                refine ⟨805007432341892813145635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536671621561261875430423 805007432341892813145635)
                ·
                  refine ⟨1207511148512839219718453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805007432341892813145635 1207511148512839219718453)
                  ·
                    refine ⟨113204170173078676848605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1207511148512839219718453 113204170173078676848605)
                    ·
                      rfl

theorem cell23_661393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 1, 5].length) (baseStart_661393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661393 prefixEnd_661393 := by exact prefixLift 661393
  have htrace : WordTrace (prefixWord ++ tailWord_661393) baseStart_661393 baseEnd_661393 := by
    simpa [prefixWord, tailWord_661393, baseEnd_661393] using wordTrace_append hprefix tailTrace_661393
  have hstable : (prefixWord ++ tailWord_661393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661393).length < 2 ^ (prefixWord ++ tailWord_661393).sum := by decide
  have hdescent : baseEnd_661393 < baseStart_661393 := by decide
  rcases family_descends (prefixWord ++ tailWord_661393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661463 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 4, 1, 3]
def baseStart_661463 : Nat := 118140960795 + 661463 * 2 ^ 59
def prefixEnd_661463 : Nat := 4983230072969 + 3 ^ 40 * 661463 * 2
def baseEnd_661463 : Nat := 339648454165050756670493

theorem tailTrace_661463 : CollatzResearch.WordTrace tailWord_661463 prefixEnd_661463 339648454165050756670493 := by
  unfold tailWord_661463
  simp only [CollatzResearch.WordTrace]
  refine ⟨24125537602639994731597043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16083691735093329821064695 24125537602639994731597043)
  ·
    refine ⟨36188306403959992097395565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24125537602639994731597043 36188306403959992097395565)
    ·
      refine ⟨13570614901484997036523337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36188306403959992097395565 13570614901484997036523337)
      ·
        refine ⟨10177961176113747777392503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13570614901484997036523337 10177961176113747777392503)
        ·
          refine ⟨15266941764170621666088755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10177961176113747777392503 15266941764170621666088755)
          ·
            refine ⟨22900412646255932499133133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15266941764170621666088755 22900412646255932499133133)
            ·
              refine ⟨8587654742345974687174925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22900412646255932499133133 8587654742345974687174925)
              ·
                refine ⟨3220370528379740507690597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8587654742345974687174925 3220370528379740507690597)
                ·
                  refine ⟨603819474071201345191987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3220370528379740507690597 603819474071201345191987)
                  ·
                    refine ⟨905729211106802017787981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 603819474071201345191987 905729211106802017787981)
                    ·
                      refine ⟨339648454165050756670493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 905729211106802017787981 339648454165050756670493)
                      ·
                        rfl

theorem cell23_661463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_661463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661463 prefixEnd_661463 := by exact prefixLift 661463
  have htrace : WordTrace (prefixWord ++ tailWord_661463) baseStart_661463 baseEnd_661463 := by
    simpa [prefixWord, tailWord_661463, baseEnd_661463] using wordTrace_append hprefix tailTrace_661463
  have hstable : (prefixWord ++ tailWord_661463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661463).length < 2 ^ (prefixWord ++ tailWord_661463).sum := by decide
  have hdescent : baseEnd_661463 < baseStart_661463 := by decide
  rcases family_descends (prefixWord ++ tailWord_661463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661464 : List Nat := [2, 1, 2, 2, 2, 2, 5, 2, 1, 2, 2]
def baseStart_661464 : Nat := 118140960795 + 661464 * 2 ^ 59
def prefixEnd_661464 : Nat := 4983230072969 + 3 ^ 40 * 661464 * 2
def baseEnd_661464 : Nat := 339648967645705252757989

theorem tailTrace_661464 : CollatzResearch.WordTrace tailWord_661464 prefixEnd_661464 339648967645705252757989 := by
  unfold tailWord_661464
  simp only [CollatzResearch.WordTrace]
  refine ⟨12062787037818185951191723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16083716050424247934922297 12062787037818185951191723)
  ·
    refine ⟨18094180556727278926787585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12062787037818185951191723 18094180556727278926787585)
    ·
      refine ⟨13570635417545459195090689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18094180556727278926787585 13570635417545459195090689)
      ·
        refine ⟨10177976563159094396318017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13570635417545459195090689 10177976563159094396318017)
        ·
          refine ⟨7633482422369320797238513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10177976563159094396318017 7633482422369320797238513)
          ·
            refine ⟨5725111816776990597928885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7633482422369320797238513 5725111816776990597928885)
            ·
              refine ⟨536729232822842868555833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5725111816776990597928885 536729232822842868555833)
              ·
                refine ⟨402546924617132151416875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 536729232822842868555833 402546924617132151416875)
                ·
                  refine ⟨603820386925698227125313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 402546924617132151416875 603820386925698227125313)
                  ·
                    refine ⟨452865290194273670343985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 603820386925698227125313 452865290194273670343985)
                    ·
                      refine ⟨339648967645705252757989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 452865290194273670343985 339648967645705252757989)
                      ·
                        rfl

theorem cell23_661464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 1, 2, 2].length) (baseStart_661464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661464 prefixEnd_661464 := by exact prefixLift 661464
  have htrace : WordTrace (prefixWord ++ tailWord_661464) baseStart_661464 baseEnd_661464 := by
    simpa [prefixWord, tailWord_661464, baseEnd_661464] using wordTrace_append hprefix tailTrace_661464
  have hstable : (prefixWord ++ tailWord_661464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661464).length < 2 ^ (prefixWord ++ tailWord_661464).sum := by decide
  have hdescent : baseEnd_661464 < baseStart_661464 := by decide
  rcases family_descends (prefixWord ++ tailWord_661464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661533 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_661533 : Nat := 118140960795 + 661533 * 2 ^ 59
def prefixEnd_661533 : Nat := 4983230072969 + 3 ^ 40 * 661533 * 2
def baseEnd_661533 : Nat := 339684397810865482795171

theorem tailTrace_661533 : CollatzResearch.WordTrace tailWord_661533 prefixEnd_661533 339684397810865482795171 := by
  unfold tailWord_661533
  simp only [CollatzResearch.WordTrace]
  refine ⟨24128090712386396686645253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16085393808257597791096835 24128090712386396686645253)
  ·
    refine ⟨4524017008572449378745985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24128090712386396686645253 4524017008572449378745985)
    ·
      refine ⟨3393012756429337034059489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4524017008572449378745985 3393012756429337034059489)
      ·
        refine ⟨2544759567322002775544617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3393012756429337034059489 2544759567322002775544617)
        ·
          refine ⟨1908569675491502081658463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2544759567322002775544617 1908569675491502081658463)
          ·
            refine ⟨2862854513237253122487695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1908569675491502081658463 2862854513237253122487695)
            ·
              refine ⟨4294281769855879683731543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2862854513237253122487695 4294281769855879683731543)
              ·
                refine ⟨6441422654783819525597315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4294281769855879683731543 6441422654783819525597315)
                ·
                  refine ⟨9662133982175729288395973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6441422654783819525597315 9662133982175729288395973)
                  ·
                    refine ⟨1811650121657949241574245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9662133982175729288395973 1811650121657949241574245)
                    ·
                      refine ⟨339684397810865482795171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1811650121657949241574245 339684397810865482795171)
                      ·
                        rfl

theorem cell23_661533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_661533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661533 prefixEnd_661533 := by exact prefixLift 661533
  have htrace : WordTrace (prefixWord ++ tailWord_661533) baseStart_661533 baseEnd_661533 := by
    simpa [prefixWord, tailWord_661533, baseEnd_661533] using wordTrace_append hprefix tailTrace_661533
  have hstable : (prefixWord ++ tailWord_661533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661533).length < 2 ^ (prefixWord ++ tailWord_661533).sum := by decide
  have hdescent : baseEnd_661533 < baseStart_661533 := by decide
  rcases family_descends (prefixWord ++ tailWord_661533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661537 : List Nat := [1, 2, 3, 2, 4, 1, 2, 1, 1, 4, 2]
def baseStart_661537 : Nat := 118140960795 + 661537 * 2 ^ 59
def prefixEnd_661537 : Nat := 4983230072969 + 3 ^ 40 * 661537 * 2
def baseEnd_661537 : Nat := 339686451733483467145153

theorem tailTrace_661537 : CollatzResearch.WordTrace tailWord_661537 prefixEnd_661537 339686451733483467145153 := by
  unfold tailWord_661537
  simp only [CollatzResearch.WordTrace]
  refine ⟨24128236604371905369790865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16085491069581270246527243 24128236604371905369790865)
  ·
    refine ⟨18096177453278929027343149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24128236604371905369790865 18096177453278929027343149)
    ·
      refine ⟨6786066544979598385253681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18096177453278929027343149 6786066544979598385253681)
      ·
        refine ⟨5089549908734698788940261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6786066544979598385253681 5089549908734698788940261)
        ·
          refine ⟨954290607887756022926299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5089549908734698788940261 954290607887756022926299)
          ·
            refine ⟨1431435911831634034389449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 954290607887756022926299 1431435911831634034389449)
            ·
              refine ⟨1073576933873725525792087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1431435911831634034389449 1073576933873725525792087)
              ·
                refine ⟨1610365400810588288688131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1073576933873725525792087 1610365400810588288688131)
                ·
                  refine ⟨2415548101215882433032197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1610365400810588288688131 2415548101215882433032197)
                  ·
                    refine ⟨452915268977977956193537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2415548101215882433032197 452915268977977956193537)
                    ·
                      refine ⟨339686451733483467145153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 452915268977977956193537 339686451733483467145153)
                      ·
                        rfl

theorem cell23_661537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_661537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661537 prefixEnd_661537 := by exact prefixLift 661537
  have htrace : WordTrace (prefixWord ++ tailWord_661537) baseStart_661537 baseEnd_661537 := by
    simpa [prefixWord, tailWord_661537, baseEnd_661537] using wordTrace_append hprefix tailTrace_661537
  have hstable : (prefixWord ++ tailWord_661537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661537).length < 2 ^ (prefixWord ++ tailWord_661537).sum := by decide
  have hdescent : baseEnd_661537 < baseStart_661537 := by decide
  rcases family_descends (prefixWord ++ tailWord_661537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661563 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 4, 5, 2]
def baseStart_661563 : Nat := 118140960795 + 661563 * 2 ^ 59
def prefixEnd_661563 : Nat := 4983230072969 + 3 ^ 40 * 661563 * 2
def baseEnd_661563 : Nat := 339699802230500365420033

theorem tailTrace_661563 : CollatzResearch.WordTrace tailWord_661563 prefixEnd_661563 339699802230500365420033 := by
  unfold tailWord_661563
  simp only [CollatzResearch.WordTrace]
  refine ⟨24129184902277711810237343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16086123268185141206824895 24129184902277711810237343)
  ·
    refine ⟨36193777353416567715356015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24129184902277711810237343 36193777353416567715356015)
    ·
      refine ⟨54290666030124851573034023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36193777353416567715356015 54290666030124851573034023)
      ·
        refine ⟨81435999045187277359551035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54290666030124851573034023 81435999045187277359551035)
        ·
          refine ⟨122153998567780916039326553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81435999045187277359551035 122153998567780916039326553)
          ·
            refine ⟨91615498925835687029494915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122153998567780916039326553 91615498925835687029494915)
            ·
              refine ⟨137423248388753530544242373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91615498925835687029494915 137423248388753530544242373)
              ·
                refine ⟨25766859072891286977045445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137423248388753530544242373 25766859072891286977045445)
                ·
                  refine ⟨4831286076167116308196021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25766859072891286977045445 4831286076167116308196021)
                  ·
                    refine ⟨452933069640667153893377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4831286076167116308196021 452933069640667153893377)
                    ·
                      refine ⟨339699802230500365420033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 452933069640667153893377 339699802230500365420033)
                      ·
                        rfl

theorem cell23_661563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 5, 2].length) (baseStart_661563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661563 prefixEnd_661563 := by exact prefixLift 661563
  have htrace : WordTrace (prefixWord ++ tailWord_661563) baseStart_661563 baseEnd_661563 := by
    simpa [prefixWord, tailWord_661563, baseEnd_661563] using wordTrace_append hprefix tailTrace_661563
  have hstable : (prefixWord ++ tailWord_661563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661563).length < 2 ^ (prefixWord ++ tailWord_661563).sum := by decide
  have hdescent : baseEnd_661563 < baseStart_661563 := by decide
  rcases family_descends (prefixWord ++ tailWord_661563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661637 : List Nat := [1, 3, 1, 1, 5, 3, 1, 1, 3, 4]
def baseStart_661637 : Nat := 118140960795 + 661637 * 2 ^ 59
def prefixEnd_661637 : Nat := 4983230072969 + 3 ^ 40 * 661637 * 2
def baseEnd_661637 : Nat := 113245933266311025298231

theorem tailTrace_661637 : CollatzResearch.WordTrace tailWord_661637 prefixEnd_661637 113245933266311025298231 := by
  unfold tailWord_661637
  simp only [CollatzResearch.WordTrace]
  refine ⟨24131883904009622448431165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16087922602673081632287443 24131883904009622448431165)
  ·
    refine ⟨9049456464003608418161687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24131883904009622448431165 9049456464003608418161687)
    ·
      refine ⟨13574184696005412627242531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9049456464003608418161687 13574184696005412627242531)
      ·
        refine ⟨20361277044008118940863797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13574184696005412627242531 20361277044008118940863797)
        ·
          refine ⟨1908869722875761150705981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20361277044008118940863797 1908869722875761150705981)
          ·
            refine ⟨715826146078410431514743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1908869722875761150705981 715826146078410431514743)
            ·
              refine ⟨1073739219117615647272115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715826146078410431514743 1073739219117615647272115)
              ·
                refine ⟨1610608828676423470908173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1073739219117615647272115 1610608828676423470908173)
                ·
                  refine ⟨603978310753658801590565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1610608828676423470908173 603978310753658801590565)
                  ·
                    refine ⟨113245933266311025298231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 603978310753658801590565 113245933266311025298231)
                    ·
                      rfl

theorem cell23_661637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 3, 4].length) (baseStart_661637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661637 prefixEnd_661637 := by exact prefixLift 661637
  have htrace : WordTrace (prefixWord ++ tailWord_661637) baseStart_661637 baseEnd_661637 := by
    simpa [prefixWord, tailWord_661637, baseEnd_661637] using wordTrace_append hprefix tailTrace_661637
  have hstable : (prefixWord ++ tailWord_661637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661637).length < 2 ^ (prefixWord ++ tailWord_661637).sum := by decide
  have hdescent : baseEnd_661637 < baseStart_661637 := by decide
  rcases family_descends (prefixWord ++ tailWord_661637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661650 : List Nat := [3, 2, 3, 1, 1, 1, 3, 3, 6]
def baseStart_661650 : Nat := 118140960795 + 661650 * 2 ^ 59
def prefixEnd_661650 : Nat := 4983230072969 + 3 ^ 40 * 661650 * 2
def baseEnd_661650 : Nat := 37749386116382391670237

theorem tailTrace_661650 : CollatzResearch.WordTrace tailWord_661650 prefixEnd_661650 37749386116382391670237 := by
  unfold tailWord_661650
  simp only [CollatzResearch.WordTrace]
  refine ⟨6033089513240631417163601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16088238701975017112436269 6033089513240631417163601)
  ·
    refine ⟨4524817134930473562872701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6033089513240631417163601 4524817134930473562872701)
    ·
      refine ⟨1696806425598927586077263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4524817134930473562872701 1696806425598927586077263)
      ·
        refine ⟨2545209638398391379115895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1696806425598927586077263 2545209638398391379115895)
        ·
          refine ⟨3817814457597587068673843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2545209638398391379115895 3817814457597587068673843)
          ·
            refine ⟨5726721686396380603010765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3817814457597587068673843 5726721686396380603010765)
            ·
              refine ⟨2147520632398642726129037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5726721686396380603010765 2147520632398642726129037)
              ·
                refine ⟨805320237149491022298389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2147520632398642726129037 805320237149491022298389)
                ·
                  refine ⟨37749386116382391670237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 805320237149491022298389 37749386116382391670237)
                  ·
                    rfl

theorem cell23_661650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_661650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661650 prefixEnd_661650 := by exact prefixLift 661650
  have htrace : WordTrace (prefixWord ++ tailWord_661650) baseStart_661650 baseEnd_661650 := by
    simpa [prefixWord, tailWord_661650, baseEnd_661650] using wordTrace_append hprefix tailTrace_661650
  have hstable : (prefixWord ++ tailWord_661650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661650).length < 2 ^ (prefixWord ++ tailWord_661650).sum := by decide
  have hdescent : baseEnd_661650 < baseStart_661650 := by decide
  rcases family_descends (prefixWord ++ tailWord_661650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661687 : List Nat := [1, 1, 3, 1, 4, 2, 2, 2, 2, 3, 2]
def baseStart_661687 : Nat := 118140960795 + 661687 * 2 ^ 59
def prefixEnd_661687 : Nat := 4983230072969 + 3 ^ 40 * 661687 * 2
def baseEnd_661687 : Nat := 339763473831657880269463

theorem tailTrace_661687 : CollatzResearch.WordTrace tailWord_661687 prefixEnd_661687 339763473831657880269463 := by
  unfold tailWord_661687
  simp only [CollatzResearch.WordTrace]
  refine ⟨24133707553828480987751315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16089138369218987325167543 24133707553828480987751315)
  ·
    refine ⟨36200561330742721481626973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24133707553828480987751315 36200561330742721481626973)
    ·
      refine ⟨13575210499028520555610115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36200561330742721481626973 13575210499028520555610115)
      ·
        refine ⟨20362815748542780833415173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13575210499028520555610115 20362815748542780833415173)
        ·
          refine ⟨3818027952851771406265345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20362815748542780833415173 3818027952851771406265345)
          ·
            refine ⟨2863520964638828554699009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3818027952851771406265345 2863520964638828554699009)
            ·
              refine ⟨2147640723479121416024257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2863520964638828554699009 2147640723479121416024257)
              ·
                refine ⟨1610730542609341062018193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2147640723479121416024257 1610730542609341062018193)
                ·
                  refine ⟨1208047906957005796513645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1610730542609341062018193 1208047906957005796513645)
                  ·
                    refine ⟨453017965108877173692617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1208047906957005796513645 453017965108877173692617)
                    ·
                      refine ⟨339763473831657880269463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 453017965108877173692617 339763473831657880269463)
                      ·
                        rfl

theorem cell23_661687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 2, 3, 2].length) (baseStart_661687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661687 prefixEnd_661687 := by exact prefixLift 661687
  have htrace : WordTrace (prefixWord ++ tailWord_661687) baseStart_661687 baseEnd_661687 := by
    simpa [prefixWord, tailWord_661687, baseEnd_661687] using wordTrace_append hprefix tailTrace_661687
  have hstable : (prefixWord ++ tailWord_661687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661687).length < 2 ^ (prefixWord ++ tailWord_661687).sum := by decide
  have hdescent : baseEnd_661687 < baseStart_661687 := by decide
  rcases family_descends (prefixWord ++ tailWord_661687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661693 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 5, 6]
def baseStart_661693 : Nat := 118140960795 + 661693 * 2 ^ 59
def prefixEnd_661693 : Nat := 4983230072969 + 3 ^ 40 * 661693 * 2
def baseEnd_661693 : Nat := 113255518238528285598145

theorem tailTrace_661693 : CollatzResearch.WordTrace tailWord_661693 prefixEnd_661693 113255518238528285598145 := by
  unfold tailWord_661693
  simp only [CollatzResearch.WordTrace]
  refine ⟨24133926391806744012469733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16089284261204496008313155 24133926391806744012469733)
  ·
    refine ⟨4525111198463764502338075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24133926391806744012469733 4525111198463764502338075)
    ·
      refine ⟨6787666797695646753507113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4525111198463764502338075 6787666797695646753507113)
      ·
        refine ⟨5090750098271735065130335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6787666797695646753507113 5090750098271735065130335)
        ·
          refine ⟨7636125147407602597695503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5090750098271735065130335 7636125147407602597695503)
          ·
            refine ⟨11454187721111403896543255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7636125147407602597695503 11454187721111403896543255)
            ·
              refine ⟨17181281581667105844814883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11454187721111403896543255 17181281581667105844814883)
              ·
                refine ⟨25771922372500658767222325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17181281581667105844814883 25771922372500658767222325)
                ·
                  refine ⟨2416117722421936759427093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25771922372500658767222325 2416117722421936759427093)
                  ·
                    refine ⟨113255518238528285598145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2416117722421936759427093 113255518238528285598145)
                    ·
                      rfl

theorem cell23_661693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_661693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661693 prefixEnd_661693 := by exact prefixLift 661693
  have htrace : WordTrace (prefixWord ++ tailWord_661693) baseStart_661693 baseEnd_661693 := by
    simpa [prefixWord, tailWord_661693, baseEnd_661693] using wordTrace_append hprefix tailTrace_661693
  have hstable : (prefixWord ++ tailWord_661693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661693).length < 2 ^ (prefixWord ++ tailWord_661693).sum := by decide
  have hdescent : baseEnd_661693 < baseStart_661693 := by decide
  rcases family_descends (prefixWord ++ tailWord_661693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661710 : List Nat := [4, 1, 1, 1, 4, 1, 1, 3, 1, 6]
def baseStart_661710 : Nat := 118140960795 + 661710 * 2 ^ 59
def prefixEnd_661710 : Nat := 4983230072969 + 3 ^ 40 * 661710 * 2
def baseEnd_661710 : Nat := 113258427962237096760619

theorem tailTrace_661710 : CollatzResearch.WordTrace tailWord_661710 prefixEnd_661710 113258427962237096760619 := by
  unfold tailWord_661710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3016818304093144489479823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16089697621830103943892389 3016818304093144489479823)
  ·
    refine ⟨4525227456139716734219735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3016818304093144489479823 4525227456139716734219735)
    ·
      refine ⟨6787841184209575101329603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4525227456139716734219735 6787841184209575101329603)
      ·
        refine ⟨10181761776314362651994405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6787841184209575101329603 10181761776314362651994405)
        ·
          refine ⟨1909080333058942997248951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10181761776314362651994405 1909080333058942997248951)
          ·
            refine ⟨2863620499588414495873427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1909080333058942997248951 2863620499588414495873427)
            ·
              refine ⟨4295430749382621743810141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2863620499588414495873427 4295430749382621743810141)
              ·
                refine ⟨1610786531018483153928803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4295430749382621743810141 1610786531018483153928803)
                ·
                  refine ⟨2416179796527724730893205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1610786531018483153928803 2416179796527724730893205)
                  ·
                    refine ⟨113258427962237096760619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2416179796527724730893205 113258427962237096760619)
                    ·
                      rfl

theorem cell23_661710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_661710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661710 prefixEnd_661710 := by exact prefixLift 661710
  have htrace : WordTrace (prefixWord ++ tailWord_661710) baseStart_661710 baseEnd_661710 := by
    simpa [prefixWord, tailWord_661710, baseEnd_661710] using wordTrace_append hprefix tailTrace_661710
  have hstable : (prefixWord ++ tailWord_661710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661710).length < 2 ^ (prefixWord ++ tailWord_661710).sum := by decide
  have hdescent : baseEnd_661710 < baseStart_661710 := by decide
  rcases family_descends (prefixWord ++ tailWord_661710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661713 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 6]
def baseStart_661713 : Nat := 118140960795 + 661713 * 2 ^ 59
def prefixEnd_661713 : Nat := 4983230072969 + 3 ^ 40 * 661713 * 2
def baseEnd_661713 : Nat := 339776824328674778544343

theorem tailTrace_661713 : CollatzResearch.WordTrace tailWord_661713 prefixEnd_661713 339776824328674778544343 := by
  unfold tailWord_661713
  simp only [CollatzResearch.WordTrace]
  refine ⟨24134655851734287428197793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16089770567822858285465195 24134655851734287428197793)
  ·
    refine ⟨18100991888800715571148345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24134655851734287428197793 18100991888800715571148345)
    ·
      refine ⟨13575743916600536678361259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18100991888800715571148345 13575743916600536678361259)
      ·
        refine ⟨20363615874900805017541889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13575743916600536678361259 20363615874900805017541889)
        ·
          refine ⟨15272711906175603763156417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20363615874900805017541889 15272711906175603763156417)
          ·
            refine ⟨11454533929631702822367313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15272711906175603763156417 11454533929631702822367313)
            ·
              refine ⟨8590900447223777116775485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11454533929631702822367313 8590900447223777116775485)
              ·
                refine ⟨3221587667708916418790807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8590900447223777116775485 3221587667708916418790807)
                ·
                  refine ⟨4832381501563374628186211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3221587667708916418790807 4832381501563374628186211)
                  ·
                    refine ⟨7248572252345061942279317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4832381501563374628186211 7248572252345061942279317)
                    ·
                      refine ⟨339776824328674778544343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7248572252345061942279317 339776824328674778544343)
                      ·
                        rfl

theorem cell23_661713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_661713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661713 prefixEnd_661713 := by exact prefixLift 661713
  have htrace : WordTrace (prefixWord ++ tailWord_661713) baseStart_661713 baseEnd_661713 := by
    simpa [prefixWord, tailWord_661713, baseEnd_661713] using wordTrace_append hprefix tailTrace_661713
  have hstable : (prefixWord ++ tailWord_661713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661713).length < 2 ^ (prefixWord ++ tailWord_661713).sum := by decide
  have hdescent : baseEnd_661713 < baseStart_661713 := by decide
  rcases family_descends (prefixWord ++ tailWord_661713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661731 : List Nat := [1, 1, 1, 8, 1, 2, 2, 1, 1, 5]
def baseStart_661731 : Nat := 118140960795 + 661731 * 2 ^ 59
def prefixEnd_661731 : Nat := 4983230072969 + 3 ^ 40 * 661731 * 2
def baseEnd_661731 : Nat := 113262022326818569373087

theorem tailTrace_661731 : CollatzResearch.WordTrace tailWord_661731 prefixEnd_661731 113262022326818569373087 := by
  unfold tailWord_661731
  simp only [CollatzResearch.WordTrace]
  refine ⟨24135312365669076502353047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16090208243779384334902031 24135312365669076502353047)
  ·
    refine ⟨36202968548503614753529571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24135312365669076502353047 36202968548503614753529571)
    ·
      refine ⟨54304452822755422130294357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36202968548503614753529571 54304452822755422130294357)
      ·
        refine ⟨636380306516665103089387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 54304452822755422130294357 636380306516665103089387)
        ·
          refine ⟨954570459774997654634081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636380306516665103089387 954570459774997654634081)
          ·
            refine ⟨715927844831248240975561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954570459774997654634081 715927844831248240975561)
            ·
              refine ⟨536945883623436180731671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 715927844831248240975561 536945883623436180731671)
              ·
                refine ⟨805418825435154271097507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536945883623436180731671 805418825435154271097507)
                ·
                  refine ⟨1208128238152731406646261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 805418825435154271097507 1208128238152731406646261)
                  ·
                    refine ⟨113262022326818569373087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1208128238152731406646261 113262022326818569373087)
                    ·
                      rfl

theorem cell23_661731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 2, 1, 1, 5].length) (baseStart_661731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661731 prefixEnd_661731 := by exact prefixLift 661731
  have htrace : WordTrace (prefixWord ++ tailWord_661731) baseStart_661731 baseEnd_661731 := by
    simpa [prefixWord, tailWord_661731, baseEnd_661731] using wordTrace_append hprefix tailTrace_661731
  have hstable : (prefixWord ++ tailWord_661731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661731).length < 2 ^ (prefixWord ++ tailWord_661731).sum := by decide
  have hdescent : baseEnd_661731 < baseStart_661731 := by decide
  rcases family_descends (prefixWord ++ tailWord_661731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661753 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 2, 7]
def baseStart_661753 : Nat := 118140960795 + 661753 * 2 ^ 59
def prefixEnd_661753 : Nat := 4983230072969 + 3 ^ 40 * 661753 * 2
def baseEnd_661753 : Nat := 113265787851618207348053

theorem tailTrace_661753 : CollatzResearch.WordTrace tailWord_661753 prefixEnd_661753 113265787851618207348053 := by
  unfold tailWord_661753
  simp only [CollatzResearch.WordTrace]
  refine ⟨24136114771589374259653913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16090743181059582839769275 24136114771589374259653913)
  ·
    refine ⟨18102086078692030694740435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24136114771589374259653913 18102086078692030694740435)
    ·
      refine ⟨27153129118038046042110653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18102086078692030694740435 27153129118038046042110653)
      ·
        refine ⟨10182423419264267265791495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27153129118038046042110653 10182423419264267265791495)
        ·
          refine ⟨15273635128896400898687243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10182423419264267265791495 15273635128896400898687243)
          ·
            refine ⟨22910452693344601348030865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15273635128896400898687243 22910452693344601348030865)
            ·
              refine ⟨17182839520008451011023149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22910452693344601348030865 17182839520008451011023149)
              ·
                refine ⟨6443564820003169129133681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17182839520008451011023149 6443564820003169129133681)
                ·
                  refine ⟨4832673615002376846850261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6443564820003169129133681 4832673615002376846850261)
                  ·
                    refine ⟨113265787851618207348053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4832673615002376846850261 113265787851618207348053)
                    ·
                      rfl

theorem cell23_661753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 2, 7].length) (baseStart_661753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661753 prefixEnd_661753 := by exact prefixLift 661753
  have htrace : WordTrace (prefixWord ++ tailWord_661753) baseStart_661753 baseEnd_661753 := by
    simpa [prefixWord, tailWord_661753, baseEnd_661753] using wordTrace_append hprefix tailTrace_661753
  have hstable : (prefixWord ++ tailWord_661753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661753).length < 2 ^ (prefixWord ++ tailWord_661753).sum := by decide
  have hdescent : baseEnd_661753 < baseStart_661753 := by decide
  rcases family_descends (prefixWord ++ tailWord_661753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661764 : List Nat := [2, 3, 2, 2, 3, 2, 1, 1, 1, 2, 4]
def baseStart_661764 : Nat := 118140960795 + 661764 * 2 ^ 59
def prefixEnd_661764 : Nat := 4983230072969 + 3 ^ 40 * 661764 * 2
def baseEnd_661764 : Nat := 339803011842054079006609

theorem tailTrace_661764 : CollatzResearch.WordTrace tailWord_661764 prefixEnd_661764 339803011842054079006609 := by
  unfold tailWord_661764
  simp only [CollatzResearch.WordTrace]
  refine ⟨12068257987274761569152173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16091010649699682092202897 12068257987274761569152173)
  ·
    refine ⟨4525596745228035588432065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12068257987274761569152173 4525596745228035588432065)
    ·
      refine ⟨3394197558921026691324049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4525596745228035588432065 3394197558921026691324049)
      ·
        refine ⟨2545648169190770018493037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3394197558921026691324049 2545648169190770018493037)
        ·
          refine ⟨954618063446538756934889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2545648169190770018493037 954618063446538756934889)
          ·
            refine ⟨715963547584904067701167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954618063446538756934889 715963547584904067701167)
            ·
              refine ⟨1073945321377356101551751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715963547584904067701167 1073945321377356101551751)
              ·
                refine ⟨1610917982066034152327627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1073945321377356101551751 1610917982066034152327627)
                ·
                  refine ⟨2416376973099051228491441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1610917982066034152327627 2416376973099051228491441)
                  ·
                    refine ⟨1812282729824288421368581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2416376973099051228491441 1812282729824288421368581)
                    ·
                      refine ⟨339803011842054079006609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1812282729824288421368581 339803011842054079006609)
                      ·
                        rfl

theorem cell23_661764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_661764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661764 prefixEnd_661764 := by exact prefixLift 661764
  have htrace : WordTrace (prefixWord ++ tailWord_661764) baseStart_661764 baseEnd_661764 := by
    simpa [prefixWord, tailWord_661764, baseEnd_661764] using wordTrace_append hprefix tailTrace_661764
  have hstable : (prefixWord ++ tailWord_661764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661764).length < 2 ^ (prefixWord ++ tailWord_661764).sum := by decide
  have hdescent : baseEnd_661764 < baseStart_661764 := by decide
  rcases family_descends (prefixWord ++ tailWord_661764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661820 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_661820 : Nat := 118140960795 + 661820 * 2 ^ 59
def prefixEnd_661820 : Nat := 4983230072969 + 3 ^ 40 * 661820 * 2
def baseEnd_661820 : Nat := 339831766758705859906351

theorem tailTrace_661820 : CollatzResearch.WordTrace tailWord_661820 prefixEnd_661820 339831766758705859906351 := by
  unfold tailWord_661820
  simp only [CollatzResearch.WordTrace]
  refine ⟨12069279231173322351171457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16092372308231096468228609 12069279231173322351171457)
  ·
    refine ⟨9051959423379991763378593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12069279231173322351171457 9051959423379991763378593)
    ·
      refine ⟨6788969567534993822533945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9051959423379991763378593 6788969567534993822533945)
      ·
        refine ⟨5091727175651245366900459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6788969567534993822533945 5091727175651245366900459)
        ·
          refine ⟨7637590763476868050350689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5091727175651245366900459 7637590763476868050350689)
          ·
            refine ⟨5728193072607651037763017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7637590763476868050350689 5728193072607651037763017)
            ·
              refine ⟨4296144804455738278322263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5728193072607651037763017 4296144804455738278322263)
              ·
                refine ⟨6444217206683607417483395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4296144804455738278322263 6444217206683607417483395)
                ·
                  refine ⟨9666325810025411126225093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6444217206683607417483395 9666325810025411126225093)
                  ·
                    refine ⟨1812436089379764586167205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9666325810025411126225093 1812436089379764586167205)
                    ·
                      refine ⟨339831766758705859906351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1812436089379764586167205 339831766758705859906351)
                      ·
                        rfl

theorem cell23_661820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_661820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661820 prefixEnd_661820 := by exact prefixLift 661820
  have htrace : WordTrace (prefixWord ++ tailWord_661820) baseStart_661820 baseEnd_661820 := by
    simpa [prefixWord, tailWord_661820, baseEnd_661820] using wordTrace_append hprefix tailTrace_661820
  have hstable : (prefixWord ++ tailWord_661820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661820).length < 2 ^ (prefixWord ++ tailWord_661820).sum := by decide
  have hdescent : baseEnd_661820 < baseStart_661820 := by decide
  rcases family_descends (prefixWord ++ tailWord_661820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661847 : List Nat := [1, 1, 3, 2, 3, 1, 2, 5, 5]
def baseStart_661847 : Nat := 118140960795 + 661847 * 2 ^ 59
def prefixEnd_661847 : Nat := 4983230072969 + 3 ^ 40 * 661847 * 2
def baseEnd_661847 : Nat := 37760625637375250474303

theorem tailTrace_661847 : CollatzResearch.WordTrace tailWord_661847 prefixEnd_661847 37760625637375250474303 := by
  unfold tailWord_661847
  simp only [CollatzResearch.WordTrace]
  refine ⟨24139543233248828313575795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16093028822165885542383863 24139543233248828313575795)
  ·
    refine ⟨36209314849873242470363693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24139543233248828313575795 36209314849873242470363693)
    ·
      refine ⟨13578493068702465926386385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36209314849873242470363693 13578493068702465926386385)
      ·
        refine ⟨10183869801526849444789789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13578493068702465926386385 10183869801526849444789789)
        ·
          refine ⟨3818951175572568541796171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10183869801526849444789789 3818951175572568541796171)
          ·
            refine ⟨5728426763358852812694257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3818951175572568541796171 5728426763358852812694257)
            ·
              refine ⟨4296320072519139609520693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5728426763358852812694257 4296320072519139609520693)
              ·
                refine ⟨402780006798669338392565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4296320072519139609520693 402780006798669338392565)
                ·
                  refine ⟨37760625637375250474303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 402780006798669338392565 37760625637375250474303)
                  ·
                    rfl

theorem cell23_661847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 5, 5].length) (baseStart_661847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661847 prefixEnd_661847 := by exact prefixLift 661847
  have htrace : WordTrace (prefixWord ++ tailWord_661847) baseStart_661847 baseEnd_661847 := by
    simpa [prefixWord, tailWord_661847, baseEnd_661847] using wordTrace_append hprefix tailTrace_661847
  have hstable : (prefixWord ++ tailWord_661847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661847).length < 2 ^ (prefixWord ++ tailWord_661847).sum := by decide
  have hdescent : baseEnd_661847 < baseStart_661847 := by decide
  rcases family_descends (prefixWord ++ tailWord_661847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661858 : List Nat := [3, 3, 2, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_661858 : Nat := 118140960795 + 661858 * 2 ^ 59
def prefixEnd_661858 : Nat := 4983230072969 + 3 ^ 40 * 661858 * 2
def baseEnd_661858 : Nat := 339851279023576711231177

theorem tailTrace_661858 : CollatzResearch.WordTrace tailWord_661858 prefixEnd_661858 339851279023576711231177 := by
  unfold tailWord_661858
  simp only [CollatzResearch.WordTrace]
  refine ⟨6034986109052244298056557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16093296290805984794817485 6034986109052244298056557)
  ·
    refine ⟨2263119790894591611771209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6034986109052244298056557 2263119790894591611771209)
    ·
      refine ⟨1697339843170943708828407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2263119790894591611771209 1697339843170943708828407)
      ·
        refine ⟨2546009764756415563242611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1697339843170943708828407 2546009764756415563242611)
        ·
          refine ⟨3819014647134623344863917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2546009764756415563242611 3819014647134623344863917)
          ·
            refine ⟨1432130492675483754323969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3819014647134623344863917 1432130492675483754323969)
            ·
              refine ⟨1074097869506612815742977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1432130492675483754323969 1074097869506612815742977)
              ·
                refine ⟨805573402129959611807233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1074097869506612815742977 805573402129959611807233)
                ·
                  refine ⟨604180051597469708855425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 805573402129959611807233 604180051597469708855425)
                  ·
                    refine ⟨453135038698102281641569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 604180051597469708855425 453135038698102281641569)
                    ·
                      refine ⟨339851279023576711231177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 453135038698102281641569 339851279023576711231177)
                      ·
                        rfl

theorem cell23_661858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_661858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661858 prefixEnd_661858 := by exact prefixLift 661858
  have htrace : WordTrace (prefixWord ++ tailWord_661858) baseStart_661858 baseEnd_661858 := by
    simpa [prefixWord, tailWord_661858, baseEnd_661858] using wordTrace_append hprefix tailTrace_661858
  have hstable : (prefixWord ++ tailWord_661858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661858).length < 2 ^ (prefixWord ++ tailWord_661858).sum := by decide
  have hdescent : baseEnd_661858 < baseStart_661858 := by decide
  rcases family_descends (prefixWord ++ tailWord_661858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661864 : List Nat := [2, 1, 4, 2, 2, 2, 1, 4, 5]
def baseStart_661864 : Nat := 118140960795 + 661864 * 2 ^ 59
def prefixEnd_661864 : Nat := 4983230072969 + 3 ^ 40 * 661864 * 2
def baseEnd_661864 : Nat := 37761595545278187528461

theorem tailTrace_661864 : CollatzResearch.WordTrace tailWord_661864 prefixEnd_661864 37761595545278187528461 := by
  unfold tailWord_661864
  simp only [CollatzResearch.WordTrace]
  refine ⟨12070081637093620108472323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16093442182791493477963097 12070081637093620108472323)
  ·
    refine ⟨18105122455640430162708485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12070081637093620108472323 18105122455640430162708485)
    ·
      refine ⟨3394710460432580655507841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18105122455640430162708485 3394710460432580655507841)
      ·
        refine ⟨2546032845324435491630881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3394710460432580655507841 2546032845324435491630881)
        ·
          refine ⟨1909524633993326618723161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2546032845324435491630881 1909524633993326618723161)
          ·
            refine ⟨1432143475494994964042371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1909524633993326618723161 1432143475494994964042371)
            ·
              refine ⟨2148215213242492446063557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1432143475494994964042371 2148215213242492446063557)
              ·
                refine ⟨402790352482967333636917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2148215213242492446063557 402790352482967333636917)
                ·
                  refine ⟨37761595545278187528461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 402790352482967333636917 37761595545278187528461)
                  ·
                    rfl

theorem cell23_661864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 5].length) (baseStart_661864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661864 prefixEnd_661864 := by exact prefixLift 661864
  have htrace : WordTrace (prefixWord ++ tailWord_661864) baseStart_661864 baseEnd_661864 := by
    simpa [prefixWord, tailWord_661864, baseEnd_661864] using wordTrace_append hprefix tailTrace_661864
  have hstable : (prefixWord ++ tailWord_661864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661864).length < 2 ^ (prefixWord ++ tailWord_661864).sum := by decide
  have hdescent : baseEnd_661864 < baseStart_661864 := by decide
  rcases family_descends (prefixWord ++ tailWord_661864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661897 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 1, 3, 4]
def baseStart_661897 : Nat := 118140960795 + 661897 * 2 ^ 59
def prefixEnd_661897 : Nat := 4983230072969 + 3 ^ 40 * 661897 * 2
def baseEnd_661897 : Nat := 339871304769102058643497

theorem tailTrace_661897 : CollatzResearch.WordTrace tailWord_661897 prefixEnd_661897 339871304769102058643497 := by
  unfold tailWord_661897
  simp only [CollatzResearch.WordTrace]
  refine ⟨24141366883067686852895945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16094244588711791235263963 24141366883067686852895945)
  ·
    refine ⟨18106025162300765139671959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24141366883067686852895945 18106025162300765139671959)
    ·
      refine ⟨27159037743451147709507939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18106025162300765139671959 27159037743451147709507939)
      ·
        refine ⟨40738556615176721564261909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27159037743451147709507939 40738556615176721564261909)
        ·
          refine ⟨1909619841336408823324777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40738556615176721564261909 1909619841336408823324777)
          ·
            refine ⟨1432214881002306617493583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1909619841336408823324777 1432214881002306617493583)
            ·
              refine ⟨2148322321503459926240375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1432214881002306617493583 2148322321503459926240375)
              ·
                refine ⟨3222483482255189889360563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2148322321503459926240375 3222483482255189889360563)
                ·
                  refine ⟨4833725223382784834040845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3222483482255189889360563 4833725223382784834040845)
                  ·
                    refine ⟨1812646958768544312765317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4833725223382784834040845 1812646958768544312765317)
                    ·
                      refine ⟨339871304769102058643497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1812646958768544312765317 339871304769102058643497)
                      ·
                        rfl

theorem cell23_661897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 3, 4].length) (baseStart_661897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661897 prefixEnd_661897 := by exact prefixLift 661897
  have htrace : WordTrace (prefixWord ++ tailWord_661897) baseStart_661897 baseEnd_661897 := by
    simpa [prefixWord, tailWord_661897, baseEnd_661897] using wordTrace_append hprefix tailTrace_661897
  have hstable : (prefixWord ++ tailWord_661897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661897).length < 2 ^ (prefixWord ++ tailWord_661897).sum := by decide
  have hdescent : baseEnd_661897 < baseStart_661897 := by decide
  rcases family_descends (prefixWord ++ tailWord_661897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_661914 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2]
def baseStart_661914 : Nat := 118140960795 + 661914 * 2 ^ 59
def prefixEnd_661914 : Nat := 4983230072969 + 3 ^ 40 * 661914 * 2
def baseEnd_661914 : Nat := 339880033940228492130919

theorem tailTrace_661914 : CollatzResearch.WordTrace tailWord_661914 prefixEnd_661914 339880033940228492130919 := by
  unfold tailWord_661914
  simp only [CollatzResearch.WordTrace]
  refine ⟨6035496731001524689066199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16094657949337399170843197 6035496731001524689066199)
  ·
    refine ⟨9053245096502287033599299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6035496731001524689066199 9053245096502287033599299)
    ·
      refine ⟨13579867644753430550398949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9053245096502287033599299 13579867644753430550398949)
      ·
        refine ⟨2546225183391268228199803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13579867644753430550398949 2546225183391268228199803)
        ·
          refine ⟨3819337775086902342299705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2546225183391268228199803 3819337775086902342299705)
          ·
            refine ⟨2864503331315176756724779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3819337775086902342299705 2864503331315176756724779)
            ·
              refine ⟨4296754996972765135087169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2864503331315176756724779 4296754996972765135087169)
              ·
                refine ⟨3222566247729573851315377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4296754996972765135087169 3222566247729573851315377)
                ·
                  refine ⟨2416924685797180388486533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3222566247729573851315377 2416924685797180388486533)
                  ·
                    refine ⟨453173378586971322841225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2416924685797180388486533 453173378586971322841225)
                    ·
                      refine ⟨339880033940228492130919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 453173378586971322841225 339880033940228492130919)
                      ·
                        rfl

theorem cell23_661914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_661914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_661914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_661914 prefixEnd_661914 := by exact prefixLift 661914
  have htrace : WordTrace (prefixWord ++ tailWord_661914) baseStart_661914 baseEnd_661914 := by
    simpa [prefixWord, tailWord_661914, baseEnd_661914] using wordTrace_append hprefix tailTrace_661914
  have hstable : (prefixWord ++ tailWord_661914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_661914).length < 2 ^ (prefixWord ++ tailWord_661914).sum := by decide
  have hdescent : baseEnd_661914 < baseStart_661914 := by decide
  rcases family_descends (prefixWord ++ tailWord_661914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662044 : List Nat := [2, 2, 3, 1, 2, 4, 1, 8]
def baseStart_662044 : Nat := 118140960795 + 662044 * 2 ^ 59
def prefixEnd_662044 : Nat := 4983230072969 + 3 ^ 40 * 662044 * 2
def baseEnd_662044 : Nat := 12590621719456036426123

theorem tailTrace_662044 : CollatzResearch.WordTrace tailWord_662044 prefixEnd_662044 12590621719456036426123 := by
  unfold tailWord_662044
  simp only [CollatzResearch.WordTrace]
  refine ⟨12073364206767565479248593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16097818942356753972331457 12073364206767565479248593)
  ·
    refine ⟨9055023155075674109436445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12073364206767565479248593 9055023155075674109436445)
    ·
      refine ⟨3395633683153377791038667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9055023155075674109436445 3395633683153377791038667)
      ·
        refine ⟨5093450524730066686558001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3395633683153377791038667 5093450524730066686558001)
        ·
          refine ⟨3820087893547550014918501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5093450524730066686558001 3820087893547550014918501)
          ·
            refine ⟨716266480040165627797219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3820087893547550014918501 716266480040165627797219)
            ·
              refine ⟨1074399720060248441695829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716266480040165627797219 1074399720060248441695829)
              ·
                refine ⟨12590621719456036426123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1074399720060248441695829 12590621719456036426123)
                ·
                  rfl

theorem cell23_662044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 8].length) (baseStart_662044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662044 prefixEnd_662044 := by exact prefixLift 662044
  have htrace : WordTrace (prefixWord ++ tailWord_662044) baseStart_662044 baseEnd_662044 := by
    simpa [prefixWord, tailWord_662044, baseEnd_662044] using wordTrace_append hprefix tailTrace_662044
  have hstable : (prefixWord ++ tailWord_662044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662044).length < 2 ^ (prefixWord ++ tailWord_662044).sum := by decide
  have hdescent : baseEnd_662044 < baseStart_662044 := by decide
  rcases family_descends (prefixWord ++ tailWord_662044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662067 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 5]
def baseStart_662067 : Nat := 118140960795 + 662067 * 2 ^ 59
def prefixEnd_662067 : Nat := 4983230072969 + 3 ^ 40 * 662067 * 2
def baseEnd_662067 : Nat := 339958596480366393517715

theorem tailTrace_662067 : CollatzResearch.WordTrace tailWord_662067 prefixEnd_662067 339958596480366393517715 := by
  unfold tailWord_662067
  simp only [CollatzResearch.WordTrace]
  refine ⟨24147567292451805886584455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16098378194967870591056303 24147567292451805886584455)
  ·
    refine ⟨36221350938677708829876683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24147567292451805886584455 36221350938677708829876683)
    ·
      refine ⟨54332026408016563244815025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36221350938677708829876683 54332026408016563244815025)
      ·
        refine ⟨40749019806012422433611269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54332026408016563244815025 40749019806012422433611269)
        ·
          refine ⟨7640441213627329206302113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40749019806012422433611269 7640441213627329206302113)
          ·
            refine ⟨5730330910220496904726585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7640441213627329206302113 5730330910220496904726585)
            ·
              refine ⟨4297748182665372678544939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5730330910220496904726585 4297748182665372678544939)
              ·
                refine ⟨6446622273998059017817409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4297748182665372678544939 6446622273998059017817409)
                ·
                  refine ⟨4834966705498544263363057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6446622273998059017817409 4834966705498544263363057)
                  ·
                    refine ⟨3626225029123908197522293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4834966705498544263363057 3626225029123908197522293)
                    ·
                      refine ⟨339958596480366393517715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3626225029123908197522293 339958596480366393517715)
                      ·
                        rfl

theorem cell23_662067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_662067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662067 prefixEnd_662067 := by exact prefixLift 662067
  have htrace : WordTrace (prefixWord ++ tailWord_662067) baseStart_662067 baseEnd_662067 := by
    simpa [prefixWord, tailWord_662067, baseEnd_662067] using wordTrace_append hprefix tailTrace_662067
  have hstable : (prefixWord ++ tailWord_662067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662067).length < 2 ^ (prefixWord ++ tailWord_662067).sum := by decide
  have hdescent : baseEnd_662067 < baseStart_662067 := by decide
  rcases family_descends (prefixWord ++ tailWord_662067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662162 : List Nat := [3, 2, 3, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_662162 : Nat := 118140960795 + 662162 * 2 ^ 59
def prefixEnd_662162 : Nat := 4983230072969 + 3 ^ 40 * 662162 * 2
def baseEnd_662162 : Nat := 340007377142543521829779

theorem tailTrace_662162 : CollatzResearch.WordTrace tailWord_662162 prefixEnd_662162 340007377142543521829779 := by
  unfold tailWord_662162
  simp only [CollatzResearch.WordTrace]
  refine ⟨6037758056776909277823185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16100688151405091407528493 6037758056776909277823185)
  ·
    refine ⟨4528318542582681958367389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6037758056776909277823185 4528318542582681958367389)
    ·
      refine ⟨1698119453468505734387771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4528318542582681958367389 1698119453468505734387771)
      ·
        refine ⟨2547179180202758601581657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1698119453468505734387771 2547179180202758601581657)
        ·
          refine ⟨1910384385152068951186243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2547179180202758601581657 1910384385152068951186243)
          ·
            refine ⟨2865576577728103426779365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1910384385152068951186243 2865576577728103426779365)
            ·
              refine ⟨537295608324019392521131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2865576577728103426779365 537295608324019392521131)
              ·
                refine ⟨805943412486029088781697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537295608324019392521131 805943412486029088781697)
                ·
                  refine ⟨604457559364521816586273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 805943412486029088781697 604457559364521816586273)
                  ·
                    refine ⟨453343169523391362439705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 604457559364521816586273 453343169523391362439705)
                    ·
                      refine ⟨340007377142543521829779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 453343169523391362439705 340007377142543521829779)
                      ·
                        rfl

theorem cell23_662162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_662162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662162 prefixEnd_662162 := by exact prefixLift 662162
  have htrace : WordTrace (prefixWord ++ tailWord_662162) baseStart_662162 baseEnd_662162 := by
    simpa [prefixWord, tailWord_662162, baseEnd_662162] using wordTrace_append hprefix tailTrace_662162
  have hstable : (prefixWord ++ tailWord_662162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662162).length < 2 ^ (prefixWord ++ tailWord_662162).sum := by decide
  have hdescent : baseEnd_662162 < baseStart_662162 := by decide
  rcases family_descends (prefixWord ++ tailWord_662162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662201 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 2, 4, 2]
def baseStart_662201 : Nat := 118140960795 + 662201 * 2 ^ 59
def prefixEnd_662201 : Nat := 4983230072969 + 3 ^ 40 * 662201 * 2
def baseEnd_662201 : Nat := 340027402888068869242099

theorem tailTrace_662201 : CollatzResearch.WordTrace tailWord_662201 prefixEnd_662201 340027402888068869242099 := by
  unfold tailWord_662201
  simp only [CollatzResearch.WordTrace]
  refine ⟨24152454673966346771962457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16101636449310897847974971 24152454673966346771962457)
  ·
    refine ⟨18114341005474760078971843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24152454673966346771962457 18114341005474760078971843)
    ·
      refine ⟨27171511508212140118457765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18114341005474760078971843 27171511508212140118457765)
      ·
        refine ⟨5094658407789776272210831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27171511508212140118457765 5094658407789776272210831)
        ·
          refine ⟨7641987611684664408316247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5094658407789776272210831 7641987611684664408316247)
          ·
            refine ⟨11462981417526996612474371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7641987611684664408316247 11462981417526996612474371)
            ·
              refine ⟨17194472126290494918711557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11462981417526996612474371 17194472126290494918711557)
              ·
                refine ⟨3223963523679467797258417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17194472126290494918711557 3223963523679467797258417)
                ·
                  refine ⟨2417972642759600847943813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3223963523679467797258417 2417972642759600847943813)
                  ·
                    refine ⟨453369870517425158989465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2417972642759600847943813 453369870517425158989465)
                    ·
                      refine ⟨340027402888068869242099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 453369870517425158989465 340027402888068869242099)
                      ·
                        rfl

theorem cell23_662201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_662201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662201 prefixEnd_662201 := by exact prefixLift 662201
  have htrace : WordTrace (prefixWord ++ tailWord_662201) baseStart_662201 baseEnd_662201 := by
    simpa [prefixWord, tailWord_662201, baseEnd_662201] using wordTrace_append hprefix tailTrace_662201
  have hstable : (prefixWord ++ tailWord_662201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662201).length < 2 ^ (prefixWord ++ tailWord_662201).sum := by decide
  have hdescent : baseEnd_662201 < baseStart_662201 := by decide
  rcases family_descends (prefixWord ++ tailWord_662201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662204 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_662204 : Nat := 118140960795 + 662204 * 2 ^ 59
def prefixEnd_662204 : Nat := 4983230072969 + 3 ^ 40 * 662204 * 2
def baseEnd_662204 : Nat := 340028943330032357504585

theorem tailTrace_662204 : CollatzResearch.WordTrace tailWord_662204 prefixEnd_662204 340028943330032357504585 := by
  unfold tailWord_662204
  simp only [CollatzResearch.WordTrace]
  refine ⟨12076282046477739142160833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16101709395303652189547777 12076282046477739142160833)
  ·
    refine ⟨9057211534858304356620625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12076282046477739142160833 9057211534858304356620625)
    ·
      refine ⟨6792908651143728267465469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9057211534858304356620625 6792908651143728267465469)
      ·
        refine ⟨2547340744178898100299551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6792908651143728267465469 2547340744178898100299551)
        ·
          refine ⟨3821011116268347150449327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2547340744178898100299551 3821011116268347150449327)
          ·
            refine ⟨5731516674402520725673991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3821011116268347150449327 5731516674402520725673991)
            ·
              refine ⟨8597275011603781088510987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5731516674402520725673991 8597275011603781088510987)
              ·
                refine ⟨12895912517405671632766481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8597275011603781088510987 12895912517405671632766481)
                ·
                  refine ⟨9671934388054253724574861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12895912517405671632766481 9671934388054253724574861)
                  ·
                    refine ⟨3626975395520345146715573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9671934388054253724574861 3626975395520345146715573)
                    ·
                      refine ⟨340028943330032357504585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3626975395520345146715573 340028943330032357504585)
                      ·
                        rfl

theorem cell23_662204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_662204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662204 prefixEnd_662204 := by exact prefixLift 662204
  have htrace : WordTrace (prefixWord ++ tailWord_662204) baseStart_662204 baseEnd_662204 := by
    simpa [prefixWord, tailWord_662204, baseEnd_662204] using wordTrace_append hprefix tailTrace_662204
  have hstable : (prefixWord ++ tailWord_662204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662204).length < 2 ^ (prefixWord ++ tailWord_662204).sum := by decide
  have hdescent : baseEnd_662204 < baseStart_662204 := by decide
  rcases family_descends (prefixWord ++ tailWord_662204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662218 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 2, 4, 2]
def baseStart_662218 : Nat := 118140960795 + 662218 * 2 ^ 59
def prefixEnd_662218 : Nat := 4983230072969 + 3 ^ 40 * 662218 * 2
def baseEnd_662218 : Nat := 340036132059195302729521

theorem tailTrace_662218 : CollatzResearch.WordTrace tailWord_662218 prefixEnd_662218 340036132059195302729521 := by
  unfold tailWord_662218
  simp only [CollatzResearch.WordTrace]
  refine ⟨6038268678726189668832827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16102049809936505783554205 6038268678726189668832827)
  ·
    refine ⟨9057403018089284503249241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6038268678726189668832827 9057403018089284503249241)
    ·
      refine ⟨6793052263566963377436931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9057403018089284503249241 6793052263566963377436931)
      ·
        refine ⟨10189578395350445066155397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6793052263566963377436931 10189578395350445066155397)
        ·
          refine ⟨1910545949128208449904137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10189578395350445066155397 1910545949128208449904137)
          ·
            refine ⟨1432909461846156337428103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1910545949128208449904137 1432909461846156337428103)
            ·
              refine ⟨2149364192769234506142155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1432909461846156337428103 2149364192769234506142155)
              ·
                refine ⟨3224046289153851759213233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2149364192769234506142155 3224046289153851759213233)
                ·
                  refine ⟨2418034716865388819409925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3224046289153851759213233 2418034716865388819409925)
                  ·
                    refine ⟨453381509412260403639361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2418034716865388819409925 453381509412260403639361)
                    ·
                      refine ⟨340036132059195302729521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 453381509412260403639361 340036132059195302729521)
                      ·
                        rfl

theorem cell23_662218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_662218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662218 prefixEnd_662218 := by exact prefixLift 662218
  have htrace : WordTrace (prefixWord ++ tailWord_662218) baseStart_662218 baseEnd_662218 := by
    simpa [prefixWord, tailWord_662218, baseEnd_662218] using wordTrace_append hprefix tailTrace_662218
  have hstable : (prefixWord ++ tailWord_662218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662218).length < 2 ^ (prefixWord ++ tailWord_662218).sum := by decide
  have hdescent : baseEnd_662218 < baseStart_662218 := by decide
  rcases family_descends (prefixWord ++ tailWord_662218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662245 : List Nat := [1, 3, 1, 4, 1, 3, 2, 3, 1, 4]
def baseStart_662245 : Nat := 118140960795 + 662245 * 2 ^ 59
def prefixEnd_662245 : Nat := 4983230072969 + 3 ^ 40 * 662245 * 2
def baseEnd_662245 : Nat := 113349998678955565697299

theorem tailTrace_662245 : CollatzResearch.WordTrace tailWord_662245 prefixEnd_662245 113349998678955565697299 := by
  unfold tailWord_662245
  simp only [CollatzResearch.WordTrace]
  refine ⟨24154059485806942286564189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16102706323871294857709459 24154059485806942286564189)
  ·
    refine ⟨9057772307177603357461571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24154059485806942286564189 9057772307177603357461571)
    ·
      refine ⟨13586658460766405036192357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9057772307177603357461571 13586658460766405036192357)
      ·
        refine ⟨2547498461393700944286067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13586658460766405036192357 2547498461393700944286067)
        ·
          refine ⟨3821247692090551416429101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2547498461393700944286067 3821247692090551416429101)
          ·
            refine ⟨1432967884533956781160913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3821247692090551416429101 1432967884533956781160913)
            ·
              refine ⟨1074725913400467585870685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1432967884533956781160913 1074725913400467585870685)
              ·
                refine ⟨403022217525175344701507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1074725913400467585870685 403022217525175344701507)
                ·
                  refine ⟨604533326287763017052261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403022217525175344701507 604533326287763017052261)
                  ·
                    refine ⟨113349998678955565697299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 604533326287763017052261 113349998678955565697299)
                    ·
                      rfl

theorem cell23_662245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 1, 4].length) (baseStart_662245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662245 prefixEnd_662245 := by exact prefixLift 662245
  have htrace : WordTrace (prefixWord ++ tailWord_662245) baseStart_662245 baseEnd_662245 := by
    simpa [prefixWord, tailWord_662245, baseEnd_662245] using wordTrace_append hprefix tailTrace_662245
  have hstable : (prefixWord ++ tailWord_662245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662245).length < 2 ^ (prefixWord ++ tailWord_662245).sum := by decide
  have hdescent : baseEnd_662245 < baseStart_662245 := by decide
  rcases family_descends (prefixWord ++ tailWord_662245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662251 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 7, 1, 3]
def baseStart_662251 : Nat := 118140960795 + 662251 * 2 ^ 59
def prefixEnd_662251 : Nat := 4983230072969 + 3 ^ 40 * 662251 * 2
def baseEnd_662251 : Nat := 340053076920793673616869

theorem tailTrace_662251 : CollatzResearch.WordTrace tailWord_662251 prefixEnd_662251 340053076920793673616869 := by
  unfold tailWord_662251
  simp only [CollatzResearch.WordTrace]
  refine ⟨24154278323785205311282607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16102852215856803540855071 24154278323785205311282607)
  ·
    refine ⟨36231417485677807966923911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24154278323785205311282607 36231417485677807966923911)
    ·
      refine ⟨54347126228516711950385867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36231417485677807966923911 54347126228516711950385867)
      ·
        refine ⟨81520689342775067925578801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54347126228516711950385867 81520689342775067925578801)
        ·
          refine ⟨61140517007081300944184101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81520689342775067925578801 61140517007081300944184101)
          ·
            refine ⟨11463846938827743927034519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61140517007081300944184101 11463846938827743927034519)
            ·
              refine ⟨17195770408241615890551779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11463846938827743927034519 17195770408241615890551779)
              ·
                refine ⟨25793655612362423835827669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17195770408241615890551779 25793655612362423835827669)
                ·
                  refine ⟨604538803414744308652211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 25793655612362423835827669 604538803414744308652211)
                  ·
                    refine ⟨906808205122116462978317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 604538803414744308652211 906808205122116462978317)
                    ·
                      refine ⟨340053076920793673616869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 906808205122116462978317 340053076920793673616869)
                      ·
                        rfl

theorem cell23_662251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 7, 1, 3].length) (baseStart_662251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662251 prefixEnd_662251 := by exact prefixLift 662251
  have htrace : WordTrace (prefixWord ++ tailWord_662251) baseStart_662251 baseEnd_662251 := by
    simpa [prefixWord, tailWord_662251, baseEnd_662251] using wordTrace_append hprefix tailTrace_662251
  have hstable : (prefixWord ++ tailWord_662251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662251).length < 2 ^ (prefixWord ++ tailWord_662251).sum := by decide
  have hdescent : baseEnd_662251 < baseStart_662251 := by decide
  rcases family_descends (prefixWord ++ tailWord_662251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662258 : List Nat := [3, 2, 1, 3, 1, 4, 1, 2, 6]
def baseStart_662258 : Nat := 118140960795 + 662258 * 2 ^ 59
def prefixEnd_662258 : Nat := 4983230072969 + 3 ^ 40 * 662258 * 2
def baseEnd_662258 : Nat := 37784074587263905136593

theorem tailTrace_662258 : CollatzResearch.WordTrace tailWord_662258 prefixEnd_662258 37784074587263905136593 := by
  unfold tailWord_662258
  simp only [CollatzResearch.WordTrace]
  refine ⟨6038633408689961376696857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16103022423173230337858285 6038633408689961376696857)
  ·
    refine ⟨4528975056517471032522643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6038633408689961376696857 4528975056517471032522643)
    ·
      refine ⟨6793462584776206548783965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4528975056517471032522643 6793462584776206548783965)
      ·
        refine ⟨2547548469291077455793987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6793462584776206548783965 2547548469291077455793987)
        ·
          refine ⟨3821322703936616183690981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2547548469291077455793987 3821322703936616183690981)
          ·
            refine ⟨716498006988115534442059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3821322703936616183690981 716498006988115534442059)
            ·
              refine ⟨1074747010482173301663089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716498006988115534442059 1074747010482173301663089)
              ·
                refine ⟨806060257861629976247317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1074747010482173301663089 806060257861629976247317)
                ·
                  refine ⟨37784074587263905136593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 806060257861629976247317 37784074587263905136593)
                  ·
                    rfl

theorem cell23_662258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_662258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662258 prefixEnd_662258 := by exact prefixLift 662258
  have htrace : WordTrace (prefixWord ++ tailWord_662258) baseStart_662258 baseEnd_662258 := by
    simpa [prefixWord, tailWord_662258, baseEnd_662258] using wordTrace_append hprefix tailTrace_662258
  have hstable : (prefixWord ++ tailWord_662258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662258).length < 2 ^ (prefixWord ++ tailWord_662258).sum := by decide
  have hdescent : baseEnd_662258 < baseStart_662258 := by decide
  rcases family_descends (prefixWord ++ tailWord_662258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662268 : List Nat := [2, 2, 2, 1, 3, 2, 1, 3, 3, 1, 3]
def baseStart_662268 : Nat := 118140960795 + 662268 * 2 ^ 59
def prefixEnd_662268 : Nat := 4983230072969 + 3 ^ 40 * 662268 * 2
def baseEnd_662268 : Nat := 340061806091920107104291

theorem tailTrace_662268 : CollatzResearch.WordTrace tailWord_662268 prefixEnd_662268 340061806091920107104291 := by
  unfold tailWord_662268
  simp only [CollatzResearch.WordTrace]
  refine ⟨12077449182361808607325729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16103265576482411476434305 12077449182361808607325729)
  ·
    refine ⟨9058086886771356455494297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12077449182361808607325729 9058086886771356455494297)
    ·
      refine ⟨6793565165078517341620723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9058086886771356455494297 6793565165078517341620723)
      ·
        refine ⟨10190347747617776012431085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6793565165078517341620723 10190347747617776012431085)
        ·
          refine ⟨3821380405356666004661657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10190347747617776012431085 3821380405356666004661657)
          ·
            refine ⟨2866035304017499503496243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3821380405356666004661657 2866035304017499503496243)
            ·
              refine ⟨4299052956026249255244365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2866035304017499503496243 4299052956026249255244365)
              ·
                refine ⟨1612144858509843470716637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4299052956026249255244365 1612144858509843470716637)
                ·
                  refine ⟨604554321941191301518739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1612144858509843470716637 604554321941191301518739)
                  ·
                    refine ⟨906831482911786952278109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 604554321941191301518739 906831482911786952278109)
                    ·
                      refine ⟨340061806091920107104291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 906831482911786952278109 340061806091920107104291)
                      ·
                        rfl

theorem cell23_662268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_662268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662268 prefixEnd_662268 := by exact prefixLift 662268
  have htrace : WordTrace (prefixWord ++ tailWord_662268) baseStart_662268 baseEnd_662268 := by
    simpa [prefixWord, tailWord_662268, baseEnd_662268] using wordTrace_append hprefix tailTrace_662268
  have hstable : (prefixWord ++ tailWord_662268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662268).length < 2 ^ (prefixWord ++ tailWord_662268).sum := by decide
  have hdescent : baseEnd_662268 < baseStart_662268 := by decide
  rcases family_descends (prefixWord ++ tailWord_662268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662291 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 2, 6, 2]
def baseStart_662291 : Nat := 118140960795 + 662291 * 2 ^ 59
def prefixEnd_662291 : Nat := 4983230072969 + 3 ^ 40 * 662291 * 2
def baseEnd_662291 : Nat := 340073616146973517116685

theorem tailTrace_662291 : CollatzResearch.WordTrace tailWord_662291 prefixEnd_662291 340073616146973517116685 := by
  unfold tailWord_662291
  simp only [CollatzResearch.WordTrace]
  refine ⟨24155737243640292142738727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16103824829093528095159151 24155737243640292142738727)
  ·
    refine ⟨36233605865460438214108091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24155737243640292142738727 36233605865460438214108091)
    ·
      refine ⟨54350408798190657321162137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36233605865460438214108091 54350408798190657321162137)
      ·
        refine ⟨40762806598642992990871603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54350408798190657321162137 40762806598642992990871603)
        ·
          refine ⟨61144209897964489486307405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40762806598642992990871603 61144209897964489486307405)
          ·
            refine ⟨22929078711736683557365277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61144209897964489486307405 22929078711736683557365277)
            ·
              refine ⟨8598404516901256334011979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22929078711736683557365277 8598404516901256334011979)
              ·
                refine ⟨12897606775351884501017969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8598404516901256334011979 12897606775351884501017969)
                ·
                  refine ⟨9673205081513913375763477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12897606775351884501017969 9673205081513913375763477)
                  ·
                    refine ⟨453431488195964689488913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9673205081513913375763477 453431488195964689488913)
                    ·
                      refine ⟨340073616146973517116685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 453431488195964689488913 340073616146973517116685)
                      ·
                        rfl

theorem cell23_662291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 6, 2].length) (baseStart_662291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662291 prefixEnd_662291 := by exact prefixLift 662291
  have htrace : WordTrace (prefixWord ++ tailWord_662291) baseStart_662291 baseEnd_662291 := by
    simpa [prefixWord, tailWord_662291, baseEnd_662291] using wordTrace_append hprefix tailTrace_662291
  have hstable : (prefixWord ++ tailWord_662291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662291).length < 2 ^ (prefixWord ++ tailWord_662291).sum := by decide
  have hdescent : baseEnd_662291 < baseStart_662291 := by decide
  rcases family_descends (prefixWord ++ tailWord_662291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662335 : List Nat := [1, 1, 2, 2, 5, 1, 4, 1, 2, 4]
def baseStart_662335 : Nat := 118140960795 + 662335 * 2 ^ 59
def prefixEnd_662335 : Nat := 4983230072969 + 3 ^ 40 * 662335 * 2
def baseEnd_662335 : Nat := 113365403098590448322161

theorem tailTrace_662335 : CollatzResearch.WordTrace tailWord_662335 prefixEnd_662335 113365403098590448322161 := by
  unfold tailWord_662335
  simp only [CollatzResearch.WordTrace]
  refine ⟨24157342055480887657340459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16104894703653925104893639 24157342055480887657340459)
  ·
    refine ⟨36236013083221331486010689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24157342055480887657340459 36236013083221331486010689)
    ·
      refine ⟨27177009812415998614508017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36236013083221331486010689 27177009812415998614508017)
      ·
        refine ⟨20382757359311998960881013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27177009812415998614508017 20382757359311998960881013)
        ·
          refine ⟨1910883502435499902582595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20382757359311998960881013 1910883502435499902582595)
          ·
            refine ⟨2866325253653249853873893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1910883502435499902582595 2866325253653249853873893)
            ·
              refine ⟨537435985059984347601355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2866325253653249853873893 537435985059984347601355)
              ·
                refine ⟨806153977589976521402033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537435985059984347601355 806153977589976521402033)
                ·
                  refine ⟨604615483192482391051525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 806153977589976521402033 604615483192482391051525)
                  ·
                    refine ⟨113365403098590448322161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 604615483192482391051525 113365403098590448322161)
                    ·
                      rfl

theorem cell23_662335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 2, 4].length) (baseStart_662335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662335 prefixEnd_662335 := by exact prefixLift 662335
  have htrace : WordTrace (prefixWord ++ tailWord_662335) baseStart_662335 baseEnd_662335 := by
    simpa [prefixWord, tailWord_662335, baseEnd_662335] using wordTrace_append hprefix tailTrace_662335
  have hstable : (prefixWord ++ tailWord_662335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662335).length < 2 ^ (prefixWord ++ tailWord_662335).sum := by decide
  have hdescent : baseEnd_662335 < baseStart_662335 := by decide
  rcases family_descends (prefixWord ++ tailWord_662335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662342 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_662342 : Nat := 118140960795 + 662342 * 2 ^ 59
def prefixEnd_662342 : Nat := 4983230072969 + 3 ^ 40 * 662342 * 2
def baseEnd_662342 : Nat := 340099803660352817578951

theorem tailTrace_662342 : CollatzResearch.WordTrace tailWord_662342 prefixEnd_662342 340099803660352817578951 := by
  unfold tailWord_662342
  simp only [CollatzResearch.WordTrace]
  refine ⟨754924917701735245401415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16105064910970351901896853 754924917701735245401415)
  ·
    refine ⟨1132387376552602868102123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 754924917701735245401415 1132387376552602868102123)
    ·
      refine ⟨1698581064828904302153185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1132387376552602868102123 1698581064828904302153185)
      ·
        refine ⟨1273935798621678226614889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1698581064828904302153185 1273935798621678226614889)
        ·
          refine ⟨955451848966258669961167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1273935798621678226614889 955451848966258669961167)
          ·
            refine ⟨1433177773449388004941751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955451848966258669961167 1433177773449388004941751)
            ·
              refine ⟨2149766660174082007412627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1433177773449388004941751 2149766660174082007412627)
              ·
                refine ⟨3224649990261123011118941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2149766660174082007412627 3224649990261123011118941)
                ·
                  refine ⟨1209243746347921129169603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3224649990261123011118941 1209243746347921129169603)
                  ·
                    refine ⟨1813865619521881693754405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1209243746347921129169603 1813865619521881693754405)
                    ·
                      refine ⟨340099803660352817578951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1813865619521881693754405 340099803660352817578951)
                      ·
                        rfl

theorem cell23_662342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_662342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662342 prefixEnd_662342 := by exact prefixLift 662342
  have htrace : WordTrace (prefixWord ++ tailWord_662342) baseStart_662342 baseEnd_662342 := by
    simpa [prefixWord, tailWord_662342, baseEnd_662342] using wordTrace_append hprefix tailTrace_662342
  have hstable : (prefixWord ++ tailWord_662342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662342).length < 2 ^ (prefixWord ++ tailWord_662342).sum := by decide
  have hdescent : baseEnd_662342 < baseStart_662342 := by decide
  rcases family_descends (prefixWord ++ tailWord_662342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662345 : List Nat := [1, 2, 1, 1, 2, 7, 1, 2, 1, 2, 3]
def baseStart_662345 : Nat := 118140960795 + 662345 * 2 ^ 59
def prefixEnd_662345 : Nat := 4983230072969 + 3 ^ 40 * 662345 * 2
def baseEnd_662345 : Nat := 340101344102316305841437

theorem tailTrace_662345 : CollatzResearch.WordTrace tailWord_662345 prefixEnd_662345 340101344102316305841437 := by
  unfold tailWord_662345
  simp only [CollatzResearch.WordTrace]
  refine ⟨24157706785444659365204489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16105137856963106243469659 24157706785444659365204489)
  ·
    refine ⟨18118280089083494523903367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24157706785444659365204489 18118280089083494523903367)
    ·
      refine ⟨27177420133625241785855051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18118280089083494523903367 27177420133625241785855051)
      ·
        refine ⟨40766130200437862678782577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27177420133625241785855051 40766130200437862678782577)
        ·
          refine ⟨30574597650328397009086933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40766130200437862678782577 30574597650328397009086933)
          ·
            refine ⟨716592132429571804900475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 30574597650328397009086933 716592132429571804900475)
            ·
              refine ⟨1074888198644357707350713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716592132429571804900475 1074888198644357707350713)
              ·
                refine ⟨806166148983268280513035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1074888198644357707350713 806166148983268280513035)
                ·
                  refine ⟨1209249223474902420769553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 806166148983268280513035 1209249223474902420769553)
                  ·
                    refine ⟨906936917606176815577165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1209249223474902420769553 906936917606176815577165)
                    ·
                      refine ⟨340101344102316305841437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 906936917606176815577165 340101344102316305841437)
                      ·
                        rfl

theorem cell23_662345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 1, 2, 3].length) (baseStart_662345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662345 prefixEnd_662345 := by exact prefixLift 662345
  have htrace : WordTrace (prefixWord ++ tailWord_662345) baseStart_662345 baseEnd_662345 := by
    simpa [prefixWord, tailWord_662345, baseEnd_662345] using wordTrace_append hprefix tailTrace_662345
  have hstable : (prefixWord ++ tailWord_662345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662345).length < 2 ^ (prefixWord ++ tailWord_662345).sum := by decide
  have hdescent : baseEnd_662345 < baseStart_662345 := by decide
  rcases family_descends (prefixWord ++ tailWord_662345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662375 : List Nat := [1, 1, 5, 1, 2, 2, 1, 4, 2, 1, 3]
def baseStart_662375 : Nat := 118140960795 + 662375 * 2 ^ 59
def prefixEnd_662375 : Nat := 4983230072969 + 3 ^ 40 * 662375 * 2
def baseEnd_662375 : Nat := 340116748521951188466299

theorem tailTrace_662375 : CollatzResearch.WordTrace tailWord_662375 prefixEnd_662375 340116748521951188466299 := by
  unfold tailWord_662375
  simp only [CollatzResearch.WordTrace]
  refine ⟨24158800975335974488796579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16105867316890649659197719 24158800975335974488796579)
  ·
    refine ⟨36238201463003961733194869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24158800975335974488796579 36238201463003961733194869)
    ·
      refine ⟨3397331387156621412487019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36238201463003961733194869 3397331387156621412487019)
      ·
        refine ⟨5095997080734932118730529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3397331387156621412487019 5095997080734932118730529)
        ·
          refine ⟨3821997810551199089047897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5095997080734932118730529 3821997810551199089047897)
          ·
            refine ⟨2866498357913399316785923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3821997810551199089047897 2866498357913399316785923)
            ·
              refine ⟨4299747536870098975178885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2866498357913399316785923 4299747536870098975178885)
              ·
                refine ⟨806202663163143557846041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4299747536870098975178885 806202663163143557846041)
                ·
                  refine ⟨604651997372357668384531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 806202663163143557846041 604651997372357668384531)
                  ·
                    refine ⟨906977996058536502576797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 604651997372357668384531 906977996058536502576797)
                    ·
                      refine ⟨340116748521951188466299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 906977996058536502576797 340116748521951188466299)
                      ·
                        rfl

theorem cell23_662375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_662375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662375 prefixEnd_662375 := by exact prefixLift 662375
  have htrace : WordTrace (prefixWord ++ tailWord_662375) baseStart_662375 baseEnd_662375 := by
    simpa [prefixWord, tailWord_662375, baseEnd_662375] using wordTrace_append hprefix tailTrace_662375
  have hstable : (prefixWord ++ tailWord_662375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662375).length < 2 ^ (prefixWord ++ tailWord_662375).sum := by decide
  have hdescent : baseEnd_662375 < baseStart_662375 := by decide
  rcases family_descends (prefixWord ++ tailWord_662375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662376 : List Nat := [2, 1, 4, 2, 1, 4, 2, 2, 1, 2, 2]
def baseStart_662376 : Nat := 118140960795 + 662376 * 2 ^ 59
def prefixEnd_662376 : Nat := 4983230072969 + 3 ^ 40 * 662376 * 2
def baseEnd_662376 : Nat := 340117262002605684553795

theorem tailTrace_662376 : CollatzResearch.WordTrace tailWord_662376 prefixEnd_662376 340117262002605684553795 := by
  unfold tailWord_662376
  simp only [CollatzResearch.WordTrace]
  refine ⟨12079418724166175829791491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16105891632221567773055321 12079418724166175829791491)
  ·
    refine ⟨18119128086249263744687237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12079418724166175829791491 18119128086249263744687237)
    ·
      refine ⟨3397336516171736952128857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18119128086249263744687237 3397336516171736952128857)
      ·
        refine ⟨2548002387128802714096643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3397336516171736952128857 2548002387128802714096643)
        ·
          refine ⟨3822003580693204071144965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2548002387128802714096643 3822003580693204071144965)
          ·
            refine ⟨716625671379975763339681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3822003580693204071144965 716625671379975763339681)
            ·
              refine ⟨537469253534981822504761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 716625671379975763339681 537469253534981822504761)
              ·
                refine ⟨403101940151236366878571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537469253534981822504761 403101940151236366878571)
                ·
                  refine ⟨604652910226854550317857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403101940151236366878571 604652910226854550317857)
                  ·
                    refine ⟨453489682670140912738393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 604652910226854550317857 453489682670140912738393)
                    ·
                      refine ⟨340117262002605684553795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 453489682670140912738393 340117262002605684553795)
                      ·
                        rfl

theorem cell23_662376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_662376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662376 prefixEnd_662376 := by exact prefixLift 662376
  have htrace : WordTrace (prefixWord ++ tailWord_662376) baseStart_662376 baseEnd_662376 := by
    simpa [prefixWord, tailWord_662376, baseEnd_662376] using wordTrace_append hprefix tailTrace_662376
  have hstable : (prefixWord ++ tailWord_662376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662376).length < 2 ^ (prefixWord ++ tailWord_662376).sum := by decide
  have hdescent : baseEnd_662376 < baseStart_662376 := by decide
  rcases family_descends (prefixWord ++ tailWord_662376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662432 : List Nat := [2, 1, 1, 4, 1, 1, 5, 2, 2, 2, 2]
def baseStart_662432 : Nat := 118140960795 + 662432 * 2 ^ 59
def prefixEnd_662432 : Nat := 4983230072969 + 3 ^ 40 * 662432 * 2
def baseEnd_662432 : Nat := 340146016919257465453537

theorem tailTrace_662432 : CollatzResearch.WordTrace tailWord_662432 prefixEnd_662432 340146016919257465453537 := by
  unfold tailWord_662432
  simp only [CollatzResearch.WordTrace]
  refine ⟨12080439968064736611810775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16107253290752982149081033 12080439968064736611810775)
  ·
    refine ⟨18120659952097104917716163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12080439968064736611810775 18120659952097104917716163)
    ·
      refine ⟨27180989928145657376574245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18120659952097104917716163 27180989928145657376574245)
      ·
        refine ⟨5096435611527310758107671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27180989928145657376574245 5096435611527310758107671)
        ·
          refine ⟨7644653417290966137161507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5096435611527310758107671 7644653417290966137161507)
          ·
            refine ⟨11466980125936449205742261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7644653417290966137161507 11466980125936449205742261)
            ·
              refine ⟨1075029386806542113038337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11466980125936449205742261 1075029386806542113038337)
              ·
                refine ⟨806272040104906584778753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1075029386806542113038337 806272040104906584778753)
                ·
                  refine ⟨604704030078679938584065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 806272040104906584778753 604704030078679938584065)
                  ·
                    refine ⟨453528022559009953938049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 604704030078679938584065 453528022559009953938049)
                    ·
                      refine ⟨340146016919257465453537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 453528022559009953938049 340146016919257465453537)
                      ·
                        rfl

theorem cell23_662432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_662432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662432 prefixEnd_662432 := by exact prefixLift 662432
  have htrace : WordTrace (prefixWord ++ tailWord_662432) baseStart_662432 baseEnd_662432 := by
    simpa [prefixWord, tailWord_662432, baseEnd_662432] using wordTrace_append hprefix tailTrace_662432
  have hstable : (prefixWord ++ tailWord_662432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662432).length < 2 ^ (prefixWord ++ tailWord_662432).sum := by decide
  have hdescent : baseEnd_662432 < baseStart_662432 := by decide
  rcases family_descends (prefixWord ++ tailWord_662432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662449 : List Nat := [1, 2, 2, 4, 4, 1, 1, 1, 1, 4, 2]
def baseStart_662449 : Nat := 118140960795 + 662449 * 2 ^ 59
def prefixEnd_662449 : Nat := 4983230072969 + 3 ^ 40 * 662449 * 2
def baseEnd_662449 : Nat := 340154746090383898940959

theorem tailTrace_662449 : CollatzResearch.WordTrace tailWord_662449 prefixEnd_662449 340154746090383898940959 := by
  unfold tailWord_662449
  simp only [CollatzResearch.WordTrace]
  refine ⟨24161499977067885126990401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16107666651378590084660267 24161499977067885126990401)
  ·
    refine ⟨18121124982800913845242801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24161499977067885126990401 18121124982800913845242801)
    ·
      refine ⟨13590843737100685383932101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18121124982800913845242801 13590843737100685383932101)
      ·
        refine ⟨2548283200706378509487269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13590843737100685383932101 2548283200706378509487269)
        ·
          refine ⟨477803100132445970528863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2548283200706378509487269 477803100132445970528863)
          ·
            refine ⟨716704650198668955793295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477803100132445970528863 716704650198668955793295)
            ·
              refine ⟨1075056975298003433689943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716704650198668955793295 1075056975298003433689943)
              ·
                refine ⟨1612585462947005150534915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1075056975298003433689943 1612585462947005150534915)
                ·
                  refine ⟨2418878194420507725802373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1612585462947005150534915 2418878194420507725802373)
                  ·
                    refine ⟨453539661453845198587945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2418878194420507725802373 453539661453845198587945)
                    ·
                      refine ⟨340154746090383898940959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 453539661453845198587945 340154746090383898940959)
                      ·
                        rfl

theorem cell23_662449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_662449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662449 prefixEnd_662449 := by exact prefixLift 662449
  have htrace : WordTrace (prefixWord ++ tailWord_662449) baseStart_662449 baseEnd_662449 := by
    simpa [prefixWord, tailWord_662449, baseEnd_662449] using wordTrace_append hprefix tailTrace_662449
  have hstable : (prefixWord ++ tailWord_662449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662449).length < 2 ^ (prefixWord ++ tailWord_662449).sum := by decide
  have hdescent : baseEnd_662449 < baseStart_662449 := by decide
  rcases family_descends (prefixWord ++ tailWord_662449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662451 : List Nat := [1, 1, 1, 2, 3, 1, 2, 1, 6, 5]
def baseStart_662451 : Nat := 118140960795 + 662451 * 2 ^ 59
def prefixEnd_662451 : Nat := 4983230072969 + 3 ^ 40 * 662451 * 2
def baseEnd_662451 : Nat := 113385257683897630371983

theorem tailTrace_662451 : CollatzResearch.WordTrace tailWord_662451 prefixEnd_662451 113385257683897630371983 := by
  unfold tailWord_662451
  simp only [CollatzResearch.WordTrace]
  refine ⟨24161572923060639468563207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16107715282040426312375471 24161572923060639468563207)
  ·
    refine ⟨36242359384590959202844811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24161572923060639468563207 36242359384590959202844811)
    ·
      refine ⟨54363539076886438804267217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36242359384590959202844811 54363539076886438804267217)
      ·
        refine ⟨40772654307664829103200413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54363539076886438804267217 40772654307664829103200413)
        ·
          refine ⟨15289745365374310913700155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40772654307664829103200413 15289745365374310913700155)
          ·
            refine ⟨22934618048061466370550233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15289745365374310913700155 22934618048061466370550233)
            ·
              refine ⟨17200963536046099777912675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22934618048061466370550233 17200963536046099777912675)
              ·
                refine ⟨25801445304069149666869013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17200963536046099777912675 25801445304069149666869013)
                ·
                  refine ⟨1209442748628241390634485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25801445304069149666869013 1209442748628241390634485)
                  ·
                    refine ⟨113385257683897630371983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1209442748628241390634485 113385257683897630371983)
                    ·
                      rfl

theorem cell23_662451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 1, 6, 5].length) (baseStart_662451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662451 prefixEnd_662451 := by exact prefixLift 662451
  have htrace : WordTrace (prefixWord ++ tailWord_662451) baseStart_662451 baseEnd_662451 := by
    simpa [prefixWord, tailWord_662451, baseEnd_662451] using wordTrace_append hprefix tailTrace_662451
  have hstable : (prefixWord ++ tailWord_662451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662451).length < 2 ^ (prefixWord ++ tailWord_662451).sum := by decide
  have hdescent : baseEnd_662451 < baseStart_662451 := by decide
  rcases family_descends (prefixWord ++ tailWord_662451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662472 : List Nat := [2, 1, 3, 1, 5, 2, 1, 3, 5]
def baseStart_662472 : Nat := 118140960795 + 662472 * 2 ^ 59
def prefixEnd_662472 : Nat := 4983230072969 + 3 ^ 40 * 662472 * 2
def baseEnd_662472 : Nat := 37796284016159700994817

theorem tailTrace_662472 : CollatzResearch.WordTrace tailWord_662472 prefixEnd_662472 37796284016159700994817 := by
  unfold tailWord_662472
  simp only [CollatzResearch.WordTrace]
  refine ⟨12081169427992280027538835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16108225903989706703385113 12081169427992280027538835)
  ·
    refine ⟨18121754141988420041308253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12081169427992280027538835 18121754141988420041308253)
    ·
      refine ⟨6795657803245657515490595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18121754141988420041308253 6795657803245657515490595)
      ·
        refine ⟨10193486704868486273235893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6795657803245657515490595 10193486704868486273235893)
        ·
          refine ⟨955639378581420588115865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10193486704868486273235893 955639378581420588115865)
          ·
            refine ⟨716729533936065441086899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 955639378581420588115865 716729533936065441086899)
            ·
              refine ⟨1075094300904098161630349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 716729533936065441086899 1075094300904098161630349)
              ·
                refine ⟨403160362839036810611381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1075094300904098161630349 403160362839036810611381)
                ·
                  refine ⟨37796284016159700994817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 403160362839036810611381 37796284016159700994817)
                  ·
                    rfl

theorem cell23_662472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 3, 5].length) (baseStart_662472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662472 prefixEnd_662472 := by exact prefixLift 662472
  have htrace : WordTrace (prefixWord ++ tailWord_662472) baseStart_662472 baseEnd_662472 := by
    simpa [prefixWord, tailWord_662472, baseEnd_662472] using wordTrace_append hprefix tailTrace_662472
  have hstable : (prefixWord ++ tailWord_662472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662472).length < 2 ^ (prefixWord ++ tailWord_662472).sum := by decide
  have hdescent : baseEnd_662472 < baseStart_662472 := by decide
  rcases family_descends (prefixWord ++ tailWord_662472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662485 : List Nat := [1, 3, 2, 3, 3, 1, 1, 2, 2, 5]
def baseStart_662485 : Nat := 118140960795 + 662485 * 2 ^ 59
def prefixEnd_662485 : Nat := 4983230072969 + 3 ^ 40 * 662485 * 2
def baseEnd_662485 : Nat := 113391077131315252696931

theorem tailTrace_662485 : CollatzResearch.WordTrace tailWord_662485 prefixEnd_662485 113391077131315252696931 := by
  unfold tailWord_662485
  simp only [CollatzResearch.WordTrace]
  refine ⟨24162813004937463275300909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16108542003291642183533939 24162813004937463275300909)
  ·
    refine ⟨9061054876851548728237841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24162813004937463275300909 9061054876851548728237841)
    ·
      refine ⟨6795791157638661546178381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9061054876851548728237841 6795791157638661546178381)
      ·
        refine ⟨2548421684114498079816893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6795791157638661546178381 2548421684114498079816893)
        ·
          refine ⟨955658131542936779931335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2548421684114498079816893 955658131542936779931335)
          ·
            refine ⟨1433487197314405169897003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955658131542936779931335 1433487197314405169897003)
            ·
              refine ⟨2150230795971607754845505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1433487197314405169897003 2150230795971607754845505)
              ·
                refine ⟨1612673096978705816134129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2150230795971607754845505 1612673096978705816134129)
                ·
                  refine ⟨1209504822734029362100597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1612673096978705816134129 1209504822734029362100597)
                  ·
                    refine ⟨113391077131315252696931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1209504822734029362100597 113391077131315252696931)
                    ·
                      rfl

theorem cell23_662485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_662485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662485 prefixEnd_662485 := by exact prefixLift 662485
  have htrace : WordTrace (prefixWord ++ tailWord_662485) baseStart_662485 baseEnd_662485 := by
    simpa [prefixWord, tailWord_662485, baseEnd_662485] using wordTrace_append hprefix tailTrace_662485
  have hstable : (prefixWord ++ tailWord_662485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662485).length < 2 ^ (prefixWord ++ tailWord_662485).sum := by decide
  have hdescent : baseEnd_662485 < baseStart_662485 := by decide
  rcases family_descends (prefixWord ++ tailWord_662485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662488 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 4, 1, 4]
def baseStart_662488 : Nat := 118140960795 + 662488 * 2 ^ 59
def prefixEnd_662488 : Nat := 4983230072969 + 3 ^ 40 * 662488 * 2
def baseEnd_662488 : Nat := 340174771835909246353279

theorem tailTrace_662488 : CollatzResearch.WordTrace tailWord_662488 prefixEnd_662488 340174771835909246353279 := by
  unfold tailWord_662488
  simp only [CollatzResearch.WordTrace]
  refine ⟨12081461211963297393830059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16108614949284396525106745 12081461211963297393830059)
  ·
    refine ⟨18122191817944946090745089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12081461211963297393830059 18122191817944946090745089)
    ·
      refine ⟨13591643863458709568058817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18122191817944946090745089 13591643863458709568058817)
      ·
        refine ⟨10193732897594032176044113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13591643863458709568058817 10193732897594032176044113)
        ·
          refine ⟨7645299673195524132033085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10193732897594032176044113 7645299673195524132033085)
          ·
            refine ⟨2866987377448321549512407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7645299673195524132033085 2866987377448321549512407)
            ·
              refine ⟨4300481066172482324268611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2866987377448321549512407 4300481066172482324268611)
              ·
                refine ⟨6450721599258723486402917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4300481066172482324268611 6450721599258723486402917)
                ·
                  refine ⟨1209510299861010653700547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6450721599258723486402917 1209510299861010653700547)
                  ·
                    refine ⟨1814265449791515980550821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1209510299861010653700547 1814265449791515980550821)
                    ·
                      refine ⟨340174771835909246353279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1814265449791515980550821 340174771835909246353279)
                      ·
                        rfl

theorem cell23_662488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_662488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662488 prefixEnd_662488 := by exact prefixLift 662488
  have htrace : WordTrace (prefixWord ++ tailWord_662488) baseStart_662488 baseEnd_662488 := by
    simpa [prefixWord, tailWord_662488, baseEnd_662488] using wordTrace_append hprefix tailTrace_662488
  have hstable : (prefixWord ++ tailWord_662488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662488).length < 2 ^ (prefixWord ++ tailWord_662488).sum := by decide
  have hdescent : baseEnd_662488 < baseStart_662488 := by decide
  rcases family_descends (prefixWord ++ tailWord_662488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662531 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 8]
def baseStart_662531 : Nat := 118140960795 + 662531 * 2 ^ 59
def prefixEnd_662531 : Nat := 4983230072969 + 3 ^ 40 * 662531 * 2
def baseEnd_662531 : Nat := 340196851504052578115581

theorem tailTrace_662531 : CollatzResearch.WordTrace tailWord_662531 prefixEnd_662531 340196851504052578115581 := by
  unfold tailWord_662531
  simp only [CollatzResearch.WordTrace]
  refine ⟨24164490762770813131475447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16109660508513875420983631 24164490762770813131475447)
  ·
    refine ⟨36246736144156219697213171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24164490762770813131475447 36246736144156219697213171)
    ·
      refine ⟨54370104216234329545819757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36246736144156219697213171 54370104216234329545819757)
      ·
        refine ⟨20388789081087873579682409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54370104216234329545819757 20388789081087873579682409)
        ·
          refine ⟨15291591810815905184761807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20388789081087873579682409 15291591810815905184761807)
          ·
            refine ⟨22937387716223857777142711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15291591810815905184761807 22937387716223857777142711)
            ·
              refine ⟨34406081574335786665714067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22937387716223857777142711 34406081574335786665714067)
              ·
                refine ⟨51609122361503679998571101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34406081574335786665714067 51609122361503679998571101)
                ·
                  refine ⟨19353420885563879999464163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51609122361503679998571101 19353420885563879999464163)
                  ·
                    refine ⟨29030131328345819999196245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19353420885563879999464163 29030131328345819999196245)
                    ·
                      refine ⟨340196851504052578115581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 29030131328345819999196245 340196851504052578115581)
                      ·
                        rfl

theorem cell23_662531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_662531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662531 prefixEnd_662531 := by exact prefixLift 662531
  have htrace : WordTrace (prefixWord ++ tailWord_662531) baseStart_662531 baseEnd_662531 := by
    simpa [prefixWord, tailWord_662531, baseEnd_662531] using wordTrace_append hprefix tailTrace_662531
  have hstable : (prefixWord ++ tailWord_662531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662531).length < 2 ^ (prefixWord ++ tailWord_662531).sum := by decide
  have hdescent : baseEnd_662531 < baseStart_662531 := by decide
  rcases family_descends (prefixWord ++ tailWord_662531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662549 : List Nat := [1, 3, 2, 1, 4, 1, 4, 2, 1, 4]
def baseStart_662549 : Nat := 118140960795 + 662549 * 2 ^ 59
def prefixEnd_662549 : Nat := 4983230072969 + 3 ^ 40 * 662549 * 2
def baseEnd_662549 : Nat := 113402031385277835896833

theorem tailTrace_662549 : CollatzResearch.WordTrace tailWord_662549 prefixEnd_662549 113402031385277835896833 := by
  unfold tailWord_662549
  simp only [CollatzResearch.WordTrace]
  refine ⟨24165147276705602205630701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16110098184470401470420467 24165147276705602205630701)
  ·
    refine ⟨9061930228764600827111513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24165147276705602205630701 9061930228764600827111513)
    ·
      refine ⟨6796447671573450620333635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9061930228764600827111513 6796447671573450620333635)
      ·
        refine ⟨10194671507360175930500453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6796447671573450620333635 10194671507360175930500453)
        ·
          refine ⟨1911500907630032986968835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10194671507360175930500453 1911500907630032986968835)
          ·
            refine ⟨2867251361445049480453253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1911500907630032986968835 2867251361445049480453253)
            ·
              refine ⟨537609630270946777584985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2867251361445049480453253 537609630270946777584985)
              ·
                refine ⟨403207222703210083188739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 537609630270946777584985 403207222703210083188739)
                ·
                  refine ⟨604810834054815124783109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403207222703210083188739 604810834054815124783109)
                  ·
                    refine ⟨113402031385277835896833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 604810834054815124783109 113402031385277835896833)
                    ·
                      rfl

theorem cell23_662549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_662549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662549 prefixEnd_662549 := by exact prefixLift 662549
  have htrace : WordTrace (prefixWord ++ tailWord_662549) baseStart_662549 baseEnd_662549 := by
    simpa [prefixWord, tailWord_662549, baseEnd_662549] using wordTrace_append hprefix tailTrace_662549
  have hstable : (prefixWord ++ tailWord_662549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662549).length < 2 ^ (prefixWord ++ tailWord_662549).sum := by decide
  have hdescent : baseEnd_662549 < baseStart_662549 := by decide
  rcases family_descends (prefixWord ++ tailWord_662549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662565 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 1, 5, 2]
def baseStart_662565 : Nat := 118140960795 + 662565 * 2 ^ 59
def prefixEnd_662565 : Nat := 4983230072969 + 3 ^ 40 * 662565 * 2
def baseEnd_662565 : Nat := 340214309846305445090425

theorem tailTrace_662565 : CollatzResearch.WordTrace tailWord_662565 prefixEnd_662565 340214309846305445090425 := by
  unfold tailWord_662565
  simp only [CollatzResearch.WordTrace]
  refine ⟨24165730844647636938213149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16110487229765091292142099 24165730844647636938213149)
  ·
    refine ⟨9062149066742863851829931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24165730844647636938213149 9062149066742863851829931)
    ·
      refine ⟨13593223600114295777744897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9062149066742863851829931 13593223600114295777744897)
      ·
        refine ⟨10194917700085721833308673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13593223600114295777744897 10194917700085721833308673)
        ·
          refine ⟨7646188275064291374981505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10194917700085721833308673 7646188275064291374981505)
          ·
            refine ⟨5734641206298218531236129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7646188275064291374981505 5734641206298218531236129)
            ·
              refine ⟨4300980904723663898427097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5734641206298218531236129 4300980904723663898427097)
              ·
                refine ⟨3225735678542747923820323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4300980904723663898427097 3225735678542747923820323)
                ·
                  refine ⟨4838603517814121885730485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3225735678542747923820323 4838603517814121885730485)
                  ·
                    refine ⟨453619079795073926787233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4838603517814121885730485 453619079795073926787233)
                    ·
                      refine ⟨340214309846305445090425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 453619079795073926787233 340214309846305445090425)
                      ·
                        rfl

theorem cell23_662565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_662565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662565 prefixEnd_662565 := by exact prefixLift 662565
  have htrace : WordTrace (prefixWord ++ tailWord_662565) baseStart_662565 baseEnd_662565 := by
    simpa [prefixWord, tailWord_662565, baseEnd_662565] using wordTrace_append hprefix tailTrace_662565
  have hstable : (prefixWord ++ tailWord_662565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662565).length < 2 ^ (prefixWord ++ tailWord_662565).sum := by decide
  have hdescent : baseEnd_662565 < baseStart_662565 := by decide
  rcases family_descends (prefixWord ++ tailWord_662565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662589 : List Nat := [1, 4, 1, 3, 1, 2, 1, 5, 1, 1, 3]
def baseStart_662589 : Nat := 118140960795 + 662589 * 2 ^ 59
def prefixEnd_662589 : Nat := 4983230072969 + 3 ^ 40 * 662589 * 2
def baseEnd_662589 : Nat := 340226633382013351190315

theorem tailTrace_662589 : CollatzResearch.WordTrace tailWord_662589 prefixEnd_662589 340226633382013351190315 := by
  unfold tailWord_662589
  simp only [CollatzResearch.WordTrace]
  refine ⟨24166606196560689037086821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16111070797707126024724547 24166606196560689037086821)
  ·
    refine ⟨4531238661855129194453779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24166606196560689037086821 4531238661855129194453779)
    ·
      refine ⟨6796857992782693791680669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4531238661855129194453779 6796857992782693791680669)
      ·
        refine ⟨2548821747293510171880251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6796857992782693791680669 2548821747293510171880251)
        ·
          refine ⟨3823232620940265257820377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2548821747293510171880251 3823232620940265257820377)
          ·
            refine ⟨2867424465705198943365283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3823232620940265257820377 2867424465705198943365283)
            ·
              refine ⟨4301136698557798415047925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2867424465705198943365283 4301136698557798415047925)
              ·
                refine ⟨403231565489793601410743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4301136698557798415047925 403231565489793601410743)
                ·
                  refine ⟨604847348234690402116115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403231565489793601410743 604847348234690402116115)
                  ·
                    refine ⟨907271022352035603174173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 604847348234690402116115 907271022352035603174173)
                    ·
                      refine ⟨340226633382013351190315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 907271022352035603174173 340226633382013351190315)
                      ·
                        rfl

theorem cell23_662589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_662589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662589 prefixEnd_662589 := by exact prefixLift 662589
  have htrace : WordTrace (prefixWord ++ tailWord_662589) baseStart_662589 baseEnd_662589 := by
    simpa [prefixWord, tailWord_662589, baseEnd_662589] using wordTrace_append hprefix tailTrace_662589
  have hstable : (prefixWord ++ tailWord_662589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662589).length < 2 ^ (prefixWord ++ tailWord_662589).sum := by decide
  have hdescent : baseEnd_662589 < baseStart_662589 := by decide
  rcases family_descends (prefixWord ++ tailWord_662589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662595 : List Nat := [1, 1, 1, 3, 1, 2, 5, 3, 1, 1, 4]
def baseStart_662595 : Nat := 118140960795 + 662595 * 2 ^ 59
def prefixEnd_662595 : Nat := 4983230072969 + 3 ^ 40 * 662595 * 2
def baseEnd_662595 : Nat := 340229714265940327715287

theorem tailTrace_662595 : CollatzResearch.WordTrace tailWord_662595 prefixEnd_662595 340229714265940327715287 := by
  unfold tailWord_662595
  simp only [CollatzResearch.WordTrace]
  refine ⟨24166825034538952061805239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16111216689692634707870159 24166825034538952061805239)
  ·
    refine ⟨36250237551808428092707859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24166825034538952061805239 36250237551808428092707859)
    ·
      refine ⟨54375356327712642139061789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36250237551808428092707859 54375356327712642139061789)
      ·
        refine ⟨20390758622892240802148171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54375356327712642139061789 20390758622892240802148171)
        ·
          refine ⟨30586137934338361203222257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20390758622892240802148171 30586137934338361203222257)
          ·
            refine ⟨22939603450753770902416693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30586137934338361203222257 22939603450753770902416693)
            ·
              refine ⟨2150587823508166022101565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22939603450753770902416693 2150587823508166022101565)
              ·
                refine ⟨806470433815562258288087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2150587823508166022101565 806470433815562258288087)
                ·
                  refine ⟨1209705650723343387432131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 806470433815562258288087 1209705650723343387432131)
                  ·
                    refine ⟨1814558476085015081148197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1209705650723343387432131 1814558476085015081148197)
                    ·
                      refine ⟨340229714265940327715287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1814558476085015081148197 340229714265940327715287)
                      ·
                        rfl

theorem cell23_662595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 1, 4].length) (baseStart_662595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662595 prefixEnd_662595 := by exact prefixLift 662595
  have htrace : WordTrace (prefixWord ++ tailWord_662595) baseStart_662595 baseEnd_662595 := by
    simpa [prefixWord, tailWord_662595, baseEnd_662595] using wordTrace_append hprefix tailTrace_662595
  have hstable : (prefixWord ++ tailWord_662595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662595).length < 2 ^ (prefixWord ++ tailWord_662595).sum := by decide
  have hdescent : baseEnd_662595 < baseStart_662595 := by decide
  rcases family_descends (prefixWord ++ tailWord_662595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662608 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 4]
def baseStart_662608 : Nat := 118140960795 + 662608 * 2 ^ 59
def prefixEnd_662608 : Nat := 4983230072969 + 3 ^ 40 * 662608 * 2
def baseEnd_662608 : Nat := 340236389514448776852727

theorem tailTrace_662608 : CollatzResearch.WordTrace tailWord_662608 prefixEnd_662608 340236389514448776852727 := by
  unfold tailWord_662608
  simp only [CollatzResearch.WordTrace]
  refine ⟨12083649591745927641014239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16111532788994570188018985 12083649591745927641014239)
  ·
    refine ⟨18125474387618891461521359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12083649591745927641014239 18125474387618891461521359)
    ·
      refine ⟨27188211581428337192282039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18125474387618891461521359 27188211581428337192282039)
      ·
        refine ⟨40782317372142505788423059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27188211581428337192282039 40782317372142505788423059)
        ·
          refine ⟨61173476058213758682634589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40782317372142505788423059 61173476058213758682634589)
          ·
            refine ⟨22940053521830159505987971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61173476058213758682634589 22940053521830159505987971)
            ·
              refine ⟨34410080282745239258981957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22940053521830159505987971 34410080282745239258981957)
              ·
                refine ⟨6451890053014732361059117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34410080282745239258981957 6451890053014732361059117)
                ·
                  refine ⟨2419458769880524635397169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6451890053014732361059117 2419458769880524635397169)
                  ·
                    refine ⟨1814594077410393476547877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2419458769880524635397169 1814594077410393476547877)
                    ·
                      refine ⟨340236389514448776852727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1814594077410393476547877 340236389514448776852727)
                      ·
                        rfl

theorem cell23_662608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 3, 2, 4].length) (baseStart_662608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662608 prefixEnd_662608 := by exact prefixLift 662608
  have htrace : WordTrace (prefixWord ++ tailWord_662608) baseStart_662608 baseEnd_662608 := by
    simpa [prefixWord, tailWord_662608, baseEnd_662608] using wordTrace_append hprefix tailTrace_662608
  have hstable : (prefixWord ++ tailWord_662608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662608).length < 2 ^ (prefixWord ++ tailWord_662608).sum := by decide
  have hdescent : baseEnd_662608 < baseStart_662608 := by decide
  rcases family_descends (prefixWord ++ tailWord_662608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662625 : List Nat := [1, 2, 3, 1, 1, 2, 5, 1, 1, 2, 4]
def baseStart_662625 : Nat := 118140960795 + 662625 * 2 ^ 59
def prefixEnd_662625 : Nat := 4983230072969 + 3 ^ 40 * 662625 * 2
def baseEnd_662625 : Nat := 340245118685575210340149

theorem tailTrace_662625 : CollatzResearch.WordTrace tailWord_662625 prefixEnd_662625 340245118685575210340149 := by
  unfold tailWord_662625
  simp only [CollatzResearch.WordTrace]
  refine ⟨24167919224430267185397329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16111946149620178123598219 24167919224430267185397329)
  ·
    refine ⟨18125939418322700389047997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24167919224430267185397329 18125939418322700389047997)
    ·
      refine ⟨6797227281871012645892999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18125939418322700389047997 6797227281871012645892999)
      ·
        refine ⟨10195840922806518968839499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6797227281871012645892999 10195840922806518968839499)
        ·
          refine ⟨15293761384209778453259249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10195840922806518968839499 15293761384209778453259249)
          ·
            refine ⟨11470321038157333839944437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15293761384209778453259249 11470321038157333839944437)
            ·
              refine ⟨1075342597327250047494791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11470321038157333839944437 1075342597327250047494791)
              ·
                refine ⟨1613013895990875071242187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1075342597327250047494791 1613013895990875071242187)
                ·
                  refine ⟨2419520843986312606863281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1613013895990875071242187 2419520843986312606863281)
                  ·
                    refine ⟨1814640632989734455147461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2419520843986312606863281 1814640632989734455147461)
                    ·
                      refine ⟨340245118685575210340149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1814640632989734455147461 340245118685575210340149)
                      ·
                        rfl

theorem cell23_662625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_662625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662625 prefixEnd_662625 := by exact prefixLift 662625
  have htrace : WordTrace (prefixWord ++ tailWord_662625) baseStart_662625 baseEnd_662625 := by
    simpa [prefixWord, tailWord_662625, baseEnd_662625] using wordTrace_append hprefix tailTrace_662625
  have hstable : (prefixWord ++ tailWord_662625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662625).length < 2 ^ (prefixWord ++ tailWord_662625).sum := by decide
  have hdescent : baseEnd_662625 < baseStart_662625 := by decide
  rcases family_descends (prefixWord ++ tailWord_662625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662679 : List Nat := [1, 1, 3, 3, 3, 2, 1, 3, 2, 1, 3]
def baseStart_662679 : Nat := 118140960795 + 662679 * 2 ^ 59
def prefixEnd_662679 : Nat := 4983230072969 + 3 ^ 40 * 662679 * 2
def baseEnd_662679 : Nat := 340272846640917999064901

theorem tailTrace_662679 : CollatzResearch.WordTrace tailWord_662679 prefixEnd_662679 340272846640917999064901 := by
  unfold tailWord_662679
  simp only [CollatzResearch.WordTrace]
  refine ⟨24169888766234634407863091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16113259177489756271908727 24169888766234634407863091)
  ·
    refine ⟨36254833149351951611794637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24169888766234634407863091 36254833149351951611794637)
    ·
      refine ⟨13595562431006981854422989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36254833149351951611794637 13595562431006981854422989)
      ·
        refine ⟨5098335911627618195408621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13595562431006981854422989 5098335911627618195408621)
        ·
          refine ⟨1911875966860356823278233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5098335911627618195408621 1911875966860356823278233)
          ·
            refine ⟨1433906975145267617458675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1911875966860356823278233 1433906975145267617458675)
            ·
              refine ⟨2150860462717901426188013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1433906975145267617458675 2150860462717901426188013)
              ·
                refine ⟨806572673519213034820505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2150860462717901426188013 806572673519213034820505)
                ·
                  refine ⟨604929505139409776115379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 806572673519213034820505 604929505139409776115379)
                  ·
                    refine ⟨907394257709114664173069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 604929505139409776115379 907394257709114664173069)
                    ·
                      refine ⟨340272846640917999064901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 907394257709114664173069 340272846640917999064901)
                      ·
                        rfl

theorem cell23_662679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_662679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662679 prefixEnd_662679 := by exact prefixLift 662679
  have htrace : WordTrace (prefixWord ++ tailWord_662679) baseStart_662679 baseEnd_662679 := by
    simpa [prefixWord, tailWord_662679, baseEnd_662679] using wordTrace_append hprefix tailTrace_662679
  have hstable : (prefixWord ++ tailWord_662679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662679).length < 2 ^ (prefixWord ++ tailWord_662679).sum := by decide
  have hdescent : baseEnd_662679 < baseStart_662679 := by decide
  rcases family_descends (prefixWord ++ tailWord_662679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662706 : List Nat := [3, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2]
def baseStart_662706 : Nat := 118140960795 + 662706 * 2 ^ 59
def prefixEnd_662706 : Nat := 4983230072969 + 3 ^ 40 * 662706 * 2
def baseEnd_662706 : Nat := 340286710618589393427277

theorem tailTrace_662706 : CollatzResearch.WordTrace tailWord_662706 prefixEnd_662706 340286710618589393427277 := by
  unfold tailWord_662706
  simp only [CollatzResearch.WordTrace]
  refine ⟨6042718384284204504773993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16113915691424545346063981 6042718384284204504773993)
  ·
    refine ⟨4532038788213153378580495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6042718384284204504773993 4532038788213153378580495)
    ·
      refine ⟨6798058182319730067870743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4532038788213153378580495 6798058182319730067870743)
      ·
        refine ⟨10197087273479595101806115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6798058182319730067870743 10197087273479595101806115)
        ·
          refine ⟨15295630910219392652709173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10197087273479595101806115 15295630910219392652709173)
          ·
            refine ⟨1433965397833068061191485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15295630910219392652709173 1433965397833068061191485)
            ·
              refine ⟨537737024187400522946807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1433965397833068061191485 537737024187400522946807)
              ·
                refine ⟨806605536281100784420211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 537737024187400522946807 806605536281100784420211)
                ·
                  refine ⟨1209908304421651176630317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 806605536281100784420211 1209908304421651176630317)
                  ·
                    refine ⟨453715614158119191236369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1209908304421651176630317 453715614158119191236369)
                    ·
                      refine ⟨340286710618589393427277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 453715614158119191236369 340286710618589393427277)
                      ·
                        rfl

theorem cell23_662706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_662706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662706 prefixEnd_662706 := by exact prefixLift 662706
  have htrace : WordTrace (prefixWord ++ tailWord_662706) baseStart_662706 baseEnd_662706 := by
    simpa [prefixWord, tailWord_662706, baseEnd_662706] using wordTrace_append hprefix tailTrace_662706
  have hstable : (prefixWord ++ tailWord_662706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662706).length < 2 ^ (prefixWord ++ tailWord_662706).sum := by decide
  have hdescent : baseEnd_662706 < baseStart_662706 := by decide
  rcases family_descends (prefixWord ++ tailWord_662706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662719 : List Nat := [1, 1, 2, 2, 2, 2, 3, 4, 2, 2, 2]
def baseStart_662719 : Nat := 118140960795 + 662719 * 2 ^ 59
def prefixEnd_662719 : Nat := 4983230072969 + 3 ^ 40 * 662719 * 2
def baseEnd_662719 : Nat := 340293385867097842564717

theorem tailTrace_662719 : CollatzResearch.WordTrace tailWord_662719 prefixEnd_662719 340293385867097842564717 := by
  unfold tailWord_662719
  simp only [CollatzResearch.WordTrace]
  refine ⟨24171347686089721239319211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16114231790726480826212807 24171347686089721239319211)
  ·
    refine ⟨36257021529134581858978817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24171347686089721239319211 36257021529134581858978817)
    ·
      refine ⟨27192766146850936394234113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36257021529134581858978817 27192766146850936394234113)
      ·
        refine ⟨20394574610138202295675585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27192766146850936394234113 20394574610138202295675585)
        ·
          refine ⟨15295930957603651721756689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20394574610138202295675585 15295930957603651721756689)
          ·
            refine ⟨11471948218202738791317517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15295930957603651721756689 11471948218202738791317517)
            ·
              refine ⟨4301980581826027046744069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11471948218202738791317517 4301980581826027046744069)
              ·
                refine ⟨806621359092380071264513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4301980581826027046744069 806621359092380071264513)
                ·
                  refine ⟨604966019319285053448385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 806621359092380071264513 604966019319285053448385)
                  ·
                    refine ⟨453724514489463790086289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 604966019319285053448385 453724514489463790086289)
                    ·
                      refine ⟨340293385867097842564717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 453724514489463790086289 340293385867097842564717)
                      ·
                        rfl

theorem cell23_662719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 2, 2, 2].length) (baseStart_662719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662719 prefixEnd_662719 := by exact prefixLift 662719
  have htrace : WordTrace (prefixWord ++ tailWord_662719) baseStart_662719 baseEnd_662719 := by
    simpa [prefixWord, tailWord_662719, baseEnd_662719] using wordTrace_append hprefix tailTrace_662719
  have hstable : (prefixWord ++ tailWord_662719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662719).length < 2 ^ (prefixWord ++ tailWord_662719).sum := by decide
  have hdescent : baseEnd_662719 < baseStart_662719 := by decide
  rcases family_descends (prefixWord ++ tailWord_662719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662770 : List Nat := [3, 2, 1, 3, 4, 1, 1, 2, 2, 2, 2]
def baseStart_662770 : Nat := 118140960795 + 662770 * 2 ^ 59
def prefixEnd_662770 : Nat := 4983230072969 + 3 ^ 40 * 662770 * 2
def baseEnd_662770 : Nat := 340319573380477143026983

theorem tailTrace_662770 : CollatzResearch.WordTrace tailWord_662770 prefixEnd_662770 340319573380477143026983 := by
  unfold tailWord_662770
  simp only [CollatzResearch.WordTrace]
  refine ⟨6043301952226239237356441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16115471872603304632950509 6043301952226239237356441)
  ·
    refine ⟨4532476464169679428017331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6043301952226239237356441 4532476464169679428017331)
    ·
      refine ⟨6798714696254519142025997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4532476464169679428017331 6798714696254519142025997)
      ·
        refine ⟨2549518011095444678259749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6798714696254519142025997 2549518011095444678259749)
        ·
          refine ⟨478034627080395877173703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2549518011095444678259749 478034627080395877173703)
          ·
            refine ⟨717051940620593815760555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478034627080395877173703 717051940620593815760555)
            ·
              refine ⟨1075577910930890723640833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717051940620593815760555 1075577910930890723640833)
              ·
                refine ⟨806683433198168042730625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1075577910930890723640833 806683433198168042730625)
                ·
                  refine ⟨605012574898626032047969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 806683433198168042730625 605012574898626032047969)
                  ·
                    refine ⟨453759431173969524035977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 605012574898626032047969 453759431173969524035977)
                    ·
                      refine ⟨340319573380477143026983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 453759431173969524035977 340319573380477143026983)
                      ·
                        rfl

theorem cell23_662770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_662770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662770 prefixEnd_662770 := by exact prefixLift 662770
  have htrace : WordTrace (prefixWord ++ tailWord_662770) baseStart_662770 baseEnd_662770 := by
    simpa [prefixWord, tailWord_662770, baseEnd_662770] using wordTrace_append hprefix tailTrace_662770
  have hstable : (prefixWord ++ tailWord_662770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662770).length < 2 ^ (prefixWord ++ tailWord_662770).sum := by decide
  have hdescent : baseEnd_662770 < baseStart_662770 := by decide
  rcases family_descends (prefixWord ++ tailWord_662770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662805 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_662805 : Nat := 118140960795 + 662805 * 2 ^ 59
def prefixEnd_662805 : Nat := 4983230072969 + 3 ^ 40 * 662805 * 2
def baseEnd_662805 : Nat := 340337545203384506089321

theorem tailTrace_662805 : CollatzResearch.WordTrace tailWord_662805 prefixEnd_662805 340337545203384506089321 := by
  unfold tailWord_662805
  simp only [CollatzResearch.WordTrace]
  refine ⟨24174484363778157926949869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16116322909185438617966579 24174484363778157926949869)
  ·
    refine ⟨9065431636416809222606201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24174484363778157926949869 9065431636416809222606201)
    ·
      refine ⟨6799073727312606916954651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9065431636416809222606201 6799073727312606916954651)
      ·
        refine ⟨10198610590968910375431977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6799073727312606916954651 10198610590968910375431977)
        ·
          refine ⟨7648957943226682781573983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10198610590968910375431977 7648957943226682781573983)
          ·
            refine ⟨11473436914840024172360975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7648957943226682781573983 11473436914840024172360975)
            ·
              refine ⟨17210155372260036258541463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11473436914840024172360975 17210155372260036258541463)
              ·
                refine ⟨25815233058390054387812195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17210155372260036258541463 25815233058390054387812195)
                ·
                  refine ⟨38722849587585081581718293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25815233058390054387812195 38722849587585081581718293)
                  ·
                    refine ⟨1815133574418050699143045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 38722849587585081581718293 1815133574418050699143045)
                    ·
                      refine ⟨340337545203384506089321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1815133574418050699143045 340337545203384506089321)
                      ·
                        rfl

theorem cell23_662805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_662805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662805 prefixEnd_662805 := by exact prefixLift 662805
  have htrace : WordTrace (prefixWord ++ tailWord_662805) baseStart_662805 baseEnd_662805 := by
    simpa [prefixWord, tailWord_662805, baseEnd_662805] using wordTrace_append hprefix tailTrace_662805
  have hstable : (prefixWord ++ tailWord_662805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662805).length < 2 ^ (prefixWord ++ tailWord_662805).sum := by decide
  have hdescent : baseEnd_662805 < baseStart_662805 := by decide
  rcases family_descends (prefixWord ++ tailWord_662805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662812 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 1, 4, 3]
def baseStart_662812 : Nat := 118140960795 + 662812 * 2 ^ 59
def prefixEnd_662812 : Nat := 4983230072969 + 3 ^ 40 * 662812 * 2
def baseEnd_662812 : Nat := 340341139567965978701789

theorem tailTrace_662812 : CollatzResearch.WordTrace tailWord_662812 prefixEnd_662812 340341139567965978701789 := by
  unfold tailWord_662812
  simp only [CollatzResearch.WordTrace]
  refine ⟨12087369837376399061227345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16116493116501865414969793 12087369837376399061227345)
  ·
    refine ⟨9065527378032299295920509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12087369837376399061227345 9065527378032299295920509)
    ·
      refine ⟨3399572766762112235970191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9065527378032299295920509 3399572766762112235970191)
      ·
        refine ⟨5099359150143168353955287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3399572766762112235970191 5099359150143168353955287)
        ·
          refine ⟨7649038725214752530932931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5099359150143168353955287 7649038725214752530932931)
          ·
            refine ⟨11473558087822128796399397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7649038725214752530932931 11473558087822128796399397)
            ·
              refine ⟨2151292141466649149324887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11473558087822128796399397 2151292141466649149324887)
              ·
                refine ⟨3226938212199973723987331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2151292141466649149324887 3226938212199973723987331)
                ·
                  refine ⟨4840407318299960585980997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3226938212199973723987331 4840407318299960585980997)
                  ·
                    refine ⟨907576372181242609871437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4840407318299960585980997 907576372181242609871437)
                    ·
                      refine ⟨340341139567965978701789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 907576372181242609871437 340341139567965978701789)
                      ·
                        rfl

theorem cell23_662812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_662812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662812 prefixEnd_662812 := by exact prefixLift 662812
  have htrace : WordTrace (prefixWord ++ tailWord_662812) baseStart_662812 baseEnd_662812 := by
    simpa [prefixWord, tailWord_662812, baseEnd_662812] using wordTrace_append hprefix tailTrace_662812
  have hstable : (prefixWord ++ tailWord_662812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662812).length < 2 ^ (prefixWord ++ tailWord_662812).sum := by decide
  have hdescent : baseEnd_662812 < baseStart_662812 := by decide
  rcases family_descends (prefixWord ++ tailWord_662812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662849 : List Nat := [1, 2, 5, 2, 1, 2, 1, 3, 6]
def baseStart_662849 : Nat := 118140960795 + 662849 * 2 ^ 59
def prefixEnd_662849 : Nat := 4983230072969 + 3 ^ 40 * 662849 * 2
def baseEnd_662849 : Nat := 37817793150242481548791

theorem tailTrace_662849 : CollatzResearch.WordTrace tailWord_662849 prefixEnd_662849 37817793150242481548791 := by
  unfold tailWord_662849
  simp only [CollatzResearch.WordTrace]
  refine ⟨24176089175618753441551601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16117392783745835627701067 24176089175618753441551601)
  ·
    refine ⟨18132066881714065081163701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24176089175618753441551601 18132066881714065081163701)
    ·
      refine ⟨1699881270160693601359097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18132066881714065081163701 1699881270160693601359097)
      ·
        refine ⟨1274910952620520201019323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1699881270160693601359097 1274910952620520201019323)
        ·
          refine ⟨1912366428930780301528985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1274910952620520201019323 1912366428930780301528985)
          ·
            refine ⟨1434274821698085226146739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1912366428930780301528985 1434274821698085226146739)
            ·
              refine ⟨2151412232547127839220109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1434274821698085226146739 2151412232547127839220109)
              ·
                refine ⟨806779587205172939707541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2151412232547127839220109 806779587205172939707541)
                ·
                  refine ⟨37817793150242481548791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 806779587205172939707541 37817793150242481548791)
                  ·
                    rfl

theorem cell23_662849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 3, 6].length) (baseStart_662849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662849 prefixEnd_662849 := by exact prefixLift 662849
  have htrace : WordTrace (prefixWord ++ tailWord_662849) baseStart_662849 baseEnd_662849 := by
    simpa [prefixWord, tailWord_662849, baseEnd_662849] using wordTrace_append hprefix tailTrace_662849
  have hstable : (prefixWord ++ tailWord_662849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662849).length < 2 ^ (prefixWord ++ tailWord_662849).sum := by decide
  have hdescent : baseEnd_662849 < baseStart_662849 := by decide
  rcases family_descends (prefixWord ++ tailWord_662849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662862 : List Nat := [4, 1, 1, 1, 1, 1, 5, 1, 3, 5]
def baseStart_662862 : Nat := 118140960795 + 662862 * 2 ^ 59
def prefixEnd_662862 : Nat := 4983230072969 + 3 ^ 40 * 662862 * 2
def baseEnd_662862 : Nat := 113455604533563594358853

theorem tailTrace_662862 : CollatzResearch.WordTrace tailWord_662862 prefixEnd_662862 113455604533563594358853 := by
  unfold tailWord_662862
  simp only [CollatzResearch.WordTrace]
  refine ⟨3022070415571457082721855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16117708883047771107849893 3022070415571457082721855)
  ·
    refine ⟨4533105623357185624082783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3022070415571457082721855 4533105623357185624082783)
    ·
      refine ⟨6799658435035778436124175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4533105623357185624082783 6799658435035778436124175)
      ·
        refine ⟨10199487652553667654186263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6799658435035778436124175 10199487652553667654186263)
        ·
          refine ⟨15299231478830501481279395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10199487652553667654186263 15299231478830501481279395)
          ·
            refine ⟨22948847218245752221919093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15299231478830501481279395 22948847218245752221919093)
            ·
              refine ⟨2151454426710539270804915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22948847218245752221919093 2151454426710539270804915)
              ·
                refine ⟨3227181640065808906207373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2151454426710539270804915 3227181640065808906207373)
                ·
                  refine ⟨1210193115024678339827765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3227181640065808906207373 1210193115024678339827765)
                  ·
                    refine ⟨113455604533563594358853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1210193115024678339827765 113455604533563594358853)
                    ·
                      rfl

theorem cell23_662862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_662862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662862 prefixEnd_662862 := by exact prefixLift 662862
  have htrace : WordTrace (prefixWord ++ tailWord_662862) baseStart_662862 baseEnd_662862 := by
    simpa [prefixWord, tailWord_662862, baseEnd_662862] using wordTrace_append hprefix tailTrace_662862
  have hstable : (prefixWord ++ tailWord_662862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662862).length < 2 ^ (prefixWord ++ tailWord_662862).sum := by decide
  have hdescent : baseEnd_662862 < baseStart_662862 := by decide
  rcases family_descends (prefixWord ++ tailWord_662862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662893 : List Nat := [1, 5, 1, 1, 1, 4, 1, 4, 1, 1, 3]
def baseStart_662893 : Nat := 118140960795 + 662893 * 2 ^ 59
def prefixEnd_662893 : Nat := 4983230072969 + 3 ^ 40 * 662893 * 2
def baseEnd_662893 : Nat := 340382731500980161788917

theorem tailTrace_662893 : CollatzResearch.WordTrace tailWord_662893 prefixEnd_662893 340382731500980161788917 := by
  unfold tailWord_662893
  simp only [CollatzResearch.WordTrace]
  refine ⟨24177693987459348956153333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16118462658306232637435555 24177693987459348956153333)
  ·
    refine ⟨2266658811324313964639375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24177693987459348956153333 2266658811324313964639375)
    ·
      refine ⟨3399988216986470946959063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2266658811324313964639375 3399988216986470946959063)
      ·
        refine ⟨5099982325479706420438595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3399988216986470946959063 5099982325479706420438595)
        ·
          refine ⟨7649973488219559630657893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5099982325479706420438595 7649973488219559630657893)
          ·
            refine ⟨1434370029041167430748355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7649973488219559630657893 1434370029041167430748355)
            ·
              refine ⟨2151555043561751146122533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1434370029041167430748355 2151555043561751146122533)
              ·
                refine ⟨403416570667828339897975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2151555043561751146122533 403416570667828339897975)
                ·
                  refine ⟨605124856001742509846963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 403416570667828339897975 605124856001742509846963)
                  ·
                    refine ⟨907687284002613764770445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 605124856001742509846963 907687284002613764770445)
                    ·
                      refine ⟨340382731500980161788917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 907687284002613764770445 340382731500980161788917)
                      ·
                        rfl

theorem cell23_662893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_662893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662893 prefixEnd_662893 := by exact prefixLift 662893
  have htrace : WordTrace (prefixWord ++ tailWord_662893) baseStart_662893 baseEnd_662893 := by
    simpa [prefixWord, tailWord_662893, baseEnd_662893] using wordTrace_append hprefix tailTrace_662893
  have hstable : (prefixWord ++ tailWord_662893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662893).length < 2 ^ (prefixWord ++ tailWord_662893).sum := by decide
  have hdescent : baseEnd_662893 < baseStart_662893 := by decide
  rcases family_descends (prefixWord ++ tailWord_662893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662909 : List Nat := [1, 4, 1, 1, 2, 2, 1, 5, 2, 4]
def baseStart_662909 : Nat := 118140960795 + 662909 * 2 ^ 59
def prefixEnd_662909 : Nat := 4983230072969 + 3 ^ 40 * 662909 * 2
def baseEnd_662909 : Nat := 113463649063817366396281

theorem tailTrace_662909 : CollatzResearch.WordTrace tailWord_662909 prefixEnd_662909 113463649063817366396281 := by
  unfold tailWord_662909
  simp only [CollatzResearch.WordTrace]
  refine ⟨24178277555401383688735781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16118851703600922459157187 24178277555401383688735781)
  ·
    refine ⟨4533427041637759441637959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24178277555401383688735781 4533427041637759441637959)
    ·
      refine ⟨6800140562456639162456939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4533427041637759441637959 6800140562456639162456939)
      ·
        refine ⟨10200210843684958743685409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6800140562456639162456939 10200210843684958743685409)
        ·
          refine ⟨7650158132763719057764057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10200210843684958743685409 7650158132763719057764057)
          ·
            refine ⟨5737618599572789293323043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7650158132763719057764057 5737618599572789293323043)
            ·
              refine ⟨8606427899359183939984565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5737618599572789293323043 8606427899359183939984565)
              ·
                refine ⟨806852615564923494373553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8606427899359183939984565 806852615564923494373553)
                ·
                  refine ⟨605139461673692620780165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 806852615564923494373553 605139461673692620780165)
                  ·
                    refine ⟨113463649063817366396281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 605139461673692620780165 113463649063817366396281)
                    ·
                      rfl

theorem cell23_662909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_662909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662909 prefixEnd_662909 := by exact prefixLift 662909
  have htrace : WordTrace (prefixWord ++ tailWord_662909) baseStart_662909 baseEnd_662909 := by
    simpa [prefixWord, tailWord_662909, baseEnd_662909] using wordTrace_append hprefix tailTrace_662909
  have hstable : (prefixWord ++ tailWord_662909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662909).length < 2 ^ (prefixWord ++ tailWord_662909).sum := by decide
  have hdescent : baseEnd_662909 < baseStart_662909 := by decide
  rcases family_descends (prefixWord ++ tailWord_662909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662910 : List Nat := [4, 2, 3, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_662910 : Nat := 118140960795 + 662910 * 2 ^ 59
def prefixEnd_662910 : Nat := 4983230072969 + 3 ^ 40 * 662910 * 2
def baseEnd_662910 : Nat := 340391460672106595276339

theorem tailTrace_662910 : CollatzResearch.WordTrace tailWord_662910 prefixEnd_662910 340391460672106595276339 := by
  unfold tailWord_662910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3022289253549720107440273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16118876018931840573014789 3022289253549720107440273)
  ·
    refine ⟨2266716940162290080580205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3022289253549720107440273 2266716940162290080580205)
    ·
      refine ⟨850018852560858780217577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2266716940162290080580205 850018852560858780217577)
      ·
        refine ⟨637514139420644085163183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 850018852560858780217577 637514139420644085163183)
        ·
          refine ⟨956271209130966127744775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 637514139420644085163183 956271209130966127744775)
          ·
            refine ⟨1434406813696449191617163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 956271209130966127744775 1434406813696449191617163)
            ·
              refine ⟨2151610220544673787425745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1434406813696449191617163 2151610220544673787425745)
              ·
                refine ⟨1613707665408505340569309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2151610220544673787425745 1613707665408505340569309)
                ·
                  refine ⟨605140374528189502713491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1613707665408505340569309 605140374528189502713491)
                  ·
                    refine ⟨907710561792284254070237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 605140374528189502713491 907710561792284254070237)
                    ·
                      refine ⟨340391460672106595276339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 907710561792284254070237 340391460672106595276339)
                      ·
                        rfl

theorem cell23_662910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_662910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662910 prefixEnd_662910 := by exact prefixLift 662910
  have htrace : WordTrace (prefixWord ++ tailWord_662910) baseStart_662910 baseEnd_662910 := by
    simpa [prefixWord, tailWord_662910, baseEnd_662910] using wordTrace_append hprefix tailTrace_662910
  have hstable : (prefixWord ++ tailWord_662910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662910).length < 2 ^ (prefixWord ++ tailWord_662910).sum := by decide
  have hdescent : baseEnd_662910 < baseStart_662910 := by decide
  rcases family_descends (prefixWord ++ tailWord_662910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_662916 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 5, 2, 2]
def baseStart_662916 : Nat := 118140960795 + 662916 * 2 ^ 59
def prefixEnd_662916 : Nat := 4983230072969 + 3 ^ 40 * 662916 * 2
def baseEnd_662916 : Nat := 340394541556033571801311

theorem tailTrace_662916 : CollatzResearch.WordTrace tailWord_662916 prefixEnd_662916 340394541556033571801311 := by
  unfold tailWord_662916
  simp only [CollatzResearch.WordTrace]
  refine ⟨12089266433188011942120301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16119021910917349256160401 12089266433188011942120301)
  ·
    refine ⟨4533474912445504478295113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12089266433188011942120301 4533474912445504478295113)
    ·
      refine ⟨3400106184334128358721335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4533474912445504478295113 3400106184334128358721335)
      ·
        refine ⟨5100159276501192538082003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3400106184334128358721335 5100159276501192538082003)
        ·
          refine ⟨7650238914751788807123005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5100159276501192538082003 7650238914751788807123005)
          ·
            refine ⟨2868839593031920802671127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7650238914751788807123005 2868839593031920802671127)
            ·
              refine ⟨4303259389547881204006691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2868839593031920802671127 4303259389547881204006691)
              ·
                refine ⟨6454889084321821806010037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4303259389547881204006691 6454889084321821806010037)
                ·
                  refine ⟨605145851655170794313441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6454889084321821806010037 605145851655170794313441)
                  ·
                    refine ⟨453859388741378095735081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 605145851655170794313441 453859388741378095735081)
                    ·
                      refine ⟨340394541556033571801311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 453859388741378095735081 340394541556033571801311)
                      ·
                        rfl

theorem cell23_662916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_662916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_662916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_662916 prefixEnd_662916 := by exact prefixLift 662916
  have htrace : WordTrace (prefixWord ++ tailWord_662916) baseStart_662916 baseEnd_662916 := by
    simpa [prefixWord, tailWord_662916, baseEnd_662916] using wordTrace_append hprefix tailTrace_662916
  have hstable : (prefixWord ++ tailWord_662916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_662916).length < 2 ^ (prefixWord ++ tailWord_662916).sum := by decide
  have hdescent : baseEnd_662916 < baseStart_662916 := by decide
  rcases family_descends (prefixWord ++ tailWord_662916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
